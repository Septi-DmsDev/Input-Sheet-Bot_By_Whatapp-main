const { Boom } = require('@hapi/boom');
const pino = require('pino');
const qrcode = require('qrcode-terminal');
const fetch = (...args) => import('node-fetch').then(({ default: fetch }) => fetch(...args));
const fs = require('fs');
const http = require('http');
const { google } = require('googleapis');

const sheetsConfig = JSON.parse(fs.readFileSync('./sheets-config.json'));
const FIXED_TIMES = { "1": "10.00", "2": "14.00", "3": "16.00", "4": "19.00" };
const groupNameCache = new Map();
const messageCache = new Map();

const HEALTH_PORT = Number(process.env.HEALTH_PORT || process.env.PORT || 3000);
const BOOT_WATCHDOG_MS = Number(process.env.WA_BOOT_WATCHDOG_MS || 180000);
const RECONNECT_DELAY_MS = Number(process.env.WA_RECONNECT_DELAY_MS || 5000);
const LIVENESS_INTERVAL_MS = Number(process.env.WA_LIVENESS_INTERVAL_MS || 120000);
const LIVENESS_TIMEOUT_MS = Number(process.env.WA_LIVENESS_TIMEOUT_MS || 15000);
const LIVENESS_MAX_FAILURES = Number(process.env.WA_LIVENESS_MAX_FAILURES || 2);
const REACT_INITIAL_DELAY_MS = Number(process.env.WA_REACT_INITIAL_DELAY_MS || 1500);
const REACT_MAX_RETRIES = Number(process.env.WA_REACT_MAX_RETRIES || 3);
const REACT_RETRY_DELAY_MS = Number(process.env.WA_REACT_RETRY_DELAY_MS || 1200);
const WEBHOOK_TIMEOUT_MS = Number(process.env.WEBHOOK_TIMEOUT_MS || 20000);
const WEBHOOK_MAX_RETRIES = Number(process.env.WEBHOOK_MAX_RETRIES || 3);
const WEBHOOK_RETRY_DELAY_MS = Number(process.env.WEBHOOK_RETRY_DELAY_MS || 2000);
const WEBHOOK_FAILURE_LOG = process.env.WEBHOOK_FAILURE_LOG || './failed_webhooks.ndjson';
const SHEETS_REQUEST_MIN_INTERVAL_MS = Number(process.env.SHEETS_REQUEST_MIN_INTERVAL_MS || 1100);
const SHEETS_INDEX_CACHE_TTL_MS = Number(process.env.SHEETS_INDEX_CACHE_TTL_MS || 900000);
const SHEETS_LOOKUP_CACHE_TTL_MS = Number(process.env.SHEETS_LOOKUP_CACHE_TTL_MS || 21600000);
const SHEETS_NEGATIVE_LOOKUP_CACHE_TTL_MS = Number(process.env.SHEETS_NEGATIVE_LOOKUP_CACHE_TTL_MS || 300000);
const SHEETS_429_RETRY_DELAY_MS = Number(process.env.SHEETS_429_RETRY_DELAY_MS || 15000);
const SHEETS_CACHE_DEBUG = process.env.SHEETS_CACHE_DEBUG !== '0';
const HEALTH_MAX_STALENESS_MS = Number(
    process.env.WA_HEALTH_MAX_STALENESS_MS || (LIVENESS_INTERVAL_MS + LIVENESS_TIMEOUT_MS + 30000)
);
const REPORT_GROUP_NAME = (process.env.REPORT_GROUP_NAME || 'LAPORAN HARIAN BOT').trim();
const REKAP_LOG_FILE = process.env.REKAP_LOG_FILE || './rekap_harian.ndjson';
const REPORT_STATE_FILE = process.env.REPORT_STATE_FILE || './report_state.json';
const REPORT_SCHEDULER_INTERVAL_MS = Number(process.env.REPORT_SCHEDULER_INTERVAL_MS || 30000);
const REPORT_WINDOW_MINUTES = Number(process.env.REPORT_WINDOW_MINUTES || 5);
const REPORT_DIVISION_ORDER = ['DESAIN', 'PRINTING', 'FINISHING', 'CSM'];
const REPORT_COMMAND_HELP = [
    '!laporan',
    '!laporan hariini',
    '!laporan kemarin',
    '!laporan kirim',
    '!laporan kirim kemarin'
].join('\n');

let watchdogTimer = null;
let livenessTimer = null;
let reconnectTimer = null;
let reportSchedulerTimer = null;
let activeSock = null;
let activeGeneration = 0;
let activeConnectionState = 'close';
let isProbeRunning = false;
let consecutiveProbeFailures = 0;
let lastSuccessfulProbeAt = 0;
let lastConnectionOpenAt = 0;
let lastDisconnectReason = 'boot';
let isShuttingDown = false;
let sheetsClientPromise = null;
let sheetsRequestChain = Promise.resolve();
let lastSheetsRequestAt = 0;
let reportGroupJidCache = null;
let isReportDispatchRunning = false;
const sheetsRowCache = new Map();
const sheetsIndexCache = new Map();

function normalizeJid(jid) {
    return jid ? jid.replace(/:\d+@/, '@') : jid;
}

function forceExit(message, code = 1) {
    console.error(message);
    process.exit(code);
}

function sleep(ms) {
    return new Promise((resolve) => setTimeout(resolve, ms));
}

function logSheetsCache(event, details) {
    if (!SHEETS_CACHE_DEBUG) return;
    console.log(`[CACHE SHEETS] ${event} ${details}`);
}

async function runSheetsRequest(task) {
    const runner = async () => {
        const now = Date.now();
        const waitMs = Math.max(0, lastSheetsRequestAt + SHEETS_REQUEST_MIN_INTERVAL_MS - now);
        if (waitMs > 0) {
            await sleep(waitMs);
        }

        const result = await task();
        lastSheetsRequestAt = Date.now();
        return result;
    };

    const pending = sheetsRequestChain.then(runner, runner);
    sheetsRequestChain = pending.catch(() => {});
    return pending;
}

function getSheetsLookupCacheKey(spreadsheetId, sheetName, kode, lookupColumn) {
    return [spreadsheetId, sheetName, lookupColumn, normalizeCellValue(kode)].join('::');
}

function getSheetsIndexCacheKey(spreadsheetId, sheetName, lookupColumn) {
    return [spreadsheetId, sheetName, lookupColumn].join('::');
}

function getCachedRowLookup(cacheKey) {
    const cached = sheetsRowCache.get(cacheKey);
    if (!cached) {
        logSheetsCache('MISS', `key=${cacheKey}`);
        return undefined;
    }

    if (cached.expiresAt <= Date.now()) {
        sheetsRowCache.delete(cacheKey);
        logSheetsCache('EXPIRE', `key=${cacheKey}`);
        return undefined;
    }

    logSheetsCache('HIT', `key=${cacheKey} row=${cached.rowNumber === null ? 'null' : cached.rowNumber}`);
    return cached.rowNumber;
}

function setCachedRowLookup(cacheKey, rowNumber, ttlMs) {
    sheetsRowCache.set(cacheKey, {
        rowNumber,
        expiresAt: Date.now() + ttlMs
    });
    logSheetsCache(
        'SET',
        `key=${cacheKey} row=${rowNumber === null ? 'null' : rowNumber} ttlMs=${ttlMs} size=${sheetsRowCache.size}`
    );
}

function getCachedSheetIndex(cacheKey) {
    const cached = sheetsIndexCache.get(cacheKey);
    if (!cached) {
        logSheetsCache('INDEX_MISS', `key=${cacheKey}`);
        return null;
    }

    if (cached.expiresAt <= Date.now()) {
        sheetsIndexCache.delete(cacheKey);
        logSheetsCache('INDEX_EXPIRE', `key=${cacheKey}`);
        return null;
    }

    logSheetsCache('INDEX_HIT', `key=${cacheKey} size=${cached.rowsByKode.size}`);
    return cached.rowsByKode;
}

function setCachedSheetIndex(cacheKey, rowsByKode, ttlMs) {
    sheetsIndexCache.set(cacheKey, {
        rowsByKode,
        expiresAt: Date.now() + ttlMs
    });
    logSheetsCache('INDEX_SET', `key=${cacheKey} size=${rowsByKode.size} ttlMs=${ttlMs}`);
}

async function getSheetRowIndex({ sheets, spreadsheetId, sheetName, lookupColumn = 1 }) {
    const cacheKey = getSheetsIndexCacheKey(spreadsheetId, sheetName, lookupColumn);
    const cachedIndex = getCachedSheetIndex(cacheKey);
    if (cachedIndex) {
        return cachedIndex;
    }

    const lookupLetter = columnNumberToLetter(lookupColumn);
    const range = getSheetRange(sheetName, `${lookupLetter}:${lookupLetter}`);
    const res = await runSheetsRequest(() => sheets.spreadsheets.values.get({
        spreadsheetId,
        range
    }));

    const rows = res.data.values || [];
    const rowsByKode = new Map();

    for (let index = 0; index < rows.length; index += 1) {
        const normalizedKode = normalizeCellValue(rows[index]?.[0]);
        if (!normalizedKode || rowsByKode.has(normalizedKode)) continue;
        rowsByKode.set(normalizedKode, index + 1);
    }

    setCachedSheetIndex(cacheKey, rowsByKode, SHEETS_INDEX_CACHE_TTL_MS);
    return rowsByKode;
}

function truncate(value, max = 300) {
    const text = String(value || '').replace(/\s+/g, ' ').trim();
    return text.length > max ? `${text.slice(0, max)}...` : text;
}

function startWatchdog() {
    clearTimeout(watchdogTimer);
    watchdogTimer = setTimeout(() => {
        forceExit(`[WATCHDOG FATAL] Bot gagal open dalam ${BOOT_WATCHDOG_MS} ms. Force exit.`);
    }, BOOT_WATCHDOG_MS);
}

function stopWatchdog() {
    clearTimeout(watchdogTimer);
    watchdogTimer = null;
    console.log('[WATCHDOG SAFE] Boot watchdog dihentikan.');
}

function clearLivenessProbe() {
    clearInterval(livenessTimer);
    livenessTimer = null;
    isProbeRunning = false;
}

function stopReportScheduler() {
    clearInterval(reportSchedulerTimer);
    reportSchedulerTimer = null;
}

function destroySocket(sock) {
    if (!sock) return;

    try {
        sock.ev.removeAllListeners();
    } catch {}

    try {
        sock.ws?.close?.();
    } catch {}
}

function getHealthSnapshot() {
    const now = Date.now();
    const lastProbeReference = lastSuccessfulProbeAt || lastConnectionOpenAt || 0;
    const probeAgeMs = lastProbeReference ? now - lastProbeReference : null;
    const ok =
        !isShuttingDown &&
        activeConnectionState === 'open' &&
        probeAgeMs !== null &&
        probeAgeMs <= HEALTH_MAX_STALENESS_MS &&
        consecutiveProbeFailures < LIVENESS_MAX_FAILURES;

    return {
        ok,
        connection: activeConnectionState,
        lastProbeAt: lastSuccessfulProbeAt || null,
        lastConnectionOpenAt: lastConnectionOpenAt || null,
        probeAgeMs,
        consecutiveProbeFailures,
        lastDisconnectReason
    };
}

function startHealthServer() {
    const server = http.createServer((req, res) => {
        if (req.url !== '/healthz' && req.url !== '/readyz') {
            res.writeHead(404, { 'Content-Type': 'application/json' });
            res.end(JSON.stringify({ ok: false, error: 'not_found' }));
            return;
        }

        const snapshot = getHealthSnapshot();
        res.writeHead(snapshot.ok ? 200 : 503, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify(snapshot));
    });

    server.listen(HEALTH_PORT, '0.0.0.0', () => {
        console.log(`[HEALTH] Endpoint aktif di :${HEALTH_PORT}/healthz`);
    });
}

function scheduleReconnect(reason = 'unknown') {
    if (isShuttingDown || reconnectTimer) return;

    console.log(`[RECONNECT] Menjadwalkan reconnect dalam ${RECONNECT_DELAY_MS} ms. reason=${reason}`);
    startWatchdog();
    reconnectTimer = setTimeout(() => {
        reconnectTimer = null;
        connectToWhatsApp().catch((error) => {
            forceExit(`[RECONNECT] Gagal membuat socket baru: ${error.stack || error.message}`);
        });
    }, RECONNECT_DELAY_MS);
}

async function runLivenessProbe(sock, generation) {
    if (isShuttingDown || generation !== activeGeneration || activeConnectionState !== 'open' || isProbeRunning) {
        return;
    }

    const botJid = normalizeJid(sock?.user?.id);
    if (!botJid) {
        forceExit('[LIVENESS] sock.user.id tidak tersedia. Force exit.');
        return;
    }

    isProbeRunning = true;
    let timeoutHandle = null;

    try {
        await Promise.race([
            sock.fetchStatus(botJid),
            new Promise((_, reject) => {
                timeoutHandle = setTimeout(() => {
                    reject(new Error(`fetchStatus timeout ${LIVENESS_TIMEOUT_MS} ms`));
                }, LIVENESS_TIMEOUT_MS);
            })
        ]);

        consecutiveProbeFailures = 0;
        lastSuccessfulProbeAt = Date.now();
        console.log(`[LIVENESS] OK jid=${botJid}`);
    } catch (error) {
        consecutiveProbeFailures += 1;
        console.error(`[LIVENESS] FAIL ${consecutiveProbeFailures}/${LIVENESS_MAX_FAILURES}: ${error.message}`);

        if (consecutiveProbeFailures >= LIVENESS_MAX_FAILURES) {
            forceExit('[LIVENESS] Batas gagal terlampaui. Force exit untuk trigger auto-heal.');
        }
    } finally {
        if (timeoutHandle) clearTimeout(timeoutHandle);
        isProbeRunning = false;
    }
}

function startLivenessProbe(sock, generation) {
    clearLivenessProbe();
    consecutiveProbeFailures = 0;
    lastSuccessfulProbeAt = Date.now();

    livenessTimer = setInterval(() => {
        runLivenessProbe(sock, generation).catch((error) => {
            forceExit(`[LIVENESS] Unexpected probe error: ${error.stack || error.message}`);
        });
    }, LIVENESS_INTERVAL_MS);

    runLivenessProbe(sock, generation).catch((error) => {
        forceExit(`[LIVENESS] Initial probe error: ${error.stack || error.message}`);
    });
}

function shutdown(signal) {
    if (isShuttingDown) return;

    isShuttingDown = true;
    console.log(`[SHUTDOWN] Signal ${signal} diterima. Menutup bot.`);
    clearTimeout(watchdogTimer);
    clearTimeout(reconnectTimer);
    clearLivenessProbe();
    stopReportScheduler();
    destroySocket(activeSock);
    setTimeout(() => process.exit(0), 250);
}

async function safeReact(sock, jid, key, emoji) {
    if (REACT_INITIAL_DELAY_MS > 0) {
        await sleep(REACT_INITIAL_DELAY_MS);
    }

    let lastError = null;
    const keyId = key?.id || 'unknown';

    for (let attempt = 1; attempt <= REACT_MAX_RETRIES; attempt += 1) {
        try {
            await sock.sendMessage(jid, { react: { text: emoji, key } });

            if (attempt > 1) {
                console.log(`[REACT] RECOVERED emoji=${emoji} attempt=${attempt} id=${keyId}`);
            }

            return true;
        } catch (e) {
            lastError = e;
            const message = e?.message || String(e);
            console.error(`[REACT] FAIL attempt=${attempt}/${REACT_MAX_RETRIES} emoji=${emoji} id=${keyId} error=${message}`);

            if (attempt < REACT_MAX_RETRIES) {
                await sleep(REACT_RETRY_DELAY_MS * attempt);
            }
        }
    }

    console.error(`[REACT] GIVEUP emoji=${emoji} id=${keyId} error=${lastError?.message || 'unknown'}`);
    return false;
}

function appendWebhookFailure(entry) {
    try {
        fs.appendFileSync(WEBHOOK_FAILURE_LOG, `${JSON.stringify(entry)}\n`);
    } catch (error) {
        console.error(`[WEBHOOK] Gagal menulis failure spool: ${error.message}`);
    }
}

function isRetryableStatus(status) {
    return status === 408 || status === 425 || status === 429 || status >= 500;
}

async function parseWebhookResponse(res) {
    const bodyText = await res.text();
    const contentType = res.headers.get('content-type') || '';
    let data = null;

    try {
        data = bodyText ? JSON.parse(bodyText) : null;
    } catch {}

    const success =
        (data && (data.success === true || String(data.success).toLowerCase() === 'true')) ||
        bodyText.trim().toLowerCase() === 'ok';

    return {
        ok: res.ok,
        status: res.status,
        contentType,
        bodyText,
        data,
        success
    };
}

function getGoogleServiceAccountRaw() {
    const encoded = process.env.GOOGLE_SERVICE_ACCOUNT_JSON_B64;
    if (encoded) {
        try {
            return Buffer.from(encoded, 'base64').toString('utf8');
        } catch (error) {
            throw new Error(`GOOGLE_SERVICE_ACCOUNT_JSON_B64 is not valid base64: ${error.message}`);
        }
    }

    return process.env.GOOGLE_SERVICE_ACCOUNT_JSON || '';
}

function hasGoogleSheetsAuth() {
    return Boolean(process.env.GOOGLE_SERVICE_ACCOUNT_JSON_B64 || process.env.GOOGLE_SERVICE_ACCOUNT_JSON);
}

function getSheetRange(sheetName, a1Range) {
    const escapedSheetName = String(sheetName).replace(/'/g, "''");
    return `'${escapedSheetName}'!${a1Range}`;
}

function columnNumberToLetter(columnNumber) {
    let value = Number(columnNumber);
    let result = '';

    while (value > 0) {
        const remainder = (value - 1) % 26;
        result = String.fromCharCode(65 + remainder) + result;
        value = Math.floor((value - 1) / 26);
    }

    return result;
}

function normalizeCellValue(value) {
    return String(value || '').trim().toUpperCase();
}

function getJakartaDateParts(now = new Date()) {
    const options = {
        timeZone: 'Asia/Jakarta',
        year: 'numeric',
        month: '2-digit',
        day: '2-digit',
        hour: '2-digit',
        minute: '2-digit',
        hour12: false
    };
    const parts = new Intl.DateTimeFormat('id-ID', options).formatToParts(now);
    const map = new Map(parts.map((part) => [part.type, part.value]));
    const year = map.get('year');
    const month = map.get('month');
    const day = map.get('day');
    const hour = map.get('hour');
    const minute = map.get('minute');

    return {
        year,
        month,
        day,
        hour,
        minute,
        dateKey: `${year}-${month}-${day}`,
        timeKey: `${hour}:${minute}`
    };
}

function getTimestamp(now = new Date()) {
    const { day, month, hour, minute } = getJakartaDateParts(now);
    return `${day}/${month}/ ${hour}.${minute}`;
}

function formatDateKey(dateKey) {
    const [year, month, day] = String(dateKey || '').split('-');
    if (!year || !month || !day) return String(dateKey || '');
    return `${day}/${month}/${year}`;
}

function formatSlotDescription(slotLabel) {
    return slotLabel === '16.00'
        ? 'Rekap sementara sampai 16.00 WIB'
        : 'Rekap penutupan hari';
}

function shiftDateKey(dateKey, deltaDays) {
    const [year, month, day] = String(dateKey || '').split('-').map(Number);
    if (!year || !month || !day) return '';

    const utcDate = new Date(Date.UTC(year, month - 1, day + deltaDays));
    const nextYear = utcDate.getUTCFullYear();
    const nextMonth = String(utcDate.getUTCMonth() + 1).padStart(2, '0');
    const nextDay = String(utcDate.getUTCDate()).padStart(2, '0');
    return `${nextYear}-${nextMonth}-${nextDay}`;
}

function readJsonFile(filePath, fallbackValue) {
    try {
        if (!fs.existsSync(filePath)) {
            return fallbackValue;
        }
        return JSON.parse(fs.readFileSync(filePath, 'utf8'));
    } catch (error) {
        console.error(`[FILE] Gagal membaca ${filePath}: ${error.message}`);
        return fallbackValue;
    }
}

function writeJsonFile(filePath, value) {
    try {
        fs.writeFileSync(filePath, JSON.stringify(value, null, 2));
    } catch (error) {
        console.error(`[FILE] Gagal menulis ${filePath}: ${error.message}`);
    }
}

function appendRekapLog(entry) {
    try {
        fs.appendFileSync(REKAP_LOG_FILE, `${JSON.stringify(entry)}\n`);
    } catch (error) {
        console.error(`[REKAP] Gagal menulis log: ${error.message}`);
    }
}

function recordRekapEvent({
    prefix,
    number,
    kode,
    divisi,
    subDivisi,
    petugas,
    groupName,
    rawLine,
    timestamp
}) {
    const nowParts = getJakartaDateParts();
    appendRekapLog({
        loggedAt: new Date().toISOString(),
        dateKey: nowParts.dateKey,
        timeKey: nowParts.timeKey,
        kodePrefix: normalizeCellValue(prefix),
        nomor: String(number || '').trim(),
        kode: normalizeCellValue(kode),
        divisi: normalizeCellValue(divisi),
        subDivisi: normalizeCellValue(subDivisi),
        petugas: String(petugas || '').trim(),
        groupName: String(groupName || '').trim(),
        rawLine: String(rawLine || '').trim(),
        timestamp: String(timestamp || getTimestamp()).trim()
    });
}

function readRekapEntriesForDate(dateKey) {
    if (!fs.existsSync(REKAP_LOG_FILE)) {
        return [];
    }

    try {
        return fs.readFileSync(REKAP_LOG_FILE, 'utf8')
            .split(/\r?\n/)
            .filter(Boolean)
            .map((line) => {
                try {
                    return JSON.parse(line);
                } catch {
                    return null;
                }
            })
            .filter((entry) => entry && entry.dateKey === dateKey);
    } catch (error) {
        console.error(`[REKAP] Gagal membaca log: ${error.message}`);
        return [];
    }
}

function buildDailyReportSummary(entries) {
    const prefixMap = new Map();
    const allCodes = new Set();

    for (const entry of entries) {
        const prefix = normalizeCellValue(entry.kodePrefix);
        const kode = normalizeCellValue(entry.kode);
        const divisi = normalizeCellValue(entry.divisi) || 'LAINNYA';
        if (!prefix || !kode) continue;

        allCodes.add(kode);

        if (!prefixMap.has(prefix)) {
            prefixMap.set(prefix, {
                codes: new Set(),
                divisions: new Map()
            });
        }

        const bucket = prefixMap.get(prefix);
        bucket.codes.add(kode);

        if (!bucket.divisions.has(divisi)) {
            bucket.divisions.set(divisi, new Set());
        }
        bucket.divisions.get(divisi).add(kode);
    }

    return {
        totalPrefixes: prefixMap.size,
        totalJobs: allCodes.size,
        prefixes: [...prefixMap.entries()]
            .sort(([left], [right]) => left.localeCompare(right))
            .map(([prefix, bucket]) => {
                const divisions = [...bucket.divisions.entries()]
                    .map(([divisi, codes]) => ({ divisi, total: codes.size }))
                    .sort((left, right) => {
                        const leftIndex = REPORT_DIVISION_ORDER.indexOf(left.divisi);
                        const rightIndex = REPORT_DIVISION_ORDER.indexOf(right.divisi);
                        const normalizedLeft = leftIndex === -1 ? Number.MAX_SAFE_INTEGER : leftIndex;
                        const normalizedRight = rightIndex === -1 ? Number.MAX_SAFE_INTEGER : rightIndex;
                        if (normalizedLeft !== normalizedRight) {
                            return normalizedLeft - normalizedRight;
                        }
                        return left.divisi.localeCompare(right.divisi);
                    });

                return {
                    prefix,
                    totalJobs: bucket.codes.size,
                    divisions
                };
            })
    };
}

function buildDailyReportMessage(dateKey, slotLabel) {
    const entries = readRekapEntriesForDate(dateKey);
    const summary = buildDailyReportSummary(entries);
    const reportType = formatSlotDescription(slotLabel);
    const lines = [
        'LAPORAN HARIAN BOT',
        `Tanggal : ${formatDateKey(dateKey)}`,
        `Sesi    : ${slotLabel} WIB`,
        `Jenis   : ${reportType}`,
        '',
        'RINGKASAN',
        `- Total job unik : ${summary.totalJobs}`,
        `- Prefix aktif   : ${summary.totalPrefixes}`
    ];

    if (!summary.prefixes.length) {
        lines.push('', 'DETAIL PREFIX', 'Belum ada job yang tercatat pada periode ini.');
        return lines.join('\n');
    }

    lines.push('', 'DETAIL PREFIX');

    summary.prefixes.forEach((item, index) => {
        const divisionText = item.divisions.length
            ? item.divisions.map((division) => `${division.divisi} ${division.total}`).join(' | ')
            : '-';
        lines.push(`${index + 1}. ${item.prefix}`);
        lines.push(`   Total job   : ${item.totalJobs}`);
        lines.push(`   Divisi aktif: ${item.divisions.length}`);
        lines.push(`   Sebaran     : ${divisionText}`);
    });

    return lines.join('\n');
}

function getManualReportTarget(argument, nowParts) {
    const normalizedArgument = normalizeCellValue(argument || '');
    if (normalizedArgument === 'KEMARIN') {
        return {
            dateKey: shiftDateKey(nowParts.dateKey, -1),
            slotLabel: '00.00',
            description: 'preview kemarin'
        };
    }

    return {
        dateKey: nowParts.dateKey,
        slotLabel: '16.00',
        description: 'preview hari ini'
    };
}

function parseReportCommand(text, nowParts) {
    const trimmed = String(text || '').trim();
    const match = trimmed.match(/^!laporan(?:\s+(\S+))?(?:\s+(\S+))?$/i);
    if (!match) return null;

    const firstArg = normalizeCellValue(match[1] || '');
    const secondArg = normalizeCellValue(match[2] || '');

    if (!firstArg) {
        return {
            mode: 'preview',
            ...getManualReportTarget('', nowParts)
        };
    }

    if (firstArg === 'HELP') {
        return { mode: 'help' };
    }

    if (firstArg === 'KIRIM') {
        return {
            mode: 'send',
            ...getManualReportTarget(secondArg, nowParts)
        };
    }

    if (firstArg === 'HARIINI' || firstArg === 'KEMARIN') {
        return {
            mode: 'preview',
            ...getManualReportTarget(firstArg, nowParts)
        };
    }

    return { mode: 'help' };
}

function getReportState() {
    const state = readJsonFile(REPORT_STATE_FILE, { sentSlots: {} });
    if (!state || typeof state !== 'object') {
        return { sentSlots: {} };
    }
    if (!state.sentSlots || typeof state.sentSlots !== 'object') {
        state.sentSlots = {};
    }
    return state;
}

function pruneReportState(state) {
    const keys = Object.keys(state.sentSlots || {}).sort().reverse().slice(0, 120);
    const nextSentSlots = {};
    for (const key of keys) {
        nextSentSlots[key] = state.sentSlots[key];
    }
    state.sentSlots = nextSentSlots;
    return state;
}

async function findGroupJidByName(sock, targetName) {
    const normalizedTarget = String(targetName || '').trim().toLowerCase();
    if (!normalizedTarget) return null;

    if (reportGroupJidCache && groupNameCache.get(reportGroupJidCache) === normalizedTarget) {
        return reportGroupJidCache;
    }

    for (const [jid, name] of groupNameCache.entries()) {
        if (name === normalizedTarget) {
            reportGroupJidCache = jid;
            return jid;
        }
    }

    try {
        const groups = await sock.groupFetchAllParticipating();
        for (const [jid, metadata] of Object.entries(groups || {})) {
            const subject = String(metadata?.subject || '').trim().toLowerCase();
            if (!subject) continue;
            groupNameCache.set(jid, subject);
            if (subject === normalizedTarget) {
                reportGroupJidCache = jid;
                return jid;
            }
        }
    } catch (error) {
        console.error(`[REPORT] Gagal mengambil daftar grup: ${error.message}`);
    }

    return null;
}

function getScheduledReportTarget(nowParts) {
    const hour = Number(nowParts.hour);
    const minute = Number(nowParts.minute);
    const currentMinuteOfDay = (hour * 60) + minute;
    const target1600 = 16 * 60;

    if (currentMinuteOfDay >= target1600 && currentMinuteOfDay < (target1600 + REPORT_WINDOW_MINUTES)) {
        return {
            slotKey: `16:00::${nowParts.dateKey}`,
            slotLabel: '16.00',
            dateKey: nowParts.dateKey
        };
    }

    if (currentMinuteOfDay >= 0 && currentMinuteOfDay < REPORT_WINDOW_MINUTES) {
        const previousDateKey = shiftDateKey(nowParts.dateKey, -1);
        return {
            slotKey: `00:00::${previousDateKey}`,
            slotLabel: '00.00',
            dateKey: previousDateKey
        };
    }

    return null;
}

async function runReportScheduler(sock, generation) {
    if (
        isShuttingDown ||
        generation !== activeGeneration ||
        activeConnectionState !== 'open' ||
        isReportDispatchRunning
    ) {
        return;
    }

    const nowParts = getJakartaDateParts();
    const target = getScheduledReportTarget(nowParts);
    if (!target?.dateKey) {
        return;
    }

    const state = getReportState();
    if (state.sentSlots[target.slotKey]) {
        return;
    }

    isReportDispatchRunning = true;

    try {
        const message = buildDailyReportMessage(target.dateKey, target.slotLabel);
        const groupJid = await findGroupJidByName(sock, REPORT_GROUP_NAME);
        if (!groupJid) {
            throw new Error(`Grup "${REPORT_GROUP_NAME}" tidak ditemukan`);
        }

        await sock.sendMessage(groupJid, { text: message });

        state.sentSlots[target.slotKey] = {
            sentAt: new Date().toISOString(),
            groupJid,
            reportDate: target.dateKey
        };
        writeJsonFile(REPORT_STATE_FILE, pruneReportState(state));
        console.log(`[REPORT] Terkirim slot=${target.slotKey} group=${REPORT_GROUP_NAME}`);
    } catch (error) {
        console.error(`[REPORT] Gagal mengirim laporan: ${error.message}`);
    } finally {
        isReportDispatchRunning = false;
    }
}

function startReportScheduler(sock, generation) {
    stopReportScheduler();
    reportSchedulerTimer = setInterval(() => {
        runReportScheduler(sock, generation).catch((error) => {
            console.error(`[REPORT] Scheduler error: ${error.stack || error.message}`);
        });
    }, REPORT_SCHEDULER_INTERVAL_MS);

    runReportScheduler(sock, generation).catch((error) => {
        console.error(`[REPORT] Initial scheduler error: ${error.stack || error.message}`);
    });
}

async function sendManualReport(sock, targetJid, dateKey, slotLabel, label) {
    const message = buildDailyReportMessage(dateKey, slotLabel);
    await sock.sendMessage(targetJid, { text: message });
    console.log(`[REPORT] Manual send target=${targetJid} label=${label} date=${dateKey} slot=${slotLabel}`);
}

async function getSheetsClient() {
    if (!sheetsClientPromise) {
        sheetsClientPromise = (async () => {
            const raw = getGoogleServiceAccountRaw();
            if (!raw) {
                throw new Error('GOOGLE_SERVICE_ACCOUNT_JSON or GOOGLE_SERVICE_ACCOUNT_JSON_B64 is missing');
            }

            let credentials;
            try {
                credentials = JSON.parse(raw);
            } catch (error) {
                throw new Error(`Google service account JSON is invalid: ${error.message}`);
            }

            const auth = new google.auth.GoogleAuth({
                credentials,
                scopes: ['https://www.googleapis.com/auth/spreadsheets']
            });
            const client = await auth.getClient();
            return google.sheets({ version: 'v4', auth: client });
        })().catch((error) => {
            sheetsClientPromise = null;
            throw error;
        });
    }

    return sheetsClientPromise;
}

async function findRowByKode({ sheets, spreadsheetId, sheetName, kode, lookupColumn = 1 }) {
    const cacheKey = getSheetsLookupCacheKey(spreadsheetId, sheetName, kode, lookupColumn);
    const cachedRowNumber = getCachedRowLookup(cacheKey);
    if (cachedRowNumber !== undefined) {
        return cachedRowNumber;
    }

    const rowsByKode = await getSheetRowIndex({
        sheets,
        spreadsheetId,
        sheetName,
        lookupColumn
    });
    const targetKode = normalizeCellValue(kode);
    const rowNumber = rowsByKode.get(targetKode) || null;

    if (rowNumber) {
        setCachedRowLookup(cacheKey, rowNumber, SHEETS_LOOKUP_CACHE_TTL_MS);
        return rowNumber;
    }

    setCachedRowLookup(cacheKey, null, SHEETS_NEGATIVE_LOOKUP_CACHE_TTL_MS);
    return null;
}

async function writePayloadToSheet(config, payload) {
    const spreadsheetId = config?.spreadsheet_id;
    if (!spreadsheetId) {
        throw new Error('spreadsheet_id is missing in config');
    }

    const sheetName = payload.sheet || config.sheet;
    const lookupColumn = Number(config.lookup_column || 1);
    const offset = Number(payload.offset || 0);
    const sheets = await getSheetsClient();
    const rowNumber = await findRowByKode({
        sheets,
        spreadsheetId,
        sheetName,
        kode: payload.kode,
        lookupColumn
    });

    if (!rowNumber) {
        throw new Error(`kode ${payload.kode} not found on sheet ${sheetName}`);
    }

    const targetRow = rowNumber + offset;
    const data = [];

    if (payload.kolom && payload.timestamp) {
        data.push({
            range: getSheetRange(sheetName, `${columnNumberToLetter(payload.kolom)}${targetRow}`),
            values: [[payload.timestamp]]
        });
    }

    if (payload.kolomNama && payload.namaPetugas) {
        data.push({
            range: getSheetRange(sheetName, `${columnNumberToLetter(payload.kolomNama)}${targetRow}`),
            values: [[payload.namaPetugas]]
        });
    }

    if (payload.kolom_petugas && payload.petugas) {
        data.push({
            range: getSheetRange(sheetName, `${columnNumberToLetter(payload.kolom_petugas)}${targetRow}`),
            values: [[payload.petugas]]
        });
    }

    if (!data.length) {
        throw new Error(`no update data generated for ${payload.kode}`);
    }

    await runSheetsRequest(() => sheets.spreadsheets.values.batchUpdate({
        spreadsheetId,
        requestBody: {
            valueInputOption: 'USER_ENTERED',
            data
        }
    }));

    const cacheKey = getSheetsLookupCacheKey(spreadsheetId, sheetName, payload.kode, lookupColumn);
    setCachedRowLookup(cacheKey, rowNumber, SHEETS_LOOKUP_CACHE_TTL_MS);

    return {
        success: true,
        spreadsheetId,
        sheetName,
        rowNumber: targetRow
    };
}

function getGoogleErrorStatus(error) {
    return Number(
        error?.code ||
        error?.response?.status ||
        error?.status
    ) || 0;
}

async function callSheetsApi(tag, config, payload) {
    let lastError = null;

    for (let attempt = 1; attempt <= WEBHOOK_MAX_RETRIES; attempt += 1) {
        try {
            const result = await writePayloadToSheet(config, payload);
            if (attempt > 1) {
                console.log(`[SHEETS ${tag}] RECOVERED attempt=${attempt} row=${result.rowNumber}`);
            }
            return result;
        } catch (error) {
            lastError = error;
            const status = getGoogleErrorStatus(error);
            console.error(`[SHEETS ${tag}] RETRY attempt=${attempt}/${WEBHOOK_MAX_RETRIES} status=${status || 'unknown'} error=${error.message}`);

            if (!(status === 408 || status === 425 || status === 429 || status >= 500)) {
                break;
            }

            if (attempt < WEBHOOK_MAX_RETRIES) {
                const delayMs = status === 429
                    ? SHEETS_429_RETRY_DELAY_MS * attempt
                    : WEBHOOK_RETRY_DELAY_MS * attempt;
                await sleep(delayMs);
            }
        }
    }

    appendWebhookFailure({
        failedAt: new Date().toISOString(),
        tag,
        type: 'sheets_api',
        spreadsheetId: config?.spreadsheet_id || null,
        sheet: payload?.sheet || config?.sheet || null,
        payload,
        error: lastError?.message || 'unknown_sheets_error'
    });

    throw lastError || new Error('unknown_sheets_error');
}

async function callDataSink(tag, config, payload) {
    if (config?.spreadsheet_id && hasGoogleSheetsAuth()) {
        console.log(`[DATASINK] tag=${tag} prefix=${payload?.sheet || config?.sheet || 'unknown'} mode=sheets_api`);
        return callSheetsApi(tag, config, payload);
    }

    console.log(`[DATASINK] tag=${tag} prefix=${payload?.sheet || config?.sheet || 'unknown'} mode=webhook`);
    return callWebhook(tag, config.webhook, payload);
}

async function callWebhook(tag, url, payload) {
    let lastError = null;

    for (let attempt = 1; attempt <= WEBHOOK_MAX_RETRIES; attempt += 1) {
        const controller = new AbortController();
        const timeoutHandle = setTimeout(() => controller.abort(), WEBHOOK_TIMEOUT_MS);

        try {
            const res = await fetch(url, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify(payload),
                signal: controller.signal
            });

            const parsed = await parseWebhookResponse(res);
            clearTimeout(timeoutHandle);

            if (parsed.success) {
                if (attempt > 1) {
                    console.log(`[WEBHOOK ${tag}] RECOVERED attempt=${attempt} status=${parsed.status}`);
                }
                return parsed;
            }

            const details =
                `status=${parsed.status} ok=${parsed.ok} contentType=${parsed.contentType || 'unknown'} body=${truncate(parsed.bodyText)}`;
            lastError = new Error(details);

            if (!isRetryableStatus(parsed.status)) {
                break;
            }

            console.error(`[WEBHOOK ${tag}] RETRY attempt=${attempt}/${WEBHOOK_MAX_RETRIES} ${details}`);
        } catch (error) {
            clearTimeout(timeoutHandle);
            const message = error.name === 'AbortError'
                ? `timeout ${WEBHOOK_TIMEOUT_MS} ms`
                : (error.message || String(error));
            lastError = new Error(message);
            console.error(`[WEBHOOK ${tag}] RETRY attempt=${attempt}/${WEBHOOK_MAX_RETRIES} error=${lastError.message}`);
        }

        if (attempt < WEBHOOK_MAX_RETRIES) {
            await sleep(WEBHOOK_RETRY_DELAY_MS * attempt);
        }
    }

    appendWebhookFailure({
        failedAt: new Date().toISOString(),
        tag,
        url,
        payload,
        error: lastError?.message || 'unknown_webhook_error'
    });

    throw lastError || new Error('unknown_webhook_error');
}

async function connectToWhatsApp() {
    if (isShuttingDown) return;

    startWatchdog();
    clearLivenessProbe();
    destroySocket(activeSock);
    activeSock = null;
    activeConnectionState = 'connecting';

    const { default: makeWASocket, useMultiFileAuthState, DisconnectReason, fetchLatestBaileysVersion } = await import('@whiskeysockets/baileys');
    const { state, saveCreds } = await useMultiFileAuthState('auth_info_baileys');
    const { version, isLatest } = await fetchLatestBaileysVersion();
    console.log(`[BOOT] Menggunakan WA v${version.join('.')}, isLatest=${isLatest}`);

    const generation = ++activeGeneration;
    const sock = makeWASocket({
        version,
        auth: state,
        printQRInTerminal: false,
        logger: pino({ level: 'silent' }),
        browser: ['TeknosBot-MVP', 'Chrome', '1.0.0'],
        keepAliveIntervalMs: 10000,
        markOnlineOnConnect: true,
        connectTimeoutMs: 60000,
        getMessage: async (key) => messageCache.get(key.id) || undefined
    });

    activeSock = sock;

    sock.ev.on('connection.update', (update) => {
        if (generation !== activeGeneration) return;

        const { connection, lastDisconnect, qr } = update;

        if (qr) {
            console.log('[AUTH] QR Code muncul, silakan scan.');
            qrcode.generate(qr, { small: true });
            stopWatchdog();
        }

        if (connection === 'close') {
            activeConnectionState = 'close';
            clearLivenessProbe();
            stopReportScheduler();
            lastDisconnectReason = String(
                (lastDisconnect?.error instanceof Boom && lastDisconnect.error.output?.statusCode) ||
                lastDisconnect?.error?.message ||
                'unknown_close'
            );

            const shouldReconnect =
                (lastDisconnect?.error instanceof Boom)?.output?.statusCode !== DisconnectReason.loggedOut;

            console.log(`[WA] connection=close reconnect=${shouldReconnect} reason=${lastDisconnectReason}`);

            if (shouldReconnect) {
                scheduleReconnect(lastDisconnectReason);
            } else {
                forceExit('[AUTH] Sesi logout. Hapus folder auth_info_baileys lalu scan ulang.');
            }

            return;
        }

        if (connection === 'open') {
            activeConnectionState = 'open';
            lastConnectionOpenAt = Date.now();
            lastSuccessfulProbeAt = Date.now();
            stopWatchdog();
            startLivenessProbe(sock, generation);
            startReportScheduler(sock, generation);
            console.log('[WA] connection=open bot siap menerima pesan.');
            return;
        }

        if (connection) {
            activeConnectionState = connection;
            console.log(`[WA] connection=${connection}`);
        }
    });

    sock.ev.on('creds.update', saveCreds);

    sock.ev.on('messages.upsert', async (m) => {
        if (generation !== activeGeneration) return;
        if (m.type !== 'notify') return;

        const msg = m.messages[0];
        if (!msg?.message || msg.key.fromMe) return;

        if (msg.key.id) {
            messageCache.set(msg.key.id, msg.message);
            if (messageCache.size > 1000) {
                messageCache.delete(messageCache.keys().next().value);
            }
        }

        const text =
            msg.message?.conversation ||
            msg.message?.extendedTextMessage?.text ||
            msg.message?.imageMessage?.caption ||
            msg.message?.videoMessage?.caption ||
            msg.message?.documentMessage?.caption ||
            '';

        if (!text) return;

        const from = msg.key.remoteJid;
        const isGroup = from.endsWith('@g.us');

        const reply = async (teks) => {
            await sock.sendMessage(from, { text: teks }, { quoted: msg });
        };

        let groupName = '';
        if (isGroup) {
            if (groupNameCache.has(from)) {
                groupName = groupNameCache.get(from);
            } else {
                try {
                    const groupMetadata = await sock.groupMetadata(from);
                    if (groupMetadata?.subject) {
                        groupName = groupMetadata.subject.toLowerCase();
                        groupNameCache.set(from, groupName);
                    }
                } catch (e) {
                    console.warn('Gagal memuat metadata grup:', e.message);
                    return;
                }
            }
        }

        if (text === '!ping') return reply('Bot aktif (Engine: Baileys).');
        if (text === '!status') {
            return reply(`Bot aktif.\nPrefix aktif: ${Object.keys(sheetsConfig).length}\nServer: ${getTimestamp()}`);
        }
        if (text === '!reset') {
            await reply('Restarting...');
            process.exit(1);
        }

        const nowParts = getJakartaDateParts();
        const reportCommand = parseReportCommand(text, nowParts);
        if (reportCommand) {
            if (reportCommand.mode === 'help') {
                return reply(`Format laporan:\n${REPORT_COMMAND_HELP}`);
            }

            try {
                if (reportCommand.mode === 'send') {
                    const reportGroupJid = await findGroupJidByName(sock, REPORT_GROUP_NAME);
                    if (!reportGroupJid) {
                        return reply(`Grup "${REPORT_GROUP_NAME}" belum ditemukan.`);
                    }

                    await sendManualReport(
                        sock,
                        reportGroupJid,
                        reportCommand.dateKey,
                        reportCommand.slotLabel,
                        reportCommand.description
                    );
                    return reply(
                        `Laporan ${reportCommand.description} berhasil dikirim ke grup ${REPORT_GROUP_NAME}.`
                    );
                }

                await sendManualReport(
                    sock,
                    from,
                    reportCommand.dateKey,
                    reportCommand.slotLabel,
                    reportCommand.description
                );
                return;
            } catch (error) {
                console.error(`[REPORT] Manual command gagal: ${error.message}`);
                return reply(`Gagal membuat laporan: ${error.message}`);
            }
        }

        const lines = text.split('\n');

        if (isGroup && groupName.includes('apo printing')) {
            for (const line of lines) {
                const match = line.trim().match(/\b([A-Z]{2,3})\s(\d{1,5})\s+([a-zA-Z\/]+(?:\s[a-zA-Z]+)*)(?:\s(\d+))?$/i);
                if (!match) continue;

                const [_, prefix, number, namaPetugas, extraNumber] = match;
                const config = sheetsConfig[prefix.toUpperCase()];
                if (!config?.webhook) continue;

                const isCut = namaPetugas.toLowerCase().endsWith('cut');
                const namaFinal = isCut ? namaPetugas.replace(/cut$/i, '').trim() : namaPetugas;
                const kode = `${prefix.toUpperCase()} ${number}`;

                try {
                    const payload = {
                        kode,
                        sheet: config.sheet,
                        timestamp: getTimestamp(),
                        kolom: isCut ? (config.kolom_cut || 17) : (config.kolom_printing || 15),
                        namaPetugas: namaFinal,
                        kolomNama: isCut ? (config.kolom_petugas_cut || 18) : (config.kolom_petugas || 16),
                        offset: extraNumber ? Number(extraNumber) : 0
                    };
                    const result = await callDataSink('PRINTING', config, payload);
                    if (result.success) {
                        recordRekapEvent({
                            prefix,
                            number,
                            kode,
                            divisi: 'PRINTING',
                            subDivisi: isCut ? 'CUT' : 'PRINTING',
                            petugas: namaFinal,
                            groupName,
                            rawLine: line,
                            timestamp: payload.timestamp
                        });
                        await safeReact(sock, from, msg.key, isCut ? '✂️' : '🖨️');
                    }
                } catch (err) {
                    console.error('Error Datasink Printing:', err.message);
                }
            }

            return;
        }

        if (isGroup && groupName.includes('apo finishing')) {
            for (const line of lines) {
                const match = line.trim().match(/\b([A-Z]{2,3})\s(\d{1,5})\s+([a-zA-Z\/]+)\s+(CU|CP|PAC|PT|DR)(?:\s+(\d+))?$/i);
                if (!match) continue;

                const [_, prefix, number, petugas, jenis, offset] = match;
                const config = sheetsConfig[prefix.toUpperCase()];
                if (!config?.webhook) continue;

                const mapping = {
                    CU: { tgl: config.kolom_cheker_undangan, ptg: config.kolom_petugas_cheker_undangan, emo: '🗒️' },
                    CP: { tgl: config.kolom_cheker_paket, ptg: config.kolom_petugas_cheker_paket, emo: '📝' },
                    PAC: { tgl: config.kolom_cheker_packing, ptg: config.kolom_petugas_cheker_packing, emo: '📦' },
                    PT: { tgl: config.kolom_potong, ptg: config.kolom_petugas_potong, emo: '🪓' },
                    DR: { tgl: config.kolom_driver, ptg: config.kolom_petugas_driver, emo: '🚚' }
                };

                const target = mapping[jenis.toUpperCase()];
                if (!target || !target.tgl) continue;

                try {
                    const payload = {
                        kode: `${prefix.toUpperCase()} ${number}`,
                        sheet: config.sheet,
                        timestamp: getTimestamp(),
                        kolom: target.tgl,
                        kolom_petugas: target.ptg,
                        petugas,
                        offset: offset || 0
                    };
                    const result = await callDataSink('FINISHING', config, payload);
                    if (result.success) {
                        recordRekapEvent({
                            prefix,
                            number,
                            kode: `${prefix.toUpperCase()} ${number}`,
                            divisi: 'FINISHING',
                            subDivisi: jenis.toUpperCase(),
                            petugas,
                            groupName,
                            rawLine: line,
                            timestamp: payload.timestamp
                        });
                        await safeReact(sock, from, msg.key, target.emo);
                    }
                } catch (err) {
                    console.error('Error Datasink Finishing:', err.message);
                }
            }

            return;
        }

        if (isGroup && groupName.includes('apo csm')) {
            for (const line of lines) {
                const match = line.trim().match(/\b([A-Z]{2,3})\s(\d{1,5})\s+([a-zA-Z\/]+)\s+(SA)(?:\s+(\d+))?$/i);
                if (!match) continue;

                const [_, prefix, number, petugas, jenis, offset] = match;
                const config = sheetsConfig[prefix.toUpperCase()];
                if (!config?.webhook) continue;

                if (jenis.toUpperCase() === 'SA') {
                    try {
                        const payload = {
                            kode: `${prefix.toUpperCase()} ${number}`,
                            sheet: config.sheet,
                            timestamp: getTimestamp(),
                            kolom: config.kolom_cs,
                            kolom_petugas: config.kolom_petugas_cs,
                            petugas,
                            offset: offset || 0
                        };
                        const result = await callDataSink('CSM', config, payload);
                        if (result.success) {
                            recordRekapEvent({
                                prefix,
                                number,
                                kode: `${prefix.toUpperCase()} ${number}`,
                                divisi: 'CSM',
                                subDivisi: 'SA',
                                petugas,
                                groupName,
                                rawLine: line,
                                timestamp: payload.timestamp
                            });
                            await safeReact(sock, from, msg.key, '🎀');
                        }
                    } catch (err) {
                        console.error('Error Datasink CSM:', err.message);
                    }
                }
            }

            return;
        }

        for (const line of lines) {
            const clean = line.trim().replace(/[*_~`]/g, '');
            const match = clean.match(/\b([A-Z]{2,3})\s(\d{1,5})(?:\s([1-4]))?(?:\s+([a-zA-Z\/]+))?$/i);
            if (!match) continue;

            const [_, prefix, number, kodeFix, namaPetugas] = match;
            const config = sheetsConfig[prefix.toUpperCase()];
            if (!config?.webhook) continue;
            const kode = `${prefix.toUpperCase()} ${number}`;

            const { day, month, hour, minute } = getJakartaDateParts();

            let timestamp;
            let kolomTarget;

            if (kodeFix && FIXED_TIMES[kodeFix]) {
                timestamp = `${day}/${month}/ ${FIXED_TIMES[kodeFix]}`;
                kolomTarget = config.kolom_fix;
            } else {
                timestamp = `${day}/${month}/ ${hour}.${minute}`;
                kolomTarget = config.kolom;
            }

            try {
                const payload = {
                    kode,
                    sheet: config.sheet,
                    timestamp,
                    kolom: kolomTarget,
                    ...(namaPetugas && config.kolom_petugas_desain && {
                        namaPetugas,
                        kolomNama: config.kolom_petugas_desain
                    })
                };
                const result = await callDataSink('DESAIN', config, payload);
                if (result.success) {
                    recordRekapEvent({
                        prefix,
                        number,
                        kode,
                        divisi: 'DESAIN',
                        subDivisi: kodeFix && FIXED_TIMES[kodeFix] ? 'FIX' : 'DESAIN',
                        petugas: namaPetugas,
                        groupName,
                        rawLine: line,
                        timestamp
                    });
                    await safeReact(sock, from, msg.key, '✅');
                }
            } catch (err) {
                console.error('Error Datasink Desain:', err.message);
            }
        }
    });
}

startHealthServer();

process.on('SIGTERM', () => shutdown('SIGTERM'));
process.on('SIGINT', () => shutdown('SIGINT'));
process.on('uncaughtException', (error) => {
    forceExit(`[FATAL] uncaughtException: ${error.stack || error.message}`);
});
process.on('unhandledRejection', (reason) => {
    const message = reason instanceof Error ? (reason.stack || reason.message) : String(reason);
    forceExit(`[FATAL] unhandledRejection: ${message}`);
});

connectToWhatsApp().catch((error) => {
    forceExit(`[BOOT] Gagal start socket: ${error.stack || error.message}`);
});
