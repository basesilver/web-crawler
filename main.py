import asyncio
import csv
import hashlib
import json
import logging
import os
import re
import sqlite3
import sys
import time
from collections import defaultdict
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Optional
from urllib.parse import urljoin, urlparse, urlencode, parse_qs, ParseResult
from urllib.robotparser import RobotFileParser

import aiohttp
from aiohttp import ClientTimeout, TCPConnector
from bs4 import BeautifulSoup
from rich.console import Console
from rich.table import Table
from rich.live import Live
from rich.layout import Layout
from rich.text import Text
from rich import box

try:
    from playwright.async_api import async_playwright
    HAS_PLAYWRIGHT = True
except ImportError:
    HAS_PLAYWRIGHT = False

try:
    import brotli
    HAS_BROTLI = True
except ImportError:
    HAS_BROTLI = False

console = Console()

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(message)s",
    datefmt="%H:%M:%S",
    handlers=[logging.StreamHandler(sys.stdout)],
)
log = logging.getLogger("crawler")
log.setLevel(logging.WARNING)


TRACKING_PARAMS = frozenset({
    "utm_source", "utm_medium", "utm_campaign", "utm_term", "utm_content",
    "fbclid", "gclid", "gclsrc", "dclid", "msclkid", "mc_cid", "mc_eid",
    "ref", "source", "si",
})

BINARY_EXTENSIONS = frozenset({
    ".pdf", ".zip", ".rar", ".tar", ".gz", ".7z", ".bz2", ".xz",
    ".jpg", ".jpeg", ".png", ".gif", ".svg", ".webp", ".ico", ".bmp", ".avif",
    ".mp4", ".avi", ".mkv", ".mov", ".webm", ".m4v", ".mpg", ".mpeg",
    ".mp3", ".wav", ".flac", ".ogg", ".m4a", ".wma", ".aac",
    ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx", ".odt", ".ods",
    ".exe", ".msi", ".dmg", ".pkg", ".deb", ".rpm",
    ".css", ".js", ".woff", ".woff2", ".ttf", ".eot",
})

BINARY_MIME_PREFIXES = frozenset({
    "application/pdf", "application/zip", "application/x-rar-compressed",
    "application/gzip", "application/x-tar", "application/x-7z-compressed",
    "image/", "video/", "audio/",
    "application/msword", "application/vnd.openxmlformats-officedocument",
    "application/vnd.ms-excel", "application/vnd.ms-powerpoint",
    "application/vnd.oasis.opendocument",
    "application/octet-stream",
    "application/x-msdownload",
})

SOFT_404_PATTERNS = [
    re.compile(r"(?i)page\s+not\s+found"),
    re.compile(r"(?i)not\s+found"),
    re.compile(r"(?i)404\s+(error|not\s+found)"),
    re.compile(r"(?i)this\s+page\s+(doesn'?t\s+exist|could\s+not\s+be\s+found)"),
    re.compile(r"(?i)no\s+results?\s+found"),
    re.compile(r"(?i)page\s+does\s+not\s+exist"),
    re.compile(r"(?i)strona\s+nie\s+znaleziona"),
    re.compile(r"(?i)nie\s+znaleziono"),
]


def normalize_url(url: str) -> str:
    p = urlparse(url)
    scheme = p.scheme.lower()
    netloc = p.netloc.lower()
    if (scheme == "http" and netloc.endswith(":80")) or \
       (scheme == "https" and netloc.endswith(":443")):
        netloc = netloc.rsplit(":", 1)[0]
    path = p.path.rstrip("/") if p.path != "/" else "/"
    raw_params = parse_qs(p.query, keep_blank_values=True)
    cleaned = {}
    for k, vals in raw_params.items():
        kl = k.lower()
        kl = kl.lstrip("?")
        if kl not in TRACKING_PARAMS:
            cleaned[k] = vals
    sorted_query = urlencode(sorted(cleaned.items()), doseq=True) if cleaned else ""
    result = ParseResult(scheme, netloc, path, p.params, sorted_query, None).geturl()
    return result


def extract_domain(url: str) -> str:
    return urlparse(url).netloc.lower()


def is_binary_url(url: str) -> bool:
    path = urlparse(url).path.lower()
    _, ext = os.path.splitext(path)
    if ext in BINARY_EXTENSIONS:
        return True
    return False


def is_binary_mime(mime: str) -> bool:
    m = mime.lower().strip()
    for prefix in BINARY_MIME_PREFIXES:
        if m.startswith(prefix):
            return True
    return False


def is_soft_404(title: str, text: str, status: int) -> bool:
    if status != 200:
        return False
    head = text[:600]
    for pat in SOFT_404_PATTERNS:
        if pat.search(title) or pat.search(head):
            return True
    if len(text) < 50 and title == "":
        return True
    return False


@dataclass(order=True)
class PriorityItem:
    priority: float
    url: str = field(compare=False)
    depth: int = field(compare=False)


@dataclass
class PageResult:
    url: str
    normalized_url: str = ""
    status: int = 0
    depth: int = 0
    title: str = ""
    links: list = field(default_factory=list)
    text_length: int = 0
    content_hash: str = ""
    content_type: str = ""
    error: Optional[str] = None
    redirect_url: str = ""
    canonical_url: str = ""
    latency: float = 0.0
    bytes_fetched: int = 0
    is_soft_404: bool = False
    is_duplicate: bool = False


@dataclass
class CrawlConfig:
    max_concurrency: int = 10
    max_pages: int = 1000
    max_depth: int = 3
    request_timeout: int = 30
    delay: float = 0.05
    user_agent: str = (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/125.0.0.0 Safari/537.36"
    )
    same_domain: bool = True
    obey_robots_txt: bool = True
    use_playwright: bool = False
    detect_soft_404: bool = True
    html_dedup: bool = True
    follow_sitemap: bool = True
    max_retries: int = 3
    retry_base_delay: float = 1.0
    domain_default_limit: int = 5
    domain_limits: dict = field(default_factory=dict)
    storage_path: str = "crawl_data.db"
    export_csv: str = ""
    export_jsonl: str = ""
    resume: bool = False
    verbose: bool = False


class RobotsChecker:
    def __init__(self):
        self._cache: dict[str, Optional[RobotFileParser]] = {}
        self._lock = asyncio.Lock()

    async def check(self, session: aiohttp.ClientSession, url: str, user_agent: str) -> bool:
        p = urlparse(url)
        domain = f"{p.scheme}://{p.netloc}"
        async with self._lock:
            if domain not in self._cache:
                parser = RobotFileParser()
                try:
                    timeout = ClientTimeout(total=8)
                    robots_url = urljoin(domain, "/robots.txt")
                    async with session.get(robots_url, timeout=timeout) as resp:
                        if resp.status == 200:
                            body = await resp.text(errors="replace")
                            parser.parse(body.splitlines())
                        else:
                            parser.allow_all = True
                except Exception:
                    parser.allow_all = True
                self._cache[domain] = parser
        return self._cache[domain].can_fetch(user_agent, url) if self._cache[domain] else True


class DomainSemaphoreManager:
    def __init__(self, default_limit: int = 5):
        self._sems: dict[str, asyncio.Semaphore] = {}
        self._limits: dict[str, int] = {}
        self.default_limit = default_limit

    def set_limit(self, domain: str, limit: int):
        self._limits[domain] = limit
        if domain in self._sems:
            self._sems[domain] = asyncio.Semaphore(limit)

    def get(self, domain: str) -> asyncio.Semaphore:
        if domain not in self._sems:
            limit = self._limits.get(domain, self.default_limit)
            self._sems[domain] = asyncio.Semaphore(limit)
        return self._sems[domain]


@dataclass
class CrawlStats:
    pages_fetched: int = 0
    pages_ok: int = 0
    pages_error: int = 0
    timeout_count: int = 0
    status_404: int = 0
    status_500: int = 0
    redirects: int = 0
    blocked_robots: int = 0
    duplicates_skipped: int = 0
    duplicates_html: int = 0
    soft_404_count: int = 0
    total_bytes: int = 0
    total_latency: float = 0.0
    depth_histogram: dict = field(default_factory=lambda: defaultdict(int))
    start_time: float = 0.0
    queue_peak: int = 0

    @property
    def avg_latency(self) -> float:
        return self.total_latency / max(self.pages_fetched, 1)

    @property
    def pages_per_sec(self) -> float:
        elapsed = time.time() - self.start_time
        return self.pages_fetched / max(elapsed, 0.01)

    @property
    def success_rate(self) -> float:
        return (self.pages_ok / max(self.pages_fetched, 1)) * 100


class Storage:
    def __init__(self, db_path: str):
        self.db_path = db_path
        self.conn: Optional[sqlite3.Connection] = None

    async def open(self):
        self.conn = self._init_db()
        return self

    def _init_db(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.db_path, check_same_thread=False)
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA synchronous=OFF")
        conn.execute("""
            CREATE TABLE IF NOT EXISTS pages (
                url TEXT PRIMARY KEY,
                normalized_url TEXT,
                status INTEGER,
                depth INTEGER,
                title TEXT,
                content_hash TEXT,
                content_length INTEGER,
                links_found INTEGER,
                error TEXT,
                redirect_url TEXT,
                canonical_url TEXT,
                content_type TEXT,
                is_soft_404 INTEGER DEFAULT 0,
                fetched_at TEXT
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS queue (
                url TEXT PRIMARY KEY,
                depth INTEGER,
                priority REAL
            )
        """)
        conn.execute("""
            CREATE INDEX IF NOT EXISTS idx_pages_hash ON pages(content_hash)
        """)
        conn.execute("""
            CREATE INDEX IF NOT EXISTS idx_pages_norm ON pages(normalized_url)
        """)
        conn.commit()
        return conn

    async def save_page(self, result: PageResult):
        if self.conn is None:
            return
        await asyncio.to_thread(self._save_page, result)

    def _save_page(self, result: PageResult):
        self.conn.execute("""
            INSERT OR REPLACE INTO pages
                (url, normalized_url, status, depth, title, content_hash,
                 content_length, links_found, error, redirect_url,
                 canonical_url, content_type, is_soft_404, fetched_at)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        """, (
            result.url, result.normalized_url, result.status, result.depth,
            result.title, result.content_hash, result.text_length,
            len(result.links), result.error, result.redirect_url,
            result.canonical_url, result.content_type,
            1 if result.is_soft_404 else 0,
            datetime.now(timezone.utc).isoformat(),
        ))
        self.conn.commit()

    async def save_queue(self, items: list):
        if self.conn is None:
            return
        await asyncio.to_thread(self._save_queue, items)

    def _save_queue(self, items: list):
        self.conn.execute("DELETE FROM queue")
        if items:
            self.conn.executemany(
                "INSERT OR REPLACE INTO queue (url, depth, priority) VALUES (?,?,?)",
                items,
            )
        self.conn.commit()

    async def load_queue(self) -> list[tuple]:
        if self.conn is None:
            return []
        return await asyncio.to_thread(self._load_queue)

    def _load_queue(self) -> list[tuple]:
        rows = self.conn.execute(
            "SELECT url, depth FROM queue ORDER BY priority ASC"
        ).fetchall()
        self.conn.execute("DELETE FROM queue")
        self.conn.commit()
        return [(r[0], r[1]) for r in rows]

    async def load_visited_hashes(self) -> set[str]:
        if self.conn is None:
            return set()
        return await asyncio.to_thread(self._load_visited_hashes)

    def _load_visited_hashes(self) -> set[str]:
        rows = self.conn.execute(
            "SELECT content_hash FROM pages WHERE content_hash IS NOT NULL AND content_hash != ''"
        ).fetchall()
        return {r[0] for r in rows}

    async def load_visited_urls(self) -> set[str]:
        if self.conn is None:
            return set()
        return await asyncio.to_thread(self._load_visited_urls)

    def _load_visited_urls(self) -> set[str]:
        rows = self.conn.execute("SELECT normalized_url FROM pages").fetchall()
        return {r[0] for r in rows}

    async def export_csv(self, path: str):
        if self.conn is None:
            return
        await asyncio.to_thread(self._export_csv, path)

    def _export_csv(self, path: str):
        rows = self.conn.execute("SELECT * FROM pages ORDER BY fetched_at").fetchall()
        cols = [d[1] for d in self.conn.execute("PRAGMA table_info(pages)").fetchall()]
        with open(path, "w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow(cols)
            w.writerows(rows)
        log.info("exported CSV: %s (%d rows)", path, len(rows))

    async def export_jsonl(self, path: str):
        if self.conn is None:
            return
        await asyncio.to_thread(self._export_jsonl, path)

    def _export_jsonl(self, path: str):
        rows = self.conn.execute("SELECT * FROM pages ORDER BY fetched_at").fetchall()
        cols = [d[1] for d in self.conn.execute("PRAGMA table_info(pages)").fetchall()]
        with open(path, "w", encoding="utf-8") as f:
            for row in rows:
                f.write(json.dumps(dict(zip(cols, row)), ensure_ascii=False, default=str) + "\n")
        log.info("exported JSONL: %s (%d rows)", path, len(rows))

    async def close(self):
        if self.conn:
            self.conn.close()


async def fetch_sitemap_urls(session: aiohttp.ClientSession, base_url: str) -> list[str]:
    p = urlparse(base_url)
    domain = f"{p.scheme}://{p.netloc}"
    candidates = []
    timeout = ClientTimeout(total=8)
    try:
        async with session.get(urljoin(domain, "/robots.txt"), timeout=timeout) as resp:
            if resp.status == 200:
                body = await resp.text(errors="replace")
                for line in body.splitlines():
                    m = re.match(r"(?i)^sitemap:\s*(\S+)", line.strip())
                    if m:
                        candidates.append(m.group(1))
    except Exception:
        pass

    candidates += [
        urljoin(domain, "/sitemap.xml"),
        urljoin(domain, "/sitemap_index.xml"),
    ]

    found_urls = []
    seen = set()
    for sitemap_url in candidates:
        if sitemap_url in seen:
            continue
        seen.add(sitemap_url)
        try:
            async with session.get(sitemap_url, timeout=timeout) as resp:
                if resp.status != 200:
                    continue
                body = await resp.text(errors="replace")
                soup = BeautifulSoup(body, "xml")
                sitemaps = soup.find_all("sitemap")
                if sitemaps:
                    for s in sitemaps:
                        loc = s.find("loc")
                        if loc:
                            found_urls.append(loc.get_text(strip=True))
                else:
                    for loc in soup.find_all("loc"):
                        found_urls.append(loc.get_text(strip=True))
                if found_urls:
                    log.info("sitemap %s found %d URLs", sitemap_url, len(found_urls))
                    break
        except Exception:
            continue
    return found_urls


@dataclass
class FetchResult:
    status: int
    content_type: str
    body: Optional[str]
    real_url: str
    headers: dict = field(default_factory=dict)


async def fetch_with_retry(
    session: aiohttp.ClientSession,
    url: str,
    timeout_sec: int = 30,
    max_retries: int = 3,
    base_delay: float = 1.0,
) -> FetchResult:
    last_exc = None
    for attempt in range(max_retries + 1):
        try:
            to = ClientTimeout(total=timeout_sec)
            async with session.get(url, timeout=to) as resp:
                ct = resp.content_type or ""
                body = None
                if resp.status == 200 and ("text/html" in ct or "application/xhtml" in ct):
                    body = await resp.text(encoding="utf-8", errors="replace")
                return FetchResult(
                    status=resp.status,
                    content_type=ct,
                    body=body,
                    real_url=str(resp.url),
                    headers=dict(resp.headers),
                )
        except (asyncio.TimeoutError, aiohttp.ClientError) as exc:
            last_exc = exc
            if attempt < max_retries:
                delay = base_delay * (2 ** attempt)
                await asyncio.sleep(delay)
            else:
                raise
    raise last_exc


def calculate_priority(url: str, depth: int) -> float:
    p = urlparse(url)
    path = p.path.rstrip("/")
    segments = len([s for s in path.split("/") if s]) if path else 0
    is_root = 0.0 if path in ("", "/") else 0.5
    return depth + (segments / 100.0) + is_root


class Crawler:
    def __init__(self, config: CrawlConfig):
        self.config = config
        self.queue: asyncio.PriorityQueue = asyncio.PriorityQueue()
        self.results: list[PageResult] = []
        self.stats = CrawlStats()
        self.stats.start_time = time.time()
        self.domain_sems = DomainSemaphoreManager(config.domain_default_limit)
        self.robots_checker = RobotsChecker()
        self.storage: Optional[Storage] = None
        self.seen_urls: set[str] = set()
        self.seen_hashes: set[str] = set()
        self.redirect_map: dict[str, str] = {}
        self._shutdown = False
        self._pending = 0
        self._save_interval = 50
        self._last_save = 0
        self._pw_browser = None
        self._pw_context = None

        for domain, limit in config.domain_limits.items():
            self.domain_sems.set_limit(domain, limit)

        if config.verbose:
            log.setLevel(logging.INFO)

    async def _log(self, msg: str):
        if self.config.verbose:
            log.info(msg)

    async def run(self, start_urls: list[str]):
        self.storage = await Storage(self.config.storage_path).open()

        if self.config.resume:
            self.seen_urls = await self.storage.load_visited_urls()
            self.seen_hashes = await self.storage.load_visited_hashes()
            saved = await self.storage.load_queue()
            log.info("resumed: %d visited, %d in queue", len(self.seen_urls), len(saved))
            for url, depth in saved:
                norm = normalize_url(url)
                if norm not in self.seen_urls:
                    self.seen_urls.add(norm)
                    priority = calculate_priority(url, depth)
                    await self.queue.put(PriorityItem(priority, url, depth))
                    self._pending += 1

        connector = TCPConnector(
            limit=100,
            ttl_dns_cache=300,
            force_close=False,
        )

        async with aiohttp.ClientSession(connector=connector) as session:
            if self.config.use_playwright and HAS_PLAYWRIGHT:
                pw = await async_playwright().start()
                self._pw_browser = await pw.chromium.launch(headless=True)

            if not self.config.resume:
                if self.config.follow_sitemap:
                    tasks = []
                    for url in start_urls:
                        tasks.append(fetch_sitemap_urls(session, url))
                    sitemap_results = await asyncio.gather(*tasks, return_exceptions=True)
                    for urls in sitemap_results:
                        if isinstance(urls, list):
                            for su in urls:
                                norm = normalize_url(su)
                                if norm not in self.seen_urls and not is_binary_url(su):
                                    self.seen_urls.add(norm)
                                    prio = calculate_priority(su, 0)
                                    await self.queue.put(PriorityItem(prio, su, 0))
                                    self._pending += 1

                for url in start_urls:
                    norm = normalize_url(url)
                    if norm not in self.seen_urls:
                        self.seen_urls.add(norm)
                        prio = calculate_priority(url, 0)
                        await self.queue.put(PriorityItem(prio, norm, 0))
                        self._pending += 1

            workers = [
                asyncio.create_task(self._worker(session))
                for _ in range(self.config.max_concurrency)
            ]

            status_task = asyncio.create_task(self._status_reporter())

            try:
                while not self._shutdown:
                    if len(self.results) >= self.config.max_pages:
                        break
                    if self._pending <= 0:
                        await asyncio.sleep(0.5)
                        if self._pending <= 0:
                            break
                    await asyncio.sleep(0.1)

                    if self._pending > self.stats.queue_peak:
                        self.stats.queue_peak = self._pending
            finally:
                self._shutdown = True

            await asyncio.gather(*workers, return_exceptions=True)
            status_task.cancel()
            try:
                await status_task
            except asyncio.CancelledError:
                pass

            if self._pw_browser:
                await self._pw_browser.close()
                await pw.stop()

            await self._save_state()

            if self.config.export_csv:
                await self.storage.export_csv(self.config.export_csv)
            if self.config.export_jsonl:
                await self.storage.export_jsonl(self.config.export_jsonl)

        await self.storage.close()

    async def _save_state(self):
        if self.storage is None:
            return
        q_items = []
        for item in list(self.queue._queue): 
            if hasattr(item, "url"):
                q_items.append((item.url, item.depth, item.priority))
        await self.storage.save_queue(q_items)

    async def _worker(self, session: aiohttp.ClientSession):
        while not self._shutdown:
            if len(self.results) >= self.config.max_pages:
                break
            try:
                item = await asyncio.wait_for(self.queue.get(), timeout=0.5)
            except asyncio.TimeoutError:
                continue

            try:
                self._pending -= 1
                domain = extract_domain(item.url)

                if self.config.obey_robots_txt:
                    allowed = await self.robots_checker.check(
                        session, item.url, self.config.user_agent
                    )
                    if not allowed:
                        self.stats.blocked_robots += 1
                        self.stats.pages_fetched += 1
                        result = PageResult(
                            url=item.url,
                            normalized_url=normalize_url(item.url),
                            depth=item.depth,
                            error="robots",
                        )
                        self.results.append(result)
                        if self.storage:
                            await self.storage.save_page(result)
                        self.queue.task_done()
                        continue

                async with self.domain_sems.get(domain):
                    result = await self._fetch(session, item.url, item.depth)

                self.results.append(result)
                self.stats.pages_fetched += 1

                if result.error:
                    self.stats.pages_error += 1
                    if result.error == "timeout":
                        self.stats.timeout_count += 1
                else:
                    self.stats.pages_ok += 1

                if result.status == 404:
                    self.stats.status_404 += 1
                elif result.status >= 500:
                    self.stats.status_500 += 1
                elif 300 <= result.status < 400:
                    self.stats.redirects += 1

                if result.is_soft_404:
                    self.stats.soft_404_count += 1
                if result.is_duplicate:
                    self.stats.duplicates_html += 1

                self.stats.total_latency += result.latency
                self.stats.total_bytes += result.bytes_fetched
                self.stats.depth_histogram[result.depth] += 1

                if self.storage:
                    await self.storage.save_page(result)

                if (
                    not result.error
                    and result.status == 200
                    and item.depth < self.config.max_depth
                    and not result.is_duplicate
                ):
                    added = 0
                    for link in result.links:
                        if self._shutdown:
                            break
                        if len(self.results) + self._pending >= self.config.max_pages * 2:
                            break
                        norm = normalize_url(link)
                        if norm in self.seen_urls:
                            continue
                        if is_binary_url(norm):
                            continue
                        self.seen_urls.add(norm)
                        new_depth = item.depth + 1
                        prio = calculate_priority(norm, new_depth)
                        await self.queue.put(PriorityItem(prio, norm, new_depth))
                        self._pending += 1
                        added += 1

                self.queue.task_done()

                pages_done = len(self.results)
                if pages_done - self._last_save >= self._save_interval:
                    self._last_save = pages_done
                    await self._save_state()

                if self.config.delay > 0:
                    await asyncio.sleep(self.config.delay)

            except asyncio.CancelledError:
                self.queue.task_done()
                raise
            except Exception:
                self.queue.task_done()

    async def _fetch(
        self,
        session: aiohttp.ClientSession,
        url: str,
        depth: int,
    ) -> PageResult:
        result = PageResult(url=url, normalized_url=normalize_url(url), depth=depth)
        t0 = time.time()

        try:
            if self.config.use_playwright and HAS_PLAYWRIGHT and self._pw_browser:
                result = await self._fetch_playwright(url, depth)
                result.latency = time.time() - t0
                return result

            fr = await fetch_with_retry(
                session,
                url,
                timeout_sec=self.config.request_timeout,
                max_retries=self.config.max_retries,
                base_delay=self.config.retry_base_delay,
            )

            result.status = fr.status
            result.redirect_url = fr.real_url
            result.content_type = fr.content_type
            body = fr.body

            ct = fr.content_type.lower()

            if is_binary_mime(ct):
                result.error = "binary"
                result.latency = time.time() - t0
                return result

            if fr.status == 200 and ("text/html" in ct or "application/xhtml" in ct) and fr.body is not None:
                body = fr.body
                result.bytes_fetched = len(body.encode("utf-8"))

                if self.config.html_dedup:
                    h = hashlib.sha256(body.encode("utf-8")).hexdigest()
                    result.content_hash = h
                    if h in self.seen_hashes:
                        result.is_duplicate = True
                        result.latency = time.time() - t0
                        return result
                    self.seen_hashes.add(h)

                title, links, text_len, canonical = self._parse(body, fr.real_url)
                result.title = title
                result.links = links
                result.text_length = text_len
                result.canonical_url = canonical

                if self.config.detect_soft_404:
                    result.is_soft_404 = is_soft_404(title, body, 200)

        except asyncio.TimeoutError:
            result.error = "timeout"
        except aiohttp.ClientError as e:
            result.error = str(e)[:80]
        except Exception as e:
            result.error = str(e)[:80]

        result.latency = time.time() - t0
        return result

    async def _fetch_playwright(self, url: str, depth: int) -> PageResult:
        result = PageResult(url=url, normalized_url=normalize_url(url), depth=depth)
        try:
            page = await self._pw_browser.new_page()
            await page.set_extra_http_headers({"User-Agent": self.config.user_agent})
            response = await page.goto(url, wait_until="networkidle", timeout=self.config.request_timeout * 1000)
            if response:
                result.status = response.status
                result.content_type = (response.headers.get("content-type") or "")
            result.redirect_url = page.url

            ct = result.content_type.lower()
            if is_binary_mime(ct):
                result.error = "binary"
                await page.close()
                return result

            body = await page.content()
            result.bytes_fetched = len(body.encode("utf-8"))

            if self.config.html_dedup:
                h = hashlib.sha256(body.encode("utf-8")).hexdigest()
                result.content_hash = h
                if h in self.seen_hashes:
                    result.is_duplicate = True
                    await page.close()
                    return result
                self.seen_hashes.add(h)

            title, links, text_len, canonical = self._parse(body, url)
            result.title = title
            result.links = links
            result.text_length = text_len
            result.canonical_url = canonical

            if self.config.detect_soft_404:
                result.is_soft_404 = is_soft_404(title, body, result.status)

            await page.close()
        except Exception as e:
            result.error = str(e)[:80]
        return result

    def _parse(self, html: str, base_url: str) -> tuple:
        soup = BeautifulSoup(html, "html.parser")
        title = (soup.find("title").get_text(strip=True) if soup.find("title") else "")

        canonical = ""
        canon_tag = soup.find("link", rel="canonical")
        if canon_tag and canon_tag.get("href"):
            canonical = urljoin(base_url, canon_tag["href"])

        links = []
        base_netloc = urlparse(base_url).netloc.lower()
        for a in soup.find_all("a", href=True):
            href = a["href"].strip()
            if not href or href.startswith(("#", "javascript:", "mailto:", "tel:")):
                continue
            abs_url = urljoin(base_url, href)
            p = urlparse(abs_url)
            if p.scheme not in ("http", "https"):
                continue
            if is_binary_url(abs_url):
                continue
            if self.config.same_domain and p.netloc.lower() != base_netloc:
                continue
            links.append(p._replace(fragment="").geturl())

        text_len = len(soup.get_text(separator=" ", strip=True))
        return title, links, text_len, canonical

    async def _status_reporter(self):
        while not self._shutdown:
            elapsed = time.time() - self.stats.start_time
            qs = self.queue.qsize()
            line = (
                f"  {len(self.results):,}/{self.config.max_pages} pages  "
                f"OK:{self.stats.pages_ok}  "
                f"ERR:{self.stats.pages_error}  "
                f"404:{self.stats.status_404}  "
                f"Dup:{self.stats.duplicates_html}  "
                f"Rate:{self.stats.pages_per_sec:.1f}/s  "
                f"Avg:{self.stats.avg_latency*1000:.0f}ms  "
                f"Queue:{qs}  "
                f"Depth:{max(self.stats.depth_histogram.keys(), default=0)}  "
                f"{elapsed:.0f}s  "
            )
            sys.stdout.write("\r" + " " * console.width + "\r")
            console.print(f"[cyan]>[/] {line}", end="\r")
            sys.stdout.flush()
            await asyncio.sleep(1)


def results_output(results: list[PageResult], stats: CrawlStats, elapsed: float):
    if not results:
        console.print("[yellow]No results.[/]")
        return

    ok = stats.pages_ok
    err = stats.pages_error
    timeout_c = stats.timeout_count
    blocked = stats.blocked_robots
    soft404 = stats.soft_404_count
    dups = stats.duplicates_html

    console.print()
    summary = (
        f"[bold cyan]Crawl complete[/]  "
        f"OK:[green]{ok}[/]  "
        f"ERR:[red]{err}[/]  "
        f"TIMEOUT:[yellow]{timeout_c}[/]  "
        f"BLOCKED:[magenta]{blocked}[/]  "
        f"SOFT404:[orange1]{soft404}[/]  "
        f"DUPS:[dim]{dups}[/]"
    )
    console.print(summary)
    console.print(
        f"  Rate: [bold]{stats.pages_per_sec:.1f}[/] pages/s  "
        f"Avg: [bold]{stats.avg_latency*1000:.0f}[/]ms  "
        f"Total: [bold]{stats.total_bytes/1024/1024:.1f}[/]MB  "
        f"Queue peak: {stats.queue_peak}"
    )
    console.print()

    table = Table(border_style="cyan", box=box.SIMPLE)
    table.add_column("Status", style="bold", width=9)
    table.add_column("URL", width=80)
    table.add_column("Title", style="dim", width=30)
    table.add_column("Links", justify="right", width=5)

    for r in results[:40]:
        if r.error == "timeout":
            status = "[yellow]TIMEOUT[/]"
        elif r.error == "robots":
            status = "[magenta]BLOCKED[/]"
        elif r.error == "binary":
            status = "[blue]BINARY[/]"
        elif r.error:
            status = f"[red]ERR[/]"
        elif r.is_soft_404:
            status = "[orange1]SOFT404[/]"
        elif r.is_duplicate:
            status = "[dim]DUP[/]"
        else:
            status = f"[green]{r.status}[/]"
        table.add_row(
            status,
            r.url[:80],
            r.title[:30] if r.title else "",
            str(len(r.links)),
        )

    if len(results) > 40:
        table.add_row("...", f"+{len(results)-40} more", "", "", "")

    console.print(table)


async def main():
    if len(sys.argv) < 2:
        console.print("[bold red]Usage:[/] python main.py <start-url> [options]")
        console.print()
        console.print("[bold]Options:[/]")
        console.print("  max-pages    [dim]default: 200[/]")
        console.print("  max-depth    [dim]default: 3[/]")
        console.print("  --resume     [dim]resume from database[/]")
        console.print("  --playwright [dim]enable JS rendering[/]")
        console.print("  --verbose    [dim]verbose logging[/]")
        console.print("  --csv FILE   [dim]export to CSV[/]")
        console.print("  --jsonl FILE [dim]export to JSONL[/]")
        console.print("  --db FILE    [dim]database path (default: crawl_data.db)[/]")
        console.print()
        console.print("[dim]Example: python main.py https://example.com 500 3 --playwright --csv out.csv[/]")
        sys.exit(1)

    url = sys.argv[1]
    args = sys.argv[2:]

    max_pages = 200
    max_depth = 3
    resume = False
    playwright = False
    verbose = False
    csv_path = ""
    jsonl_path = ""
    db_path = "crawl_data.db"

    i = 0
    while i < len(args):
        if args[i] == "--resume":
            resume = True
        elif args[i] == "--playwright":
            playwright = True
        elif args[i] == "--verbose":
            verbose = True
        elif args[i] == "--csv" and i + 1 < len(args):
            csv_path = args[i + 1]
            i += 1
        elif args[i] == "--jsonl" and i + 1 < len(args):
            jsonl_path = args[i + 1]
            i += 1
        elif args[i] == "--db" and i + 1 < len(args):
            db_path = args[i + 1]
            i += 1
        elif args[i].isdigit():
            if max_pages == 200:
                max_pages = int(args[i])
            else:
                max_depth = int(args[i])
        i += 1

    config = CrawlConfig(
        max_pages=max_pages,
        max_depth=max_depth,
        resume=resume,
        use_playwright=playwright,
        verbose=verbose,
        storage_path=db_path,
        export_csv=csv_path,
        export_jsonl=jsonl_path,
    )

    crawler = Crawler(config)
    t0 = time.time()

    console.print(f"[bold cyan]Starting crawl[/] {url}")
    console.print(
        f"  pages={max_pages} depth={max_depth} "
        f"workers={config.max_concurrency} "
        + ("playwright=on " if playwright else "")
        + ("resume=on " if resume else "")
        + ("verbose=on " if verbose else "")
    )
    console.print()

    crawl_task = asyncio.create_task(crawler.run([url]))

    from rich.progress import Progress, SpinnerColumn, TextColumn

    with Progress(
        SpinnerColumn(),
        TextColumn("[progress.description]{task.description}"),
        TextColumn("[bold]{task.completed}/{task.total}"),
        transient=True,
    ) as progress:
        task = progress.add_task(f"[cyan]Crawling...", total=max_pages)
        while not crawl_task.done():
            progress.update(task, completed=len(crawler.results))
            await asyncio.sleep(0.1)
        progress.update(task, completed=len(crawler.results))

    await crawl_task
    elapsed = time.time() - t0

    results_output(crawler.results, crawler.stats, elapsed)
    console.print(f"\n[dim]Done in {elapsed:.1f}s[/]")


if __name__ == "__main__":
    if sys.platform == "win32":
        asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())
    asyncio.run(main())
