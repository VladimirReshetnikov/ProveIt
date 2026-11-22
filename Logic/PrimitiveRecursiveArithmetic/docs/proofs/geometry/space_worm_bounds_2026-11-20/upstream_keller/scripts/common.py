"""Shared file checks, resource limits and bounded Lean builds."""

from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from contextlib import contextmanager
import fcntl
from graphlib import TopologicalSorter
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


class Progress:
    """Print a stage's counts once per minute and at completion."""

    def __init__(self, stage, total, jobs):
        self.stage, self.total = stage, total
        self.started = self.last = time.monotonic()
        print(f"{stage}: 0/{total} complete; {jobs} workers.", flush=True)

    def update(self, completed):
        now = time.monotonic()
        if completed == self.total or now - self.last >= 60:
            print(
                f"{self.stage}: {completed}/{self.total} complete; "
                f"{(now - self.started) / 60:.1f} min elapsed.",
                flush=True,
            )
            self.last = now


def memory_budget():
    info = {
        key: int(value.split()[0]) * 1024
        for key, value in (
            line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines()
        )
    }
    return max(0, info["MemAvailable"] - min(info["MemTotal"] // 5, 24 * 2**30))


def worker_count(requested, cap, bytes_per_worker=0, reserve=0):
    """Requested jobs are maxima; reserve memory for the rest of the machine."""
    jobs = len(os.sched_getaffinity(0)) if requested is None else requested
    if type(jobs) is not int or jobs < 1:
        raise ValueError("jobs must be positive")
    jobs = min(jobs, cap, len(os.sched_getaffinity(0)))
    if bytes_per_worker:
        jobs = min(jobs, max(0, memory_budget() - reserve) // bytes_per_worker)
    if jobs < 1:
        raise ValueError("insufficient available memory for one worker")
    return jobs


def sha256_file(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as source:
        for block in iter(lambda: source.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def checked_hash(path, expected):
    actual = sha256_file(path)
    if actual != expected:
        raise ValueError(f"SHA256 mismatch: {path}")
    return actual


def certificate_file(directory, name):
    directory = Path(directory).resolve()
    if not isinstance(name, str) or not name or Path(name).name != name or name in (".", ".."):
        raise ValueError(f"invalid certificate filename: {name!r}")
    path = directory / name
    if path.resolve().parent != directory:
        raise ValueError(f"certificate file escapes directory: {name}")
    return path


def fingerprint(files):
    data = json.dumps(files, sort_keys=True, separators=(",", ":")).encode()
    return {"sha256": hashlib.sha256(data).hexdigest(), "files": files}


def file_snapshot(paths, base=ROOT):
    base = Path(base).resolve()
    return fingerprint(
        {str(Path(p).resolve().relative_to(base)): sha256_file(p) for p in sorted(paths)}
    )


def source_snapshot():
    paths = [
        ROOT / name
        for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "MoserWorm.lean")
    ]
    for root in (ROOT / "MoserWorm", ROOT / "scripts"):
        for parent, directories, files in os.walk(root):
            directories[:] = [
                d for d in directories if d not in ("Generated", ".lake", "__pycache__")
            ]
            paths.extend(
                Path(parent) / name
                for name in files
                if Path(name).suffix in (".lean", ".py", ".c", ".h", ".sh")
            )
    return file_snapshot(paths)


def atomic_text(path, text):
    path = Path(path)
    if path.is_file() and path.read_bytes() == text.encode():
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", dir=path.parent, prefix="." + path.name + ".", delete=False
        ) as output:
            temporary = Path(output.name)
            output.write(text)
        temporary.replace(path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def atomic_json(path, value):
    atomic_text(path, json.dumps(value, sort_keys=True, indent=2) + "\n")


@contextmanager
def directory_lock(directory):
    key = hashlib.sha256(str(Path(directory).resolve()).encode()).hexdigest()
    path = ROOT / ".lake/locks" / (key + ".lock")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a+") as lock:
        try:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise RuntimeError(f"another process holds {path}") from None
        yield


def run(stage, command, logs, *, announce=True):
    log = Path(logs) / f"{stage}.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    if announce:
        print(f"{stage}: {log}", flush=True)
    with log.open("w") as output:
        subprocess.run(
            command,
            cwd=ROOT,
            env={**os.environ, "LEAN_NUM_THREADS": "2"},
            stdout=output,
            stderr=subprocess.STDOUT,
            check=True,
        )


def build_modules(modules, jobs, logs):
    """Build a generated dependency graph with at most jobs Lean processes."""
    graph = {m["name"]: set(m["dependencies"]) for m in modules}
    if len(graph) != len(modules) or any(
        not dependencies <= graph.keys() for dependencies in graph.values()
    ):
        raise ValueError("invalid generated module graph")
    order = TopologicalSorter(graph)
    order.prepare()
    progress = Progress(f"{Path(logs).name.capitalize()} kernel checking", len(graph), jobs)
    completed = 0
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        ready, active = [], {}
        while order.is_active():
            ready.extend(order.get_ready())
            while ready and len(active) < jobs:
                name = ready.pop()
                active[pool.submit(run, name, ["lake", "build", name], logs, announce=False)] = name
            finished, _ = wait(active, timeout=1, return_when=FIRST_COMPLETED)
            for future in finished:
                future.result()
            order.done(*(active.pop(future) for future in finished))
            completed += len(finished)
            progress.update(completed)
