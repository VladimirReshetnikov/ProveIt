#!/usr/bin/env python3
"""Low-priority, bounded 76Y graph check; never controls another process."""
import hashlib
import json
import os
import resource
import signal
import subprocess
import sys
import time
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent
SOURCE = RESEARCH/'p64-qcube76-independent-y-candidate/P64QCube76Y.lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
GRAPH = Path('/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/Compact44/P64Graph.olean')
OUT = Path('/tmp/p64-qcube76y-priority-check01')
LEAN_PATH = '/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
EXPECTED = {
    str(SOURCE): '44486d50fa9867c167a111ee6bab23fc3fe7bc17f5ded2b9c1136e643f6de644',
    str(LEAN): 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
    str(GRAPH): '4be074aa56722e991b3c067e22a00d19e2b90b8ab97b0755cc606eecb0b2445c',
}
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash')
LIMIT = 2*1024**3
MIN_AVAILABLE = 10*1024**3
TIMEOUT = 120


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def available():
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):
            return int(line.split()[1])*1024
    raise RuntimeError('MemAvailable is unavailable')


def guards():
    result = {}
    for path, expected in EXPECTED.items():
        obj = Path(path)
        if not obj.is_file() or sha(obj) != expected:
            raise RuntimeError('pinned input changed: '+path)
        result[path] = {'realpath': str(obj.resolve()), 'sha256': expected}
    stem = str(GRAPH)[:-6]
    for suffix in SUFFIXES:
        p = Path(stem+suffix)
        if os.path.lexists(p):
            if not p.is_file():
                raise RuntimeError('invalid provider companion: '+str(p))
            result[str(p)] = {'realpath': str(p.resolve()), 'sha256': sha(p)}
        else:
            result[str(p)] = None
    return result


def other_lean():
    result = []
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit():
            continue
        try:
            if (proc/'comm').read_text().strip() != 'lean':
                continue
            stat = (proc/'stat').read_text().split()
            if stat[2] == 'Z':
                continue
            argv = (proc/'cmdline').read_bytes().replace(b'\0', b' ').decode(errors='replace')
            if '/tmp/current14-standard-fresh-source-20261104/src' not in argv:
                result.append(int(proc.name))
        except (FileNotFoundError, ProcessLookupError):
            continue
    return result


if OUT.exists():
    raise SystemExit('refusing existing output')
before = guards()
if available() < MIN_AVAILABLE:
    raise SystemExit('MemAvailable below 10 GiB before launch')
if other_lean():
    raise SystemExit('another non-base Lean process is active')
OUT.mkdir()
obj = OUT/'P64QCube76Y.olean'
log = OUT/'compile.log'
cmd = ['/usr/bin/ionice', '-c', '3', str(LEAN), '-M2048', '-j1', '-DElab.async=false',
       '--root='+str(SOURCE.parent), str(SOURCE), '-o', str(obj)]
env = dict(os.environ, LEAN_PATH=LEAN_PATH, LEAN_NUM_THREADS='1')
for key in ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'):
    env.pop(key, None)


def child_setup():
    os.setsid()
    os.nice(19)
    resource.setrlimit(resource.RLIMIT_AS, (LIMIT, LIMIT))


start = time.monotonic()
minimum = available()
peak_rss_kib = 0
reason = None
with log.open('x') as stream:
    proc = subprocess.Popen(cmd, env=env, stdout=stream, stderr=subprocess.STDOUT,
                            preexec_fn=child_setup)
    while proc.poll() is None:
        current = available()
        minimum = min(minimum, current)
        try:
            for line in Path(f'/proc/{proc.pid}/status').read_text().splitlines():
                if line.startswith('VmRSS:'):
                    peak_rss_kib = max(peak_rss_kib, int(line.split()[1]))
        except FileNotFoundError:
            pass
        extra = [pid for pid in other_lean() if pid != proc.pid]
        if current < MIN_AVAILABLE:
            reason = 'MemAvailable below 10 GiB'
        elif time.monotonic()-start >= TIMEOUT:
            reason = '120-second timeout'
        elif extra:
            reason = 'another non-base Lean process appeared: '+repr(extra)
        if reason:
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
            break
        time.sleep(0.25)
    code = proc.wait()

after = guards()
text = log.read_text()
stable = before == after
passed = code == 0 and reason is None and stable and obj.is_file() and not obj.is_symlink() and not text
result = {
    'status': 'PASS' if passed else 'FAILED', 'exit': code, 'stop_reason': reason,
    'seconds': round(time.monotonic()-start, 3), 'command': cmd, 'lean_path': LEAN_PATH,
    'address_space_limit_bytes': LIMIT, 'lean_memory_mib': 2048, 'nice': 19,
    'io_class': 'idle', 'minimum_memavailable_bytes': minimum,
    'min_required_memavailable_bytes': MIN_AVAILABLE, 'sampled_peak_rss_kib': peak_rss_kib,
    'guards_before': before, 'guards_after': after, 'guards_stable': stable,
    'log_sha256': sha(log), 'object_sha256': sha(obj) if obj.is_file() else None,
    'scope': 'Graph definition only; direct captured-provider guards; inherited transitive and dynamic ancestry.',
}
(OUT/'result.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
print(json.dumps(result, sort_keys=True))
if not passed:
    raise SystemExit(1)
