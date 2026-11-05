#!/usr/bin/env python3
"""Low-priority, bounded 72 free-main forward sign check; never controls another process."""
import hashlib
import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
sys.path.insert(0, str(Path(__file__).resolve().parent))
from missing_child import finished_or_raise

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent
SOURCE = HERE.parent/'rational-carrier64-cleared-pair/ClearedCurrentPair.lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
DIRECT = {
 'ClearedCurrentIPRA': ('/tmp/rational-carrier64-cleared-ipra-priority-check01/ClearedCurrentIPRA.olean', 'd895d103bb0a8b888c205c4c7c33bbcdf8a9bbcd735c687475dc6fd96175b1f5'),
 'RationalCarrier64CurrentPair': ('/tmp/rational-carrier64-current14-pair-priority-check02/RationalCarrier64CurrentPair.olean', 'da0337c6058b21c5ae5b31eed1fa4e3d69cfe3c02eb2fce469b5bae384fd4dc3'),
 'DiophantineConsistency/CurrentEquationSyntax2011': ('/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/CurrentEquationSyntax2011.olean', '28e2a026978eb60c2fb0ef494b1c7256a1b1aa354ac4ee9f3688a9433d48daae'),
 'DiophantineConsistency/CurrentKernelData2011': ('/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/CurrentKernelData2011.olean', '95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896'),
}
OUT = Path('/tmp/rational-carrier64-cleared-pair-replay-priority-check01')
LEAN_PATH = '/tmp/rational-carrier64-cleared-ipra-priority-check01:/tmp/rational-carrier64-current14-pair-priority-check02:/tmp/rational-carrier64-current14-actual-external-priority-check01:/tmp/rational-carrier64-current14-beta-priority-check01:/tmp/rational-carrier64-current14-specialization-priority-check01:/tmp/rational-carrier64-current14-base-priority-check04:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
EXPECTED = {
 '/tmp/rational-carrier64-cleared-pair-priority-check01/ClearedCurrentPair.olean': '6f8afbccd823e06ce3173999dcedab7828abb573d04e7855fa40583298584cdb',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/rational-carrier64-cleared-pair/observations/attempt01/compile.log': '9b295efdef720cee846b4f420067ae5e4ccfedbf224b67d5bf817ebbbd9e9087',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/rational-carrier64-cleared-pair/observations/attempt01/result.json': 'de1c08b733e08df60462a56f1a3640187106f3400c00654f9b5d198a4ed5e602',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/rational-carrier64-cleared-pair/observations/attempt01/outer-terminal.json': '86b0b1817754f554c1818a5a15e21ae9722238f7c8f7e81f56c0b57d606a5807',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/rational-carrier64-cleared-pair/ClearedCurrentPair.lean': 'fb35fe4a8c8bfa1995265109485853a7b906728a9e1e87140d096b415be2f079',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/rational-carrier64-cleared-ipra/observations/attempt01/result.json': '57e8509112bf368c21425ab22c4611a269f506a92da7ec9c3e656b3f4e630d8b',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/rational-carrier64-cleared-ipra/observations/attempt01/outer-terminal.json': 'fbaa7de6b563da8cca95bc219d69e3cf41a6fbb7e1fb0ad5b78a0cb24f6c1126',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/rational-carrier64-current14-pair/observations/attempt02/result.json': '0e3cccd62ef35352f9ccbe00639947f580ec5b1a2adeb05561a58a263a945593',
 '/tmp/current14-standard-fresh-build-20261104/state.json': 'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014',
 '/tmp/current14-standard-fresh-source-20261104/src/DiophantineConsistency/CurrentEquationSyntax2011.lean': '112c21a16ddb3d45b311dbe9099ea89619ff6b25f6fb61050d9a7b8f8898d2f9',
 '/tmp/current14-standard-fresh-source-20261104/src/DiophantineConsistency/CurrentKernelData2011.lean': '529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c',
 str(LEAN): 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 **{path:sha for path,sha in DIRECT.values()}}
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash')
RSS_LIMIT = 7*1024**3//2
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
    for module, (path, expected) in DIRECT.items():
        root = str(Path(path[:-(len(module)+len('.olean'))]))
        search = LEAN_PATH.split(':')
        if root not in search: raise RuntimeError('provider outside search path')
        for suffix in SUFFIXES:
            obj = Path(path[:-6]+suffix)
            if os.path.lexists(obj):
                if not obj.is_file(): raise RuntimeError('invalid companion '+str(obj))
                result[str(obj)] = {'realpath':str(obj.resolve()),'sha256':sha(obj)}
            else: result[str(obj)] = None
            for earlier in search[:search.index(root)]:
                shadow = Path(earlier)/(module+suffix)
                if os.path.lexists(shadow): raise RuntimeError('direct shadow '+str(shadow))
                result[str(shadow)] = None
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


def group_rss(group):
    """Sample summed process RSS for this process group; fail closed on unreadable members."""
    total = 0
    members = []
    for proc in Path('/proc').iterdir():
        if not proc.name.isdigit():
            continue
        try:
            stat = (proc/'stat').read_text().rsplit(')', 1)[1].split()
            if int(stat[2]) != group or stat[0] == 'Z':
                continue
            values = (proc/'status').read_text().splitlines()
            rss = [int(line.split()[1]) for line in values if line.startswith('VmRSS:')]
            if len(rss) != 1:
                raise RuntimeError('group member RSS unavailable: '+proc.name)
            total += rss[0]*1024
            members.append(int(proc.name))
        except (FileNotFoundError, ProcessLookupError):
            continue
    return total, members


if OUT.exists():
    raise SystemExit('refusing existing output')
before = guards()
runner_before = sha(__file__)
helper_before = sha(HERE/'missing_child.py')
if available() < MIN_AVAILABLE:
    raise SystemExit('MemAvailable below 10 GiB before launch')
if other_lean():
    raise SystemExit('another non-base Lean process is active')
OUT.mkdir()
obj = OUT/'ClearedCurrentPair.olean'
log = OUT/'compile.log'
cmd = ['/usr/bin/ionice', '-c', '3', str(LEAN), '-M2800', '-j1', '-DElab.async=false',
       '--root='+str(SOURCE.parent), str(SOURCE), '-o', str(obj)]
env = dict(os.environ, LEAN_PATH=LEAN_PATH, LEAN_NUM_THREADS='1')
for key in ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'):
    env.pop(key, None)


def child_setup():
    os.setsid()
    os.nice(19)


start = time.monotonic()
minimum = available()
peak_group_rss = 0
samples = 0
reason = None
with log.open('x') as stream:
    proc = subprocess.Popen(cmd, env=env, stdout=stream, stderr=subprocess.STDOUT,
                            preexec_fn=child_setup)
    while proc.poll() is None:
        current = available()
        minimum = min(minimum, current)
        try:
            rss, members = group_rss(proc.pid)
            if proc.pid not in members:
                finished_or_raise(proc)
                if members:
                    raise RuntimeError('child exited while process-group members remain')
                break
            peak_group_rss = max(peak_group_rss, rss)
            samples += 1
            extra = [pid for pid in other_lean() if pid != proc.pid]
            if current < MIN_AVAILABLE:
                reason = 'MemAvailable below 10 GiB'
            elif rss >= RSS_LIMIT:
                reason = 'sampled process-group RSS reached 3.5 GiB'
            elif time.monotonic()-start >= TIMEOUT:
                reason = '120-second timeout'
            elif extra:
                reason = 'another non-base Lean process appeared: '+repr(extra)
        except Exception as exc:
            reason = 'RSS/process monitor failure: '+repr(exc)
        if reason:
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
            break
        time.sleep(0.25)
    code = proc.wait()

# Do not accept an exited leader if any process from its group remains alive.
try:
    _, remaining = group_rss(proc.pid)
    if remaining:
        reason = 'process-group members remain after leader exit: '+repr(remaining)
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
except Exception as exc:
    reason = 'final group monitor failure: '+repr(exc)

after = guards()
text = log.read_text()
stable = (before == after and runner_before == sha(__file__) and
          helper_before == sha(HERE/'missing_child.py'))
expected_reports = ["'DiophantineConsistency.ClearedCurrentPair.external_and_cleared_ipra' depends on axioms:"]
passed = (code == 0 and reason is None and samples > 0 and stable and obj.is_file() and not obj.is_symlink()
          and all(line in text for line in expected_reports) and not any(x in text for x in ('warning:', 'error:', 'sorryAx'))
          and sha(obj) == '6f8afbccd823e06ce3173999dcedab7828abb573d04e7855fa40583298584cdb'
          and sha(log) == '9b295efdef720cee846b4f420067ae5e4ccfedbf224b67d5bf817ebbbd9e9087')
result = {
    'status': 'PASS' if passed else 'FAILED', 'exit': code, 'stop_reason': reason,
    'seconds': round(time.monotonic()-start, 3), 'command': cmd, 'lean_path': LEAN_PATH,
    'sampled_group_rss_limit_bytes': RSS_LIMIT, 'lean_memory_mib': 2800, 'nice': 19,
    'io_class': 'idle', 'minimum_memavailable_bytes': minimum,
    'min_required_memavailable_bytes': MIN_AVAILABLE, 'sampled_peak_group_rss_bytes': peak_group_rss,
    'group_rss_samples': samples,
    'runner_sha256': runner_before, 'missing_child_helper_sha256': helper_before,
    'guards_before': before, 'guards_after': after, 'guards_stable': stable,
    'log_sha256': sha(log), 'object_sha256': sha(obj) if obj.is_file() else None,
    'scope': 'Same-source replay of external actual-port rational iff and cleared integer-language iPRA derivability; exact original object and log hash required; direct captured-provider guards; inherited transitive and dynamic ancestry.',
}
(OUT/'result.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
print(json.dumps(result, sort_keys=True))
if not passed:
    raise SystemExit(1)
