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
SOURCE = HERE/'Normalized106Rational66.lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
DIRECT = {
 'DiophantineConsistency/ModelCarrierSyntax': ('/tmp/nine-ipra-guarded-author-20261102-h/lib/DiophantineConsistency/ModelCarrierSyntax.olean', '9eaaefb9b4121df6d9c8f6f1c5feef1cc837fc38f51a831a005db072bdaaf900'),
}
OUT = Path('/tmp/normalized106-rational66-lean-priority-check03')
LEAN_PATH = '/tmp/nine-ipra-guarded-author-20261102-h/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
EXPECTED = {
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/normalized106-rational66-lean/Normalized106Rational66.lean': '99b0d71b27771ed5416e295f28f6d1668a4c5a7cdbf8a756a7ac19b513129f42',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/normalized106-rational66-lean/build_lean.py': '59976f3ec7825211ab45a0c72ab0224272a8b49f5a24a301a368e1f40c1f3a30',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/normalized106-rational66/polynomial.json': '61784a1cdc3594174c3e321712322cebdffff20be51ef7f2bc0feb3b8f9498a4',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/normalized106-rational66/result.json': '082d6634b57ed71f8c61a466a05a0dc09bf8577685a45747b4e4249ff259836a',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/rational-carrier64-lean-identity/RationalCarrier64.lean': '8676e328432ca3fd070dbd4abe6ae097137138aff4b2ceeead955e671f8b9a3b',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/reviews/nine-variable-ipra-equal-length-stages-77-81-overlap/observations/stages-077-081/author/078/receipt.json': '00300fc41cf787db439a99d4afe49e0d14cffd1aa4fad505a3ad18aac750e420',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/reviews/nine-variable-ipra-equal-length-stages-77-81-overlap/observations/stages-077-081/verify/078/receipt.json': 'b6e4ccc3df85cfb740bcaf94fa9591d4d415c7744db3e95549a4cdfffb3d42d6',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/reviews/nine-variable-ipra-equal-length-stages-77-81-overlap/observations/stages-077-081/terminal.json': '6caef4771720124c2fd6612df8f76758ae68eef97211c129fde431f53ace84d8',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/reviews/nine-variable-ipra-equal-length-stages-77-81-overlap/observations/stages-077-081/audit.json': '273dabc30b4e5a83c9875788245f378dbf6b6505b8dd008274a2728bc117964a',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/reviews/nine-variable-ipra-equal-length-stages-77-81-overlap/observations/stages-077-081/author/078/ModelCarrierSyntax.lean': '8d40486fd9adf151e905977c01cbc1a2aa7142fbd02c5e4293906c6865e5a43a',
 str(LEAN): 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 **{path:sha for path,sha in DIRECT.values()}}
PRODUCER = '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/reviews/nine-variable-ipra-equal-length-stages-77-81-overlap/observations/stages-077-081/author/078/receipt.json'
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
    # Recheck every direct/companion/shadow slot captured by producer stage 078.
    producer = json.loads(Path(PRODUCER).read_text())
    if producer['status'] != 'PASS': raise RuntimeError('producer was not PASS')
    for name, record in producer['direct_guards'].items():
        obj = Path(name)
        if record is None:
            if os.path.lexists(obj): raise RuntimeError('producer absent slot changed: '+name)
            result['producer:'+name] = None
        else:
            if not obj.is_file() or str(obj.resolve()) != record['resolved'] or sha(obj) != record['sha256']:
                raise RuntimeError('producer direct guard changed: '+name)
            link = os.readlink(obj) if obj.is_symlink() else None
            if link != record['link']: raise RuntimeError('producer link changed: '+name)
            result['producer:'+name] = record
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
obj = OUT/'Normalized106Rational66.olean'
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
expected_reports = ["'DiophantineConsistency.Normalized106Rational66.values_equal' depends on axioms:", "'DiophantineConsistency.Normalized106Rational66.value67_eq_syntax' depends on axioms:", "'DiophantineConsistency.Normalized106Rational66.value66_eq_syntax' depends on axioms:"]
passed = (code == 0 and reason is None and samples > 0 and stable and obj.is_file() and not obj.is_symlink()
          and all(line in text for line in expected_reports) and not any(x in text for x in ('warning:', 'error:', 'sorryAx')))
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
    'scope': '66/67 rational-leaf complete graph identity and 106 syntax binding on the coherent historical stage-078 provider; direct captured-provider guards; inherited transitive and dynamic ancestry.',
}
(OUT/'result.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
print(json.dumps(result, sort_keys=True))
if not passed:
    raise SystemExit(1)
