#!/usr/bin/env python3
"""Low-priority bounded sphere endpoint check; never controls another process."""
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
SOURCE = HERE/'OrdinarySphere6984Literal.lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
DIRECT = {'OrdinarySphere7084Literal': ('/tmp/current2011-ordinary70-84-literal-check01/OrdinarySphere7084Literal.olean', '69aea03a50aeb2f6d10a445c5664438771fe668174e45ac456ded02716b50720'), 'DiophantineConsistency/Carrier94Value': ('/tmp/current2011-ordinary94-six-overlay-20261105/lib/DiophantineConsistency/Carrier94Value.olean', 'a9c320a8e69a693aa869dbb7b272fe642e1bf76420e2602e580abbdfff52e887')}
OUT = Path('/tmp/current2011-ordinary69-84-literal-check01')
LEAN_PATH = '/tmp/current2011-ordinary70-84-literal-check01:/tmp/current2011-ordinary94-six-overlay-20261105/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
EXPECTED = {
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-ordinary69-84-literal/OrdinarySphere6984Literal.lean': 'dcf382876f4e7538f19a1a4ce584da76b218e008cd04842226236d31bf7bf71f',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/normalized106-fresh-base-model-build/FreshModel106.lean': '61e64a2ef559c3da369021df2705cd76f957bc0ea971467b80d627eaa9422769',
 '/tmp/normalized106-fresh-model-client-20261105/state.json': 'dea372080bd6380703bdf770bde887436699f7998e7927dacadb2bec66016d23',
 '/tmp/current14-standard-fresh-build-20261104/state.json': 'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014',
 '/tmp/normalized106-fresh-model-build-v2-20261105/state.json': 'c42e5d49c4234ff93e61b7dbadf63fe8e2d465f470f4772879694796d898272c',
'/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-ordinary94-six-module-build/survey-result-snapshot.json': 'd923d399d157acadabe033138791583b34b52c2f992e0800b04e652bb05ce821',
 '/tmp/current2011-ordinary94-six-overlay-20261105/overlay.json': '607e33f8290b8c4338e844b59334b0ad7b635c7e7b699c40a74e3274c4714e1e',
 '/tmp/current2011-ordinary94-six-overlay-20261105/lib/DiophantineConsistency/Carrier94Syntax.olean': 'b0a4f82738eb22627c3631b0cfc48053b8051682fb7ed5c2b958281a7e29c76b',
 '/tmp/current2011-ordinary94-six-overlay-20261105/lib/DiophantineConsistency/Carrier94Value.olean': 'a9c320a8e69a693aa869dbb7b272fe642e1bf76420e2602e580abbdfff52e887',
 '/tmp/current2011-ordinary94-six-overlay-20261105/lib/DiophantineConsistency/ArithmeticPellResidueAux.olean': '822ff3a7319d4e56cab509034489ec8a984816078630cb3d7fdb01a4df00df29',
 '/tmp/current2011-ordinary94-six-overlay-20261105/lib/DiophantineConsistency/ArithmeticCarrier94Indices.olean': 'e61314249a1cebf8cf30f800a884ad2299eed69ec4946d42d3e23eb36264d951',
 '/tmp/current2011-ordinary94-six-overlay-20261105/lib/DiophantineConsistency/ArithmeticCarrier94Soundness.olean': '85330b0536024a0afa6dcb693dfc11afe8c7a9469e0a86c65bae59d8cb788bf0',
 '/tmp/current2011-ordinary94-six-overlay-20261105/lib/DiophantineConsistency/ArithmeticCarrier94Extraction.olean': '51fb88739bbd625ce47e33a9fca193d962f4165186eca7ad6017bcd20f1b22ac',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-ordinary94-six-module-build/attempt01/result.json': '380405fde37344135b7cbeded449412cfdd905c1ccc04aa19e45c92274721c27',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-ordinary94-six-module-build/attempt02/result.json': '16ed96a09e44cbaa63c9592560dab2f340bf908b18ccd8d08097d3734782f974',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-ordinary94-six-module-build/attempt03/result.json': '08a9bb766e805be1f647170080c0156bfc7fc9237d25dceeb1b079debfbb0a11',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-ordinary94-six-module-build/attempt04/result.json': 'fd0eb4fb389ac27d1d6c42ff3b3a22e9386edff0774de6a6e85861884d571a80',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-ordinary94-six-module-build/attempt05/result.json': 'd2848efcaa6b3aadc58dec758a33e08e5999e84ec4d1020a431a2736eac39fb3',
'/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-ordinary94-fresh-endpoint/FreshCarrier94.lean': 'fc792393a91b12a34346e02aeefff3e799f710c1651afccdaaa5fd26c914747e',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-ordinary94-fresh-endpoint/attempt01/result.json': '5378e5fae67be1259a9b28143ab9be3d08d3c6e3e6cdfef55ae05676923311de',
'/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-spheres-fresh-base/attempt02/result.json': '67159c8c4665700e59c6745b705f42ecc459ca6a38f79bd95545c8e7115c31d9',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-ordinary71-60-generic/OrdinarySphere7160Generic.lean': '5808bcc7f662ff319ad6c64811260e216739888a7d4a8d89c68390d2561f9bae',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-ordinary71-60-generic/attempt02/result.json': 'f528cbbcd0f7bca3b4f54e4ca7dfaded857eb662a7a586791d6935cfc96bb003',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-ordinary69-84-candidate/polynomial.json': 'c9781e95b9d8e3124afadfe3ee5874eb3eb76ce9f1aaef02c7b3bf49ed93e80a',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-ordinary70-84-literal/OrdinarySphere7084Literal.lean': 'e498fa16e97284c4d048460769d758d4f5b354e2cd9faa616c1857f84897e8ec',
 '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-ordinary70-84-literal/attempt01/result.json': 'ccbd3ba0713022aaf04e1cbb26b3329742d699faa9fa7e9b303cb01acf62b44d',
 str(LEAN): 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 **{path:sha for path,sha in DIRECT.values()}}
PRODUCERS = ['/tmp/normalized106-fresh-model-client-20261105/state.json']
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
    # Recheck both passed client producers' direct/companion/shadow slots.
    for producer_path in PRODUCERS:
        producer = json.loads(Path(producer_path).read_text())
        if producer['status'] != 'PASS': raise RuntimeError('producer not PASS: '+producer_path)
        for name, record in producer['direct_guard'].items():
            obj = Path(name)
            if record is None:
                if os.path.lexists(obj): raise RuntimeError('producer absent slot changed: '+name)
                result[producer_path+':'+name] = None
            else:
                if not obj.is_file() or str(obj.resolve()) != record['realpath'] or sha(obj) != record['sha256']:
                    raise RuntimeError('producer guard changed: '+name)
                result[producer_path+':'+name] = record
        for mod, record in producer['dependencies'].items():
            obj = Path(record['path'])
            if not obj.is_file() or str(obj.resolve()) != record['realpath'] or sha(obj) != record['sha256']:
                raise RuntimeError('producer dependency changed: '+mod)
            result[producer_path+':dependency:'+mod] = record
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
obj = OUT/'OrdinarySphere6984Literal.olean'
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
expected_reports = ["'DiophantineConsistency.OrdinarySphere6984Literal."+n+"' depends on axioms:" for n in ("eval_expression","value_eq70")]
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
    'scope': 'Literal 69/84 evaluation and exact 70/84 all-ring identity; direct captured guards and inherited ancestry; direct captured-provider guards; inherited transitive and dynamic ancestry.',
}
(OUT/'result.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
print(json.dumps(result, sort_keys=True))
if not passed:
    raise SystemExit(1)
