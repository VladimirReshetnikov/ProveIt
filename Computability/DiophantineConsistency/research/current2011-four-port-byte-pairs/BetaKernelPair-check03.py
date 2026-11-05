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
SOURCE = HERE/'BetaKernelPair.lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
DIRECT = {'CurrentBetaBytes': ('/tmp/current2011-beta-byte-binding-v2-20261105/CurrentBetaBytes.olean', 'b1601003102f4483dfcaba4238826e85b4a356ff99fcd28322f31c0f93862e27'), 'KernelRecipe': ('/tmp/current2011-kernel-byte-recipe-check02-20261105/KernelRecipe.olean', 'f973fcebb0440d40bc11ef28bb3f45e717599305d0246ec892e3d9a22ce5a073'), 'CurrentMCBytes': ('/tmp/current2011-mc-byte-binding-v5-20261105/CurrentMCBytes.olean', '392c502cfd8a6c10b695187e0b463affbadf0062b68f01f7657d449707c641c4'), 'CurrentMFDecoderExplicit': ('/tmp/current2011-mf-decoder-explicit-term-20261105/CurrentMFDecoderExplicit.olean', 'de6ae438ffe08244be49fa20982a1936607ea2f2a68036d5172f368fe4448db6')}
OUT = Path('/tmp/current2011-four-port-BetaKernelPair-check03')
LEAN_PATH = '/tmp/current2011-beta-byte-binding-v2-20261105:/tmp/current2011-kernel-byte-recipe-check02-20261105:/tmp/current2011-mc-byte-binding-v5-20261105:/tmp/current2011-mf-decoder-explicit-term-20261105:/tmp/current2011-mf-natural-sum-probe-20261105:/tmp/current2011-mf-port-cast-probe-20261105:/tmp/current2011-mf-recipe-diagnostic-20261105:/tmp/normalized106-fresh-model-client-20261105:/tmp/current14-mf-base-only-attempt02-20261104/lib:/tmp/normalized106-fresh-model-build-v2-20261105/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
EXPECTED = {'/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-four-port-byte-pairs/BetaKernelPair.lean': '80ca7c881b25f341ba84c06bd6f2a670a3719feba57fd44ef7056ad36425b02d', '/tmp/current2011-beta-byte-binding-v2-20261105/state.json': '499a0f11346df9d952e6bd67964c3bed3b4272701f97aa2a3a62bf4b6f32c0f2', '/tmp/current2011-beta-byte-binding-v2-20261105/CurrentBetaBytes.lean': '538444983d5a713194673f3e17377e234bbce33d27d0f3cffa37d4a1eff762c8', '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-beta-byte-binding/attempt02/outer-terminal.json': '7167d42d73a0bf463d190f1ff64af6218dcdc2e087ad15e6d415271cc6a70822', '/tmp/current2011-kernel-byte-recipe-check02-20261105/state.json': 'f752ed2a04fc0ee2638d3687f2555abccf5796f49a10dccf015c05d1a5a0641d', '/tmp/current2011-kernel-byte-recipe-check02-20261105/KernelRecipe.lean': '13a3b32b1c87156229608a5e8cac2a33a2f85b8b87bec329f35b51cc71ab649a', '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-kernel-byte-recipe/attempt02/outer-observation.json': '86a9b1fd9ae3abf73890aa8abab3d5793cf6717f6c6f9980e3f3caab7929ac65', '/tmp/current2011-mc-byte-binding-v5-20261105/state.json': '6388d37739b7c82a09e66c497f6f88ee628b0487477ad309d0467b130d894b00', '/tmp/current2011-mc-byte-binding-v5-20261105/CurrentMCBytes.lean': 'e30de9bd64cfbdd0c372a42805dd79c0a1629be7c6be6103cbf248332bbb2eb8', '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-mc-byte-binding/attempt05/outer-terminal.json': '993709a87936de698d8674e2897f467bc7605838c00159934e823b2412afbbdd', '/tmp/current2011-mf-decoder-explicit-term-20261105/state.json': 'f0e062f99b4c4abc2579758d78a9a4b8b0a6aed0192515c01e9dc2b6c06cbab6', '/tmp/current2011-mf-decoder-explicit-term-20261105/CurrentMFDecoderExplicit.lean': 'e827d52dd16c3220e3df5068c7c7df1c2f63eb76be3547165c791d1d6e724ae7', '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/current2011-mf-decoder-explicit-term/outer-terminal.json': '60f4b28be1ab0e67efa39e08780e317d66005564f417c88769c805e93173347c'}
EXPECTED[str(LEAN)] = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
EXPECTED.update({path: digest for path,digest in DIRECT.values()})
PRODUCERS = ['/tmp/current2011-beta-byte-binding-v2-20261105/state.json', '/tmp/current2011-kernel-byte-recipe-check02-20261105/state.json', '/tmp/current2011-mc-byte-binding-v5-20261105/state.json', '/tmp/current2011-mf-decoder-explicit-term-20261105/state.json']
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
obj = OUT/'BetaKernelPair.olean'
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
expected_reports = ["'DiophantineConsistency.BetaKernelPair.decode_pair' depends on axioms:"]
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
    'scope': 'Four symbolic byte recipes decoded to current ports; no filesystem or gzip theorem; direct captured-provider guards; inherited transitive and dynamic ancestry.',
}
(OUT/'result.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
print(json.dumps(result, sort_keys=True))
if not passed:
    raise SystemExit(1)
