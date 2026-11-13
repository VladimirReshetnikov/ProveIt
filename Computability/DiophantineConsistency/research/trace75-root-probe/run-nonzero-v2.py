#!/usr/bin/env python3
"""Remove signed square representatives from trace75 root extraction."""
from pathlib import Path
from hashlib import sha256
import json, os, re, shutil, subprocess, sys, tempfile, time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H = Path(__file__).resolve().parent
D = H.parents[1]
SRC = H / 'Trace75RootNonzero.lean'
ROOTOBJ = Path('/tmp/trace75-root-wxe5rr8_/Trace75Root.olean')
MASK = Path('/tmp/tenpositive-product-root-kdq8sqms/ProductRoot.olean')
DOUBLE = Path('/tmp/tenpositive-doubling-z_t6ngdp/TenPositiveDoubling.olean')
SCALED = Path('/tmp/tenpositive-scaledsquare-rat00ki8/ScaledSquare.olean')
LIB = Path('/tmp/direct90-ipra-join-b66u_qqo/lib')
MODEL = LIB/'DiophantineConsistency/ModelDifferenceRing.olean'
PROVIDER = Path('/tmp/trace75-provider-wljjm6ws/DiophantineConsistency/TenPositiveTrace75.olean')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACK = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
pins = {
    SRC: '9879c7cf5c385cc6aafdb00e3b59f20fbaf5183ea537e34d61f2e009958c5cc1',
    ROOTOBJ: 'bf8d56a7526a5324d04c7178d8265e619a15aa624d117d11ba8b864831624958',
    MASK: '92dbb47e969d3603f6f496f53c7995493a989293a37e5272c308ff79d3fb09d5',
    DOUBLE: '138dbf9563aab2a4b867547b8f2ee9650faec64b2f403c17b1598b11db66522f',
    SCALED: '37ce988b94587130947097a868dd153f5564718dd280fafe6fd3b75aa2028691',
    MODEL: 'd0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74',
    LIB/'DiophantineConsistency/ArithmeticGcdNormalization.olean': '254b88abe787829f8bfad61f9606a14318cb31186b593e0cb76821e4e1ad1242',
    PROVIDER: '1ae82441c7023e9675c5cc532d4026da6a3ee77e906996d67c315e4f693b079c',
    LEAN: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
    PACK / 'Mathlib/Tactic/Ring.olean': 'cc12dfa66db7ef6ae4cd2d7a4e035ddffaca827168243f728812776b77836eb4',
    PACK / 'Mathlib/Tactic/LinearCombination.olean': 'e4487ef3e033c8a8cfe8562ee7a96d2926444bd73c7f138f265b58a8d1d14c08',
}
def sha(p): return sha256(Path(p).read_bytes()).hexdigest()
def need(test, message):
    if not test: raise RuntimeError(message)
def resources():
    rows = subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],check=True,capture_output=True,text=True).stdout.splitlines()
    lean = [r.strip() for r in rows if len(r.split(None,3)) == 4 and r.split(None,3)[1] == 'lean']
    mem = int(next(r for r in Path('/proc/meminfo').read_text().splitlines() if r.startswith('MemAvailable:')).split()[1])
    return {'time_ns':time.time_ns(), 'lean':lean, 'mem_available_kib':mem}
attempt = os.environ.get('ATTEMPT','nonzero-attempt02')
need(re.fullmatch(r'nonzero-attempt[0-9]{2,}', attempt) is not None, 'attempt')
out = H / 'observations' / attempt
need(not out.exists(), 'observation exists')
for p, x in pins.items(): need(sha(p) == x, 'input drift: '+str(p))
pre = resources(); need(pre['mem_available_kib'] >= 8*1024**2 and len(pre['lean']) < 2, 'resource preflight')
out.mkdir(parents=True)
root = Path(tempfile.mkdtemp(prefix='trace75-nonzero-'))
overlay = root/'DiophantineConsistency'; overlay.mkdir()
for target in (LIB/'DiophantineConsistency').iterdir():
    (overlay/target.name).symlink_to(target, target_is_directory=target.is_dir())
(overlay/'TenPositiveTrace75.olean').symlink_to(PROVIDER)
src = root/'Trace75RootNonzero.lean'
shutil.copyfile(SRC, src); shutil.copyfile(SRC, out/'source.txt')
obj = root/'Trace75RootNonzero.olean'
cmd = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={root}', str(src), '-o', str(obj)]
env = {'PATH':'/usr/bin:/bin','LEAN_PATH':str(ROOTOBJ.parent)+':'+str(MASK.parent)+':'+str(DOUBLE.parent)+':'+str(SCALED.parent)+':'+str(root)+':'+str(LIB)+':'+str(PACK),'LEAN_NUM_THREADS':'1'}
samples = []; reason = None; start = time.monotonic()
with (out/'stdout').open('x') as stdout, (out/'stderr').open('x') as stderr:
    proc = subprocess.Popen(cmd, env=env, stdout=stdout, stderr=stderr)
    while proc.poll() is None:
        sample = resources(); samples.append(sample)
        if sample['mem_available_kib'] < 8*1024**2 or len(sample['lean']) > 2:
            reason='resource guard'; proc.terminate(); break
        if time.monotonic()-start > 300:
            reason='timeout'; proc.terminate(); break
        time.sleep(2)
    try: proc.wait(timeout=10)
    except subprocess.TimeoutExpired: proc.kill(); proc.wait()
for p, x in pins.items(): need(sha(p) == x, 'input changed: '+str(p))
need(sha(src) == pins[SRC], 'copied source changed')
log = (out/'stdout').read_text() + (out/'stderr').read_text()
result = {'command':cmd, 'lean_path':env['LEAN_PATH'], 'exit':proc.returncode, 'reason':reason,
          'output_root':str(root), 'inputs':{str(p):x for p,x in pins.items()},
          'runner_sha256':sha(__file__), 'preflight':pre, 'samples':samples, 'postflight':resources(),
          'stdout_sha256':sha(out/'stdout'), 'stderr_sha256':sha(out/'stderr'),
          'object_sha256':sha(obj) if obj.is_file() else None,
          'scope':'conditional model root extraction; selected direct imports pinned; package/transitive ancestry and external graph binding inherited'}
(out/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'exit':proc.returncode, 'reason':reason, 'root':str(root), 'object_sha256':result['object_sha256']}))
need(proc.returncode == 0 and reason is None and obj.is_file() and not re.search(r'(?i)(?:\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b)',log), 'Lean check failed')
