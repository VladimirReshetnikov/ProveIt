#!/usr/bin/env python3
"""Check ordered-ring gap bounds for the trace75 two-index case."""
from pathlib import Path
from hashlib import sha256
import json, os, re, shutil, subprocess, sys, tempfile, time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H = Path(__file__).resolve().parent
D = H.parents[1]
SRC = H / 'Trace75PositiveTraceShift.lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACK = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
pins = {
    SRC: '4835c7bc85a5fc1897ed5f67add53da69456930c3528e80f106e829c1b00b786',
    PACK/'Mathlib/Algebra/Order/Ring/Basic.olean': 'ea83b1b21091681e446b6d29768b758db2523188f511a372f599db4d4f2d9333',
    PACK/'Mathlib/Tactic/Linarith.olean': 'bbe0c9d1f3d5471ae115ccd10d9ef2f6dc5ec645bad49ee5a04830c178e42091',
    PACK/'Mathlib/Tactic/Positivity.olean': '2cc0157fed7329f829258ec4d02d8a507b75db2dbe35836992c0781ab860f91c',
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
attempt = os.environ.get('ATTEMPT','shift-attempt01')
need(re.fullmatch(r'shift-attempt[0-9]{2,}', attempt) is not None, 'attempt')
out = H / 'observations' / attempt
need(not out.exists(), 'observation exists')
for p, x in pins.items(): need(sha(p) == x, 'input drift: '+str(p))
pre = resources(); need(pre['mem_available_kib'] >= 8*1024**2 and len(pre['lean']) < 2, 'resource preflight')
out.mkdir(parents=True)
root = Path(tempfile.mkdtemp(prefix='trace75-positiveshift-'))
src = root/'Trace75PositiveTraceShift.lean'
shutil.copyfile(SRC, src); shutil.copyfile(SRC, out/'source.txt')
obj = root/'Trace75PositiveTraceShift.olean'
cmd = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={root}', str(src), '-o', str(obj)]
env = {'PATH':'/usr/bin:/bin','LEAN_PATH':str(PACK),'LEAN_NUM_THREADS':'1'}
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
          'scope':'fresh provider source; selected direct imports only; package and transitive ancestry inherited'}
(out/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'exit':proc.returncode, 'reason':reason, 'root':str(root), 'object_sha256':result['object_sha256']}))
need(proc.returncode == 0 and reason is None and obj.is_file() and not re.search(r'(?i)(?:\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b)',log), 'Lean check failed')
