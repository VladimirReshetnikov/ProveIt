#!/usr/bin/env python3
"""Check ordered-ring gap bounds for the trace75 two-index case."""
from pathlib import Path
from hashlib import sha256
import json, os, re, shutil, subprocess, sys, tempfile, time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H = Path(__file__).resolve().parent
D = H.parents[1]
SRC = H / 'Trace75OldTracePositiveMap.lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACK = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
pins = {
    SRC: '4159326d3b7d7e4fc3c769b6d14448c1b63952a8c4e108b1ad9a6f517ebd0bb1',
    Path('/tmp/trace75-oldtracemap-qm52cj8c/Trace75OldTraceMap.olean'): '037f11212356efaa43494a640dbb45af97a437f6cadd2812c955bcdbc6d8ec56',
    Path('/tmp/trace75-naturalshift-23u480gg/Trace75NaturalTraceShift.olean'): 'b828737e9a8889dc05a8aab6e22f84dc2dd470a0265ae27d0d7462fe04498318',
    Path('/tmp/trace75-positiveshift-y7sk8val/Trace75PositiveTraceShift.olean'): 'f37bfe2a63967448298d15fc8aac2da4ad491489453be6bcd9d73ebda8a94c7b',
    Path('/tmp/trace75-fresh-rebuild-yn60cw_0/lib/DiophantineConsistency/ModelDifferenceRing.olean'): 'd0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74',
    Path('/tmp/trace75-fresh-rebuild-yn60cw_0/lib/DiophantineConsistency/ArithmeticPellRecurrence.olean'): 'd87f772441f0309bf879aeef7673bbdc2d2367d016402bafc8e6763e96b62a39',
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
attempt = os.environ.get('ATTEMPT','positive-attempt02')
need(re.fullmatch(r'positive-attempt[0-9]{2,}', attempt) is not None, 'attempt')
out = H / 'observations' / attempt
need(not out.exists(), 'observation exists')
for p, x in pins.items(): need(sha(p) == x, 'input drift: '+str(p))
pre = resources(); need(pre['mem_available_kib'] >= 8*1024**2 and len(pre['lean']) < 2, 'resource preflight')
out.mkdir(parents=True)
root = Path(tempfile.mkdtemp(prefix='trace75-oldtracepositive-'))
src = root/'Trace75OldTracePositiveMap.lean'
shutil.copyfile(SRC, src); shutil.copyfile(SRC, out/'source.txt')
obj = root/'Trace75OldTracePositiveMap.olean'
cmd = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={root}', str(src), '-o', str(obj)]
env = {'PATH':'/usr/bin:/bin','LEAN_PATH':'/tmp/trace75-oldtracemap-qm52cj8c:/tmp/trace75-naturalshift-23u480gg:/tmp/trace75-positiveshift-y7sk8val:/tmp/trace75-fresh-rebuild-yn60cw_0/lib:'+str(PACK),'LEAN_NUM_THREADS':'1'}
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
