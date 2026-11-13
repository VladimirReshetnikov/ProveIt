#!/usr/bin/env python3
"""Check the abstract large-first-index exclusion for trace75."""
from pathlib import Path
from hashlib import sha256
import json, os, re, shutil, subprocess, sys, tempfile, time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H = Path(__file__).resolve().parent
D = H.parents[1]
SRC = H / 'Trace75ThreeLarge.lean'
LIB = Path('/tmp/direct90-ipra-join-b66u_qqo/lib')
HALF = LIB/'DiophantineConsistency/ArithmeticPellHalfIndex.olean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACK = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
pins = {
    SRC: '4d545b6e32476f8a362d5057e69616a59ddb3e70ac56d91728d7ba8a84c337e9',
    HALF: '6142ab8eaac6e281c3372817a6f1a8cbc14704717d4f5479c28603c754c3a4d7',
    PACK/'Mathlib/Tactic/Linarith.olean': 'bbe0c9d1f3d5471ae115ccd10d9ef2f6dc5ec645bad49ee5a04830c178e42091',
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
attempt = os.environ.get('ATTEMPT','threelarge-attempt03')
need(re.fullmatch(r'threelarge-attempt[0-9]{2,}', attempt) is not None, 'attempt')
out = H / 'observations' / attempt
need(not out.exists(), 'observation exists')
for p, x in pins.items(): need(sha(p) == x, 'input drift: '+str(p))
pre = resources(); need(pre['mem_available_kib'] >= 8*1024**2 and len(pre['lean']) < 2, 'resource preflight')
out.mkdir(parents=True)
root = Path(tempfile.mkdtemp(prefix='trace75-threelarge-'))
src = root/'Trace75ThreeLarge.lean'
shutil.copyfile(SRC, src); shutil.copyfile(SRC, out/'source.txt')
obj = root/'Trace75ThreeLarge.olean'
cmd = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={root}', str(src), '-o', str(obj)]
env = {'PATH':'/usr/bin:/bin','LEAN_PATH':str(LIB)+':'+str(PACK),'LEAN_NUM_THREADS':'1'}
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
