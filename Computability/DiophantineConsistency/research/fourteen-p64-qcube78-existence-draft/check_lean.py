#!/usr/bin/env python3
"""Guard and retain a bounded replay of the 78-to-79 zero equivalence."""
import hashlib, json, os, subprocess, sys, time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
source=here/'P64QCube78Existence.lean'
out=Path('/tmp/P64QCube78ExistenceReplay.olean')
receipt=here/'lean-replay.json'; log=here/'lean-replay.log'
if out.exists() or receipt.exists() or log.exists(): raise SystemExit('refusing to overwrite output')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
inputs={str(source):'a5e64c5dfeed7752d80546d6ff3b61cff314767d64682c173f935734e22b3af7', '/tmp/P64QCube78Binding.olean':'9a2ad33b9e505ea7e2042f694439d6a64684862fca6d38d107c0f4c4cc6d6ffd', '/tmp/P64QCube78GraphSplit.olean':'76da5f69b14d211994c5ccc12e9e9de9d5d3b585b002149bca4922d7ca536150', '/tmp/P64QCube79Gap.olean':'26c848d85051079068ff792d277b8ca974b37b4e5dc905f25dd9c3b2701e0007',str(lean):'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
for p,h in inputs.items():
    if sha(Path(p))!=h: raise RuntimeError('input hash drift: '+p)
env=os.environ.copy(); env['LEAN_PATH']='/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
cmd=[str(lean),'-M4000','-j1','-DElab.async=false','--root='+str(here),str(source),'-o',str(out)]
start=time.monotonic()
try:
    p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180,env=env)
    code=p.returncode; output=p.stdout
except subprocess.TimeoutExpired as e:
    code=124; output=e.stdout or b''
log.write_bytes(output)
after={p:sha(Path(p)) for p in inputs}
names=('old_first_eq_zero','same_zero_iff','positive_zero_iff')
expected=''.join(f"'P64QCube78Existence.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in names).encode()
result={'returncode':code,'elapsed_seconds':round(time.monotonic()-start,3),'command':cmd,'lean_path':env['LEAN_PATH'],'input_hashes':inputs,'after_hashes':after,'output_sha256':sha(out) if out.exists() else None,'log_sha256':sha(log),'exact_expected_output':output==expected,'scope':'Positive-zero existence equivalence in indicated arithmetic models; no full provider ancestry, external display or iPRA endpoint.'}
receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,sort_keys=True))
if code!=0 or any(after[p]!=h for p,h in inputs.items()) or output!=expected or not out.exists(): raise SystemExit(1)
