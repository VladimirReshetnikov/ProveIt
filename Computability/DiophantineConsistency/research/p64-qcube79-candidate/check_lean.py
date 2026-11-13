#!/usr/bin/env python3
"""Guarded generated-graph compile; does not prove equivalence."""
import hashlib, json, os, subprocess, sys, time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
source=here/'P64QCube79.lean'
parent=Path('/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/Compact44/P64Graph.olean')
out=Path('/tmp/P64QCube79.olean')
receipt=here/'lean-check.json'; log=here/'lean-check.log'
if out.exists() or receipt.exists() or log.exists(): raise SystemExit('refusing to overwrite output')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
inputs={str(source):'377abf054d664130d10e781e5b239f6776f4f3e31c175bfcbff27fb3f2002d4f',str(parent):'4be074aa56722e991b3c067e22a00d19e2b90b8ab97b0755cc606eecb0b2445c',str(lean):'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
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
result={'returncode':code,'elapsed_seconds':round(time.monotonic()-start,3),'command':cmd,'lean_path':env['LEAN_PATH'],'input_hashes':inputs,'after_hashes':after,'output_sha256':sha(out) if out.exists() else None,'log_sha256':sha(log),'scope':'Generated graph definition only; no equivalence or full provider ancestry.'}
receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,sort_keys=True))
if code!=0 or any(after[p]!=h for p,h in inputs.items()) or output or not out.exists(): raise SystemExit(1)
