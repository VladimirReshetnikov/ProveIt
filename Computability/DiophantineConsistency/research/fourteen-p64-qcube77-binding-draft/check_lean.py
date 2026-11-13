#!/usr/bin/env python3
"""Guard and retain a bounded replay of the 77-to-78 ring binding."""
import hashlib, json, os, subprocess, sys, time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
source=here/'P64QCube77Binding.lean'
old=Path('/tmp/P64QCube78.olean'); new=Path('/tmp/P64QCube77.olean')
out=Path('/tmp/P64QCube77BindingReplay.olean')
receipt=here/'lean-replay.json'; log=here/'lean-replay.log'
if out.exists() or receipt.exists() or log.exists(): raise SystemExit('refusing to overwrite output')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
inputs={str(source):'f3e0fdd02ca04440ada8b7027be095cc9611f69c7e8beb63d5048c72e01d1cc5',str(old):'112e4979a76e241719cbb1b682e98c8cebabb3150c3349055dd6964ed12be0f5',str(new):'daa0b689982287a74991a14c588a23d64f7bc1b5959a2528d000a6f64c0bc99d',str(lean):'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
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
expected=''.join(f"'P64QCube77Binding.{n}' depends on axioms: [propext]\n" for n in ('first','main','strong','auxiliary','transport','output_shape','output_eval')).encode()
result={'returncode':code,'elapsed_seconds':round(time.monotonic()-start,3),'command':cmd,'lean_path':env['LEAN_PATH'],'input_hashes':inputs,'after_hashes':after,'output_sha256':sha(out) if out.exists() else None,'log_sha256':sha(log),'exact_expected_output':output==expected,'scope':'Actual generated-graph bindings; no zero-existence equivalence or full provider ancestry.'}
receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,sort_keys=True))
if code!=0 or any(after[p]!=h for p,h in inputs.items()) or output!=expected or not out.exists(): raise SystemExit(1)
