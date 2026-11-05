#!/usr/bin/env python3
"""Guard and retain a bounded replay of the 79-to-80 ring binding."""
import hashlib, json, os, subprocess, sys, time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
source=here/'P64QCube79Binding.lean'
old=Path('/tmp/P64QCube80.olean'); new=Path('/tmp/P64QCube79.olean')
out=Path('/tmp/P64QCube79BindingReplay.olean')
receipt=here/'lean-replay.json'; log=here/'lean-replay.log'
if out.exists() or receipt.exists() or log.exists(): raise SystemExit('refusing to overwrite output')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
inputs={str(source):'6699312618be0598dc0cc49473533928a46fd91a54871eef444d4f600a04e6a1',str(old):'e8829517e10e4c3d2423594dd884b86466834d7714038660030d16861c8abd68',str(new):'9f9c2112fa677ac6b330bc722741386da048fd9e01d091aa09dcdb60d24def65',str(lean):'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
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
expected=''.join(f"'P64QCube79Binding.{n}' depends on axioms: [propext]\n" for n in ('first','main','strong','auxiliary','transport','output')).encode()
result={'returncode':code,'elapsed_seconds':round(time.monotonic()-start,3),'command':cmd,'lean_path':env['LEAN_PATH'],'input_hashes':inputs,'after_hashes':after,'output_sha256':sha(out) if out.exists() else None,'log_sha256':sha(log),'exact_expected_output':output==expected,'scope':'Actual generated-graph bindings; no zero-existence equivalence or full provider ancestry.'}
receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,sort_keys=True))
if code!=0 or any(after[p]!=h for p,h in inputs.items()) or output!=expected or not out.exists(): raise SystemExit(1)
