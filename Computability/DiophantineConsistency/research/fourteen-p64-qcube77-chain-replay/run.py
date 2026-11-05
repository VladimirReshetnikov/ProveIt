#!/usr/bin/env python3
"""Replay the three 77 unit/facts/existence modules with guarded direct inputs."""
import hashlib, json, os, subprocess, sys, time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
src=here.parent/'fourteen-p64-qcube77-unit-draft'
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
overlay=Path('/tmp/p64-qcube77-chain-replay')
if overlay.exists() or any((here/name).exists() for name in ('receipt.json','Unit.log','OldFacts.log','Existence.log')):
    raise SystemExit('refusing to overwrite outputs')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
inputs={str(lean):'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 str(src/'P64QCube77Unit.lean'):'73e76eaa00bfcae01fa2b13a83892547c44c4aba34f58af4185920cfafe871dd',
 str(src/'P64QCube77OldFacts.lean'):'d100eb7a6f573fbe042657f52c1de36551ad48a09a3679dc9a65209f80be60da',
 str(src/'P64QCube77Existence.lean'):'e65822241f4308d969094f91b68a90a5c267ad82b852b3b7b68f2fad769a942a',
 '/tmp/P64QCube78GraphSplit.olean':'76da5f69b14d211994c5ccc12e9e9de9d5d3b585b002149bca4922d7ca536150',
 '/tmp/P64QCube78Existence.olean':'8371368a8feb9de7e729501224455ab26848c1509b88c93aadd757b38e0bd669',
 '/tmp/P64QCube77Binding.olean':'550873ad2b0074bfb3265c1f828957b697787806cf367383ecf7d6d8b8275c3d'}
expected_objects={'Unit':'5e4e354b5a0a420c94967ca71c99a5088d41bac615651225c5aaf44a9390370d',
 'OldFacts':'48b2c4d8dc7a4a3b56123a519f0989ef0d48b35f9ecfb28be5d56f17c65003fd',
 'Existence':'0cd0fa8b52a8cad49bad9db49507f16acb0171ee56dad0e21783515facf15a72'}
names={'Unit':['positive_factors','first_ne_neg_of_transport'],'OldFacts':['residuals'],
       'Existence':['same_zero_iff','positive_zero_iff']}
for p,h in inputs.items():
    if sha(Path(p))!=h: raise RuntimeError('input hash drift: '+p)
overlay.mkdir()
env=os.environ.copy(); env['LEAN_PATH']=str(overlay)+':/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
results=[]; status='PASS'
for stage in ('Unit','OldFacts','Existence'):
    cmd=[str(lean),'-M4000','-j1','-DElab.async=false','--root='+str(src),str(src/('P64QCube77'+stage+'.lean')),'-o',str(overlay/('P64QCube77'+stage+'.olean'))]
    start=time.monotonic()
    try:
        p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180,env=env)
        code=p.returncode; output=p.stdout
    except subprocess.TimeoutExpired as e:
        code=124; output=e.stdout or b''
    log=here/(stage+'.log'); log.write_bytes(output)
    output_path=overlay/('P64QCube77'+stage+'.olean')
    exact=''.join(f"'P64QCube77{stage}.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in names[stage]).encode()
    after={p:sha(Path(p)) for p in inputs}
    result={'stage':stage,'returncode':code,'elapsed_seconds':round(time.monotonic()-start,3),'command':cmd,
            'log_sha256':sha(log),'exact_expected_output':output==exact,
            'output_sha256':sha(output_path) if output_path.exists() else None,
            'expected_object_sha256':expected_objects[stage],'input_hashes_after':after}
    results.append(result)
    if code!=0 or output!=exact or result['output_sha256']!=expected_objects[stage] or any(after[p]!=h for p,h in inputs.items()):
        status='FAIL'; break
result={'status':status,'lean_path':env['LEAN_PATH'],'input_hashes_before':inputs,'stages':results,
        'scope':'Three-module replay only; direct captured inputs guarded, full project/package/dynamic/search-path ancestry and external bindings not authenticated.'}
(here/'receipt.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':status,'stages':[(r['stage'],r['returncode'],r['elapsed_seconds']) for r in results]},sort_keys=True))
if status!='PASS': raise SystemExit(1)
