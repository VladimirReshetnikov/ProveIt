#!/usr/bin/env python3
"""Point checks for audited U/Y, M and rank-carry providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [
 ('nine-seed38-jones-checkpoint20-27-uy-terminal-frontier-independent','2894cd041abc375f60d053f529fbbc295e6ec47d7906881e5fd73be9af54312f','9af33b21c2f238b47631d19bf1ab9120df596c87b1250af1ddebf4eee4152a0a'),
 ('nine-seed38-jones-dependent02-staged-terminal-frontier-independent','3fe72c765d785e759248768d743b1f948b2d7ec4146d2d981a938348f06d6bcb','03f4dd834eb2b106f48865c044c6614712d4f52487540cf6a717f70f8f7375fd'),
 ('nine-seed38-jones-live18-staged-terminal-frontier-independent','63ecdb794bbb09df8baa50c7a19c5f1f2de15193c0d3e34ccbc7c1fdd7165765','d4424de55d8afca035515af5bf56899b02ae64e9e7e011fa256021f267d78eac')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint21-27-m-draft'
for n,h in [('Norm38MacroMPath','a011200fa1d21b58d2986763cc4e6a0651160bb220e5fdf8635123a542b6229e'),('Norm38MacroMValue','01e3005d2546431cc995315ea20170c174b12b5d39c93c956afd14ff1ba0e9a4')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint20-27-uy-check-20261106/lib/DiophantineConsistency')
providers=[
 ('Norm38MacroUYValues','/tmp/nine-seed38-jones-checkpoint20-27-uy-check-20261106/lib/DiophantineConsistency','5be1513afe23c53b5207db78352da17597e1d45c6c8441aaa26695c4f7e9d092'),
 ('Norm38MacroDependentM','/tmp/nine-seed38-jones-dependent02-staged-check-20261106/lib/DiophantineConsistency','81363f56b3ea598151f89eda0e9cce2bdeca9c7b2a989b20739059343eb72454'),
 ('Norm38MacroLive18Group02','/tmp/nine-seed38-jones-live18-staged-check-20261106/lib/DiophantineConsistency','f028ef640af09a6477b7672e76630057147c859c26d908dafded919953f8a53c')]
selected={}
for n,root,h in providers:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Three audited U/Y, M and rank-carry providers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
