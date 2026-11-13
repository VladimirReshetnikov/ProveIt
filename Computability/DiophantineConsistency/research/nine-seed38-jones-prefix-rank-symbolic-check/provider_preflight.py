#!/usr/bin/env python3
"""Point checks for the rank and symbolic-prefix producers; no Lean."""
import hashlib, json, subprocess, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent; D=P.parents[1]
sha=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,check,result in [
 ('nine-seed38-jones-prefix-rank-composition-retry01-terminal-frontier-independent','42558aac5baefa9514d6a2bfe24a22fb3f9de6efac613ba1cab700aaa325b0e6','a1bc42c0438439a6bf8de280f3f35d14ca1edc9eff4e4cc9adec9b05b838e13a'),
 ('nine-seed38-jones-prefix-group02-staged-terminal-frontier-independent','0491edf9eadfba7404f118c6445482ed6245560fe873f7f19ccdfaea99b4fa32','f5c72aa2d5225957dafe9e3779feb803d2f0ddef8a725349e3a93b63ecc6b516'),
 ('nine-seed38-jones-prefix-group03-staged-terminal-frontier-independent','7ff8505e755090bf5b29abe4b074bcd36546ed597cc43405b9e4ea6a87c72745','2742892c8e514ac28db872993d219c639faf84961fd18f4852a03e01de81c8e3')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=check or sha(q/'result.json')!=result:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-prefix-rank-symbolic-draft'
for n,h in [('Norm38MacroRankValuesSums','bbba5ddc203be9f227a16a34972094c0df0b39a02d504a153d531b1d08d5e457'),('Norm38MacroRankValuesOther','ee3eebe4c841142a901c1cb93e77e2a59999be949e7d6557ce1a36d52814648b'),('Norm38MacroRankSymbolic','e87602c26e25d62e2ab8f72aa1864a3f6017dd105d9a7f721099e7b1ffdd4f60')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-prefix-rank-composition-retry01-20261106/lib/DiophantineConsistency')
providers=[
 ('Norm38MacroRankComposition','/tmp/nine-seed38-jones-prefix-rank-composition-retry01-20261106/lib/DiophantineConsistency','682aefdc3bde128ef02c981a75c84230ade20e306cfadefd3f49f99fe7bcb548'),
 ('Norm38MacroPrefixE','/tmp/nine-seed38-jones-prefix-group02-staged-check-20261106/lib/DiophantineConsistency','b1742d0c3c6372d05c31627da4e6f4bc32ad1757a7d20c1e31774109ec3cbe64'),
 ('Norm38MacroPrefixEll','/tmp/nine-seed38-jones-prefix-group02-staged-check-20261106/lib/DiophantineConsistency','bdf292db45b95d08a08d93a886567f773c0462c16bed0a6a8806a7e3b7539712'),
 ('Norm38MacroPrefixLambda','/tmp/nine-seed38-jones-prefix-group02-staged-check-20261106/lib/DiophantineConsistency','7f2d141c3f7c256e86f61f7ddef52f5a6025ce872a5ede3d3c1f5f8fd4caba0d'),
 ('Norm38MacroPrefixGsmall','/tmp/nine-seed38-jones-prefix-group03-staged-check-20261106/lib/DiophantineConsistency','dd500df7b9ea630528181ee3e1ac62f955822471a9f3385e0a833c13758dbaf2'),
 ('Norm38MacroPrefixTheta','/tmp/nine-seed38-jones-prefix-group03-staged-check-20261106/lib/DiophantineConsistency','6c76ea5f4ab7a4390bad1fd78c54fd95353d23af842596a0823d72d8fb088a64')]
selected={}
for n,root,h in providers:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Audited rank and symbolic-value providers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
