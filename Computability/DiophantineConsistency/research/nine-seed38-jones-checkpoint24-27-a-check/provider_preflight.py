#!/usr/bin/env python3
"""Point checks for audited M and A-node providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [
 ('nine-seed38-jones-checkpoint21-27-m-terminal-frontier-independent','950577a967e0d1c2754b5758ad1142745d28cb5c7848d7a88956d7e06cb120c2','bedb1a8cc3019dfa9881c8e69ed78383707f91bbc0f791cdf3371fadbb0ba4b5'),
 ('nine-seed38-jones-dependent03-staged-terminal-frontier-independent','456db91d9870d3207907a5c115e33939ea1b423e46119ab658293beceafdb969','0d0d2aaa5960eeaec7200494b62a585de92ce9da175dbb32d245ea8b9eff25e0')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint24-27-a-draft'
for n,h in [('Norm38MacroAPath','cbbe657413312903eca6f947477b05a7f92ad4fc2b817f8bb7feec0d56463fed'),('Norm38MacroAValue','4422b046d07d41e4c94a001b025e6c9f191e184f260788047bd029956710c495')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint21-27-m-check-20261106/lib/DiophantineConsistency')
providers=[
 ('Norm38MacroMValue','/tmp/nine-seed38-jones-checkpoint21-27-m-check-20261106/lib/DiophantineConsistency','aa0ba07d953598aa407e4d3c6356cc73bddd1d8b104b48440a24aad8db34695f'),
 ('Norm38MacroDependentA','/tmp/nine-seed38-jones-dependent03-staged-check-20261106/lib/DiophantineConsistency','ae2c004e07dd9ac2c080af9845a545e7ac46fd9418996bf3f646394a82782b12')]
selected={}
for n,root,h in providers:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Two audited M and A-node providers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
