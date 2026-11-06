#!/usr/bin/env python3
"""Point checks for audited path, carry and input-value providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [
 ('nine-seed38-jones-prefix-path18-45-terminal-frontier-independent','c5c1cd88f8ba8c5e73fca03c950405acf2f3d1d565bb2ecd010e81a268bff9b8','1362a00854f9d179d4fe9ffb6455431fabb1bb082c140d020c4713e7d87f703a'),
 ('nine-seed38-jones-live18-staged-terminal-frontier-independent','63ecdb794bbb09df8baa50c7a19c5f1f2de15193c0d3e34ccbc7c1fdd7165765','d4424de55d8afca035515af5bf56899b02ae64e9e7e011fa256021f267d78eac'),
 ('nine-seed38-jones-prefix-group04-staged-terminal-frontier-independent','31d6811cc6682276bb919729d3bc9f6465802abf6f2a134626cf7bcad193a26e','153db18a7fbd10ce1ad77c25d25f7eaceeab5f9e2b877821392b4e1416129925')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint27-34-draft/Norm38MacroCheckpoint27to34.lean'
if sha(draft)!='4693daae8e6c0f64c75480e88fd3d240b1e6862b0af9461ce043a45757790ed0':raise RuntimeError('source')
a=D/'research/nine-seed38-jones-prefix-path18-45-check/attempt01/state.json';b=D/'research/nine-seed38-jones-prefix-group04-staged-check/attempt01/state.json'
if sha(a)!='cbfeac916fd53fafbb6c0b9619171830cce1c44960d8780f11c1a280a9297309' or sha(b)!='b8a10144c1331d6eb06789d23eef0bd1713d6ebb1876449270216e6ff6e082c1':raise RuntimeError('state pins')
def librels(s):
 result={}
 for k,v in s['overlay_links'].items():
  if '/lib/' not in k:raise RuntimeError(('overlay shape',k))
  rel=k.split('/lib/',1)[1]
  if rel in result:raise RuntimeError(('duplicate overlay',rel))
  result[rel]=v
 return result
ax,by=librels(json.loads(a.read_text())),librels(json.loads(b.read_text()))
if any(k not in ax or ax[k]!=v for k,v in by.items()):raise RuntimeError('overlay disagreement')
base=Path('/tmp/nine-seed38-jones-prefix-path18-45-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h,needs_route in [
 ('Norm38MacroPath18to45','/tmp/nine-seed38-jones-prefix-path18-45-check-20261106/lib/DiophantineConsistency','e745b03d17c4a9ae99452cacda9d98ad8103d902395e56976ba48a37f382ba21',True),
 ('Norm38MacroLive18Group03','/tmp/nine-seed38-jones-live18-staged-check-20261106/lib/DiophantineConsistency','2589ac6c78d736a31bd3e851aaa0068d43ec0a10a10b3cb648b4df8b7da9d902',True),
 ('Norm38MacroPrefixInputsB','/tmp/nine-seed38-jones-prefix-group04-staged-check-20261106/lib/DiophantineConsistency','43b71a21b7efa4d263709791c323ac49005a3e3b28542836890e094710474170',False)]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or sha(p)!=h:raise RuntimeError(('producer',n))
 if needs_route and (not q.is_file() or q.resolve()!=p.resolve() or sha(q)!=h):raise RuntimeError(('route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'shared_overlay_paths':len(by),'scope':'Three audited providers and overlay comparison; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
