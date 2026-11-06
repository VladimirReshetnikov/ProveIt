#!/usr/bin/env python3
"""Point checks for audited U/Y checkpoint/input providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [
 ('nine-seed38-jones-checkpoint41-45-terminal-frontier-independent','a54ac0ebb0ad366984dbf17127ec731fc24cb2d273a3379c0082671efd4dde45','e1c9bfd226f3b93e3deeb7893db3e93f48085a9a36676e3273891873a217e76a'),
 ('nine-seed38-jones-live18-staged-terminal-frontier-independent','63ecdb794bbb09df8baa50c7a19c5f1f2de15193c0d3e34ccbc7c1fdd7165765','d4424de55d8afca035515af5bf56899b02ae64e9e7e011fa256021f267d78eac'),
 ('nine-seed38-jones-prefix-group04-staged-terminal-frontier-independent','31d6811cc6682276bb919729d3bc9f6465802abf6f2a134626cf7bcad193a26e','153db18a7fbd10ce1ad77c25d25f7eaceeab5f9e2b877821392b4e1416129925'),
 ('nine-seed38-jones-prefix-group05-terminal-frontier-independent','be57dc896c38e9f6e029d57041979a7edbfdcbed32d857ed97d877018141f423','983d494267643fd48718d104fe302405b7b2d5ea705b00abaf7854594849dbbb'),
 ('nine-seed38-jones-dependent01-staged-terminal-frontier-independent','428e5c4a81481b076a9a3ac8e48de105b6743df9c3ab9669a1c90020b55c6f8b','8729babe68c3fe7f3a27d58af564586d5e3d6e8f9e822fb806c8f9c8ba6d4a43')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint20-27-uy-draft'
for n,h in [('Norm38MacroUYInputs','091748e2df9a1dfc57fe7f8cbbcbbd05eb0e3b897c9c47018d88e801a20f3638'),('Norm38MacroUYPath','6a7c59a748175f3f2de5b4caac2e5e25b4b050490fcfb59c9d06d2fdaefafeb8'),('Norm38MacroUYValues','26a2652103e1bae571844c29f7cbfb0e27819cc3add1bf57e20a6ff837c88c14')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
a=D/'research/nine-seed38-jones-checkpoint41-45-check/attempt01/state.json';b=D/'research/nine-seed38-jones-prefix-group04-staged-check/attempt01/state.json'
if sha(a)!='78103852f59ba1c747a3e7b709e0a810fd09beca5449c70473cb65e47826789f' or sha(b)!='b8a10144c1331d6eb06789d23eef0bd1713d6ebb1876449270216e6ff6e082c1':raise RuntimeError('state pins')
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
base=Path('/tmp/nine-seed38-jones-checkpoint41-45-check-20261106/lib/DiophantineConsistency')
providers=[
 ('Norm38MacroCheckpoint41to45','/tmp/nine-seed38-jones-checkpoint41-45-check-20261106/lib/DiophantineConsistency','d0dc8713317ad6f6b829c3776d740169273d9abecbf5a344489c148fb04cb565',True),
 ('Norm38MacroLive18Group01','/tmp/nine-seed38-jones-live18-staged-check-20261106/lib/DiophantineConsistency','b2c531a9eecdd13baaf18f2f130949cd8fd7602118f575cd124fffa4b0dc32dd',True),
 ('Norm38MacroLive18Group03','/tmp/nine-seed38-jones-live18-staged-check-20261106/lib/DiophantineConsistency','2589ac6c78d736a31bd3e851aaa0068d43ec0a10a10b3cb648b4df8b7da9d902',True),
 ('Norm38MacroPrefixInputsA','/tmp/nine-seed38-jones-prefix-group04-staged-check-20261106/lib/DiophantineConsistency','ab8025bff041d6816025d2457dc12f9d5fa4e6072d399a8b8767d16bcbb2faf9',False),
 ('Norm38MacroPrefixQNCarry','/tmp/nine-seed38-jones-prefix-group05-check-20261106/lib/DiophantineConsistency','bd2995f482e56f212b821cb5ced4a9f660119720e20a57cb71aeedf9294c194c',True),
 ('Norm38MacroDependentY','/tmp/nine-seed38-jones-dependent01-staged-check-20261106/lib/DiophantineConsistency','eb28e13077c175963702682ff8501cb25c4036813d5d035c3574a9e605f516a9',True)]
selected={}
for n,root,h,route in providers:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or sha(p)!=h:raise RuntimeError(('provider',n))
 if route and (not q.is_file() or q.resolve()!=p.resolve() or sha(q)!=h):raise RuntimeError(('route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'shared_overlay_paths':len(by),'scope':'Six audited checkpoint/U-Y providers and overlay comparison; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
