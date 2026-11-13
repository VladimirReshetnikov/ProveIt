#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-checkpoint40-41-bdcd-terminal-frontier-independent', '78052d5b19a1d7906cf396ada47dbc6d4fc9589f4caf454d9eb8e0a1b416a657', '45899b6f0ad60b7e117d28d04f2c5507f29d4c11ba76c32c374de06e0a1e986e'), ('nine-seed38-jones-checkpoint41-45-terminal-frontier-independent', 'a54ac0ebb0ad366984dbf17127ec731fc24cb2d273a3379c0082671efd4dde45', 'e1c9bfd226f3b93e3deeb7893db3e93f48085a9a36676e3273891873a217e76a'), ('nine-seed38-jones-dependent08-staged-terminal-frontier-independent', 'c9093ca2c52b810bf0f2d878bb513aa54502b0b2fa13146b11e4e35fbf62d26e', 'f59e7238d645a2eebab7b13fd342d5a1045ea3b53331e7e40620b2223407678c')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint42-dm-draft'
for n,h in [('Norm38MacroDmInputs', '06d62b29d3c043dab0b50c94953774d5a53358af62709c09100748533f86dfca'), ('Norm38MacroDmValue', 'f10360f9d27362cfb8c4ae8c0f17f760c6e1316084508862af01607f982b1e9b')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint40-41-bdcd-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroCdValue', '/tmp/nine-seed38-jones-checkpoint40-41-bdcd-check-20261106/lib/DiophantineConsistency', '6d243292a8fca880882143a751e5daadb0cdfcc334a60ba880481c42f67325e2'), ('Norm38MacroCheckpoint41to45', '/tmp/nine-seed38-jones-checkpoint41-45-check-20261106/lib/DiophantineConsistency', 'd0dc8713317ad6f6b829c3776d740169273d9abecbf5a344489c148fb04cb565'), ('Norm38MacroDependentDmKc', '/tmp/nine-seed38-jones-dependent08-staged-check-20261106/lib/DiophantineConsistency', '9c6fa4a8df1d1376528fb8ae07ed1648572cf9e0534bb4d2d6cfc897cb157e59')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Three audited Bd/Cd, g/G and Dm-node producers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
