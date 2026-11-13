#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-checkpoint36-41-a0-terminal-frontier-independent', '477cf4e744013a55c9f42e29e063c314be62f8ecc40fd379944c411323a4f3d0', '14167a39297cd9f5e37073d277615b3d6393a70ac201a8e79fc74800958f523e'), ('nine-seed38-jones-dependent07-staged-terminal-frontier-independent', '3131f0ac15437151abbf12ec026b35630df58542d0b1d4f4f63dc3dc14f169a8', '6dea09a5229acfc79d3dc1afa8380370ae173632b4cbde02acec4e12e452b3f9')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint37-41-a1-draft'
for n,h in [('Norm38MacroA1Value', '124f298cb19240027583814ef65f4b721f6fc5378d5b36fa239836fd6cbae9c5'), ('Norm38MacroA1Path', '7660db034acc402ee4e6770ef41ca132c61544eb346010f4ee70cec91fb0b9a0')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint36-41-a0-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroA0Path', '/tmp/nine-seed38-jones-checkpoint36-41-a0-check-20261106/lib/DiophantineConsistency', 'd8915cf6fe8fc9245466662f0d3c6389a0d4141d36af507fa8797d580ff5c043'), ('Norm38MacroDependentA1', '/tmp/nine-seed38-jones-dependent07-staged-check-20261106/lib/DiophantineConsistency', 'ceafb76103e30efb1f9c8a9cb4c57ec2c9d294c5a6c4c6f5b85fb6f1bcc58513')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Two audited A0 and A1-node producers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
