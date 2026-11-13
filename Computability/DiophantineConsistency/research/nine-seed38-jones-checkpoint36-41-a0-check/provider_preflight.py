#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-checkpoint22-23-pk-terminal-frontier-independent', '8924f7c34660a09962a4736b31ba27bf93d448ccc8b719a17ca8b892217ec5f7', '950750403ea5325d5876eb2bc3765b11fa197de67f6795ebe9ff65d8a21a487c'), ('nine-seed38-jones-dependent07-staged-terminal-frontier-independent', '3131f0ac15437151abbf12ec026b35630df58542d0b1d4f4f63dc3dc14f169a8', '6dea09a5229acfc79d3dc1afa8380370ae173632b4cbde02acec4e12e452b3f9')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint36-41-a0-draft'
for n,h in [('Norm38MacroPKPaths', '46c57452feae35e9c7f7d515778c22ad229c47aef1dbe9ffb6560b18a0cbd1c4'), ('Norm38MacroA0Value', '2d3c033a4407197c7692d680414292ff4d91025a600c50bea098b83c5e4db9e4'), ('Norm38MacroA0Path', '49344aea80f0f8d8bfe75c6aca4f8e9af5936ee8dc0be16852f107f3aa00d932')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint22-23-pk-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroKValue', '/tmp/nine-seed38-jones-checkpoint22-23-pk-check-20261106/lib/DiophantineConsistency', '27e93856b14ee56444fd9ec4aed38eec3179043737f5e483f60824677a47c5dd'), ('Norm38MacroDependentA0', '/tmp/nine-seed38-jones-dependent07-staged-check-20261106/lib/DiophantineConsistency', 'eff7a82240baac63d26df27eb612b3c1104971b0540666aa076855cd8890a9d4')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Two audited P/K and A0-node producers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
