#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-checkpoint31-41-e-retry01-terminal-frontier-independent', 'f738f67d8c50d5954d61f2f17379be8a3423bb1216d2c20363067ece59f08985', 'a4f100a9a81f22b0b4dc963e2d79bcb0b45ff9c2dce164732a9aa2bc465a4a11'), ('nine-seed38-jones-dependent05-staged-terminal-frontier-independent', '4a0b38cafb87dfdbaf3e0aa4c8038f1d0f595992903814632316b4dd80988bed', '032d6f20599ed912ba688e6fbe24697fd7ec8a5742df1b9de9442f2f653b1f44'), ('nine-seed38-jones-checkpoint34-41-terminal-frontier-independent', '0dcf25e14027b11e215e45c105f573e357db9d9e070e9141ea40b5edbdda4282', '840e200729849d89f7be8d82b727dd00dba990998b201885b19ad746ac7e3b7e')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint32-41-f-draft'
for n,h in [('Norm38MacroFValue', 'b31037e2de33c6fd1cd46943c7270ff3c158855670659e7ef250a4a69589140c'), ('Norm38MacroFPath', '1c15372232f2b09fde8e5ed51330557800cd4dfb6c19c0b3f02f3a3adc57d6c3')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint31-41-e-retry01-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroEPath', '/tmp/nine-seed38-jones-checkpoint31-41-e-retry01-20261106/lib/DiophantineConsistency', '87b518d9d42c7ba288eed4b25cc6060a96a47236bfc7441de75240bc1737bb89'), ('Norm38MacroDependentF', '/tmp/nine-seed38-jones-dependent05-staged-check-20261106/lib/DiophantineConsistency', 'a7700d99911c457d906075eccae9433ac825b8b9fc0df269c01bfd66426b2118'), ('Norm38MacroCheckpoint34to41', '/tmp/nine-seed38-jones-checkpoint34-41-check-20261106/lib/DiophantineConsistency', '985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Three audited E/F and checkpoint providers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
