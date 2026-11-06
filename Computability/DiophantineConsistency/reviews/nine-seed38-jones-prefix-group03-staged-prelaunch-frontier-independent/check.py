#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-group03-staged-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'8baf76c23077a34e1f676ffc656d9774953f0342152770ef112ed87094fbc641','provider_preflight.py':'8fde8d67cfc730b392e807da46d00ab3346fb1eb10d0f5649d07ae8d00e0cf10','source-manifest.json':'778241db0870370dacc27379edcaf80035c402b52a16b69a9a38aa7f2bd4b66b'}.items():assert h(p/n)==v
rows=json.loads((p/'source-manifest.json').read_text())['rows']
expected=[('Norm38MacroPrefixCarry03','22dc3497bf7c376eb505518e806bec65e98168a77d5185b3f1f331ad192de7ec','Norm38MacroPrefixCarry',['d8_B','d9_B','d9_b']),('Norm38MacroPrefixGsmall','a952cf020ba61703f20922f5633b1d3f6fc37d4919f2bfe3933d39b0416bf818','Norm38MacroPrefixCarry03',['prefix_g']),('Norm38MacroPrefixTheta','32d162df0a5e6a627b3a2b1f98630a3411bef3f2183cc9974d9687a2f29df5c2','Norm38MacroPrefixCarry03',['prefix_theta']),('Norm38MacroPrefixGlarge','ba80ac2963ba65d8014661cc49f485deed735f772b1cde3fb6906da1ee302653','Norm38MacroPrefixCarry03',['prefix_G'])]
assert len(rows)==len(expected)
for row,(n,sha,imp,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';assert h(q)==sha==row['source_sha256'];s=q.read_text();assert row['module']=='DiophantineConsistency.'+n;assert row['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+imp];assert re.findall(r'^theorem (\w+)',s,re.M)==ts;assert re.findall(r'^#print axioms (\w+)',s,re.M)==ts
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==4
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled symbolic short-prefix statements; no Lean replay'},sort_keys=True,indent=2))
