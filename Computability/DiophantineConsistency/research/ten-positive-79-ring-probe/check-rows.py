#!/usr/bin/env python3
"""Read-only exact comparison of the 79 Lean syntax with the candidate DAG."""
from hashlib import sha256
from pathlib import Path
import json,re
H=Path(__file__).resolve().parent;D=H.parents[1];SRC=H/'MaskCoordinate79.lean'
GRAPH=D/'research/ten-positive-79-mask-coordinate-probe/candidate.json'
PINS={SRC:'d017edeccda26a8c605dd0da90d99ea599b5bcb47d32b19f977818ab689d4b9d',GRAPH:'5389bb9386371ca71790c5bbac3e5307f4b15ee278e560c13089d65f3ea25d00'}
def sha(p):return sha256(p.read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
x=json.loads(GRAPH.read_text());source=SRC.read_text().split('def output79 ',1)[1].split('\nvariable {R',1)[0]
vars=re.findall(r'^  let (\w+) : Expr \(Fin 10\) := \.var (\d+)$',source,re.M)
ports=re.findall(r'^  let (port\d) : Expr \(Fin 10\) := \.constant \(p (\d+)\)$',source,re.M)
need(vars==[(n,str(i)) for i,n in enumerate(x['witnesses'])],'variable slots')
need(ports==[(f'port{i}',str(i)) for i in range(4)],'port slots')
found=re.findall(r'^  let (r\d{2}) := (\w+) ([+*\-]) (\w+)$',source,re.M)
need(len(found)==len(x['source'])==79,'row count')
refs={n:n for n in x['witnesses']};refs.update({n:f'port{i}' for i,n in enumerate(x['fixed_numerals'])})
for i,((name,op,a,b),(rn,la,lop,lb)) in enumerate(zip(x['source'],found),1):
 def conv(v):return str(v) if isinstance(v,int) else refs[v]
 need((rn,la,lop,lb)==(f'r{i:02}',conv(a),op,conv(b)),'row mismatch '+str(i));refs[name]=rn
need(refs[x['output']]=='r79' and source.rstrip().endswith('r79'),'output slot')
for p,h in PINS.items():need(sha(p)==h,'input changed after scan '+str(p))
print(json.dumps({'status':'PASS','rows':79,'lean_sha256':sha(SRC),'candidate_sha256':sha(GRAPH),
 'scope':'external exact Lean syntax/JSON comparison; no positivity or file theorem'},sort_keys=True))
