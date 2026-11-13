#!/usr/bin/env python3
"""Extract a pinned residual/port/index inventory; no Lean proof."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];f=D/'research/nine-sharing-quartic65-sign33-candidate/seed.json';raw=f.read_bytes();assert hashlib.sha256(raw).hexdigest()=='a8cd4d01962b9380065ebbd3d7b75db3ffcadf18969099398bd151c4e2219e75';d=json.loads(raw);assert d['coordinate_count']==34 and d['jones_witness_count']==33 and len(d['residuals'])==24
rows=[]
def walk(t,p,v):
 k=t[0]
 if k=='port':p.add(t[1])
 elif k=='var':v.add(t[1])
 elif k in ('add','sub','mul'):walk(t[1],p,v);walk(t[2],p,v)
 else:assert k=='num'
for j,r in enumerate(d['residuals']):
 p=set();v=set();walk(r['expr'],p,v);assert 0 not in v and all(1<=x<=33 for x in v)
 rows.append({'residual_index':j,'gate':r['gate'],'kind':r['kind'],'ports':sorted(p),'full_fin34_indices':sorted(v)})
assert [r['kind'] for r in rows].count('positive')==14 and [r['kind'] for r in rows].count('signed')==5 and [r['kind'] for r in rows].count('norm')==5
cuts={g['name']:{'full_fin34_index':g.get('positive_coordinate',g.get('sign_coordinate')),'orientation':g.get('sign',1)} for g in d['gate_records'] if g['kind']=='materialized'}
assert len(cuts)==19 and cuts['gap']=={'full_fin34_index':26,'orientation':1} and cuts['V2minusY2']=={'full_fin34_index':33,'orientation':-1}
print(json.dumps({'status':'PASS_EXTERNAL_RESIDUAL_INVENTORY','seed_sha256':hashlib.sha256(raw).hexdigest(),'rows':rows,'materialized_cuts':cuts,'scope':'External candidate inventory only; no Lean residual identity, source graph bridge, witness construction or iPRA endpoint.'},indent=2,sort_keys=True))
