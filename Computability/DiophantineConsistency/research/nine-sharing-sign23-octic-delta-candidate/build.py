#!/usr/bin/env python3
"""External AST: eliminate Delta from the audited 24-witness octic seed."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
p=Path(__file__).resolve().parent;src=p.parent/'nine-sharing-sign24-octic-q3-candidate/seed.json';raw=src.read_bytes();pin='24a6dcf05b96112cfa332aafe4790a367c44b9a0cc033a74197f92d3520ab865';assert hashlib.sha256(raw).hexdigest()==pin;s=json.loads(raw);rows=s['residuals'];q=[r for r in rows if r['gate']=='Delta'];assert len(q)==1 and q[0]['kind']=='positive' and q[0]['expr'][0:2]==['sub',['var',18]];rhs=q[0]['expr'][2]
def replace(t):
 op=t[0]
 if op=='var':return replace(rhs) if t[1]==18 else ['var',t[1] if t[1]<18 else t[1]-1]
 if op in ('num','port'):return t[:]
 assert op in ('add','sub','mul') and len(t)==3;return [op,replace(t[1]),replace(t[2])]
out={'schema':'sign23_octic_delta_candidate_v1','status':'external source-only candidate; no Lean bridge or endpoint','source':'../nine-sharing-sign24-octic-q3-candidate/seed.json','source_sha256':pin,'coefficient_binding':s['coefficient_binding'],'fixed_ports':s['fixed_ports'],'distinguished_input_coordinate':0,'total_coordinates':24,'witness_count':23,'removed_old_coordinate':18,'removed_gate':'Delta','lift_expression':replace(rhs),'output':'sum of squares of the 14 displayed residuals','residuals':[dict(r,expr=replace(r['expr'])) for r in rows if r['gate']!='Delta']};encoded=json.dumps(out,indent=2,sort_keys=True)+'\n';target=p/'seed.json'
if sys.argv[1:]==['--write']:
 if target.exists():raise SystemExit('refusing to overwrite seed')
 target.write_text(encoded)
elif sys.argv[1:]==['--check']:
 assert target.read_text()==encoded
 print(json.dumps({'status':'PASS','seed_sha256':hashlib.sha256(encoded.encode()).hexdigest()},sort_keys=True))
else:raise SystemExit('use --write or --check')
