#!/usr/bin/env python3
"""External AST: eliminate q3 from the audited 25-witness octic seed."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
p=Path(__file__).resolve().parent;src=p.parent/'nine-sharing-sign25-octic-ell-candidate/seed.json';raw=src.read_bytes();pin='c95637ae24a57dba0ae1113a8256ed6f12d33f416f035f9cd4f92cffdbf59fc8';assert hashlib.sha256(raw).hexdigest()==pin;s=json.loads(raw);rows=s['residuals'];q=[r for r in rows if r['gate']=='q3'];assert len(q)==1 and q[0]['kind']=='positive' and q[0]['expr'][0:2]==['sub',['var',15]];rhs=q[0]['expr'][2]
def replace(t):
 op=t[0]
 if op=='var':return replace(rhs) if t[1]==15 else ['var',t[1] if t[1]<15 else t[1]-1]
 if op in ('num','port'):return t[:]
 assert op in ('add','sub','mul') and len(t)==3;return [op,replace(t[1]),replace(t[2])]
out={'schema':'sign24_octic_q3_candidate_v1','status':'external source-only candidate; no Lean bridge or endpoint','source':'../nine-sharing-sign25-octic-ell-candidate/seed.json','source_sha256':pin,'coefficient_binding':s['coefficient_binding'],'fixed_ports':s['fixed_ports'],'distinguished_input_coordinate':0,'total_coordinates':25,'witness_count':24,'removed_old_coordinate':15,'removed_gate':'q3','lift_expression':replace(rhs),'output':'sum of squares of the 15 displayed residuals','residuals':[dict(r,expr=replace(r['expr'])) for r in rows if r['gate']!='q3']};encoded=json.dumps(out,indent=2,sort_keys=True)+'\n';target=p/'seed.json'
if sys.argv[1:]==['--write']:
 if target.exists():raise SystemExit('refusing to overwrite seed')
 target.write_text(encoded)
elif sys.argv[1:]==['--check']:
 assert target.read_text()==encoded
 print(json.dumps({'status':'PASS','seed_sha256':hashlib.sha256(encoded.encode()).hexdigest()},sort_keys=True))
else:raise SystemExit('use --write or --check')
