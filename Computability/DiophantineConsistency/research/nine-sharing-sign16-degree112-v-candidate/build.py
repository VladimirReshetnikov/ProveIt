#!/usr/bin/env python3
"""Draft conditional signed V elimination from the external sign17 seed."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;source=here.parent/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json';raw=source.read_bytes();pin='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';assert hashlib.sha256(raw).hexdigest()==pin;seed=json.loads(raw);row,=[r for r in seed['residuals'] if r['gate']=='V'];assert row['expr'][:2]==['sub',['var',17]];rhs=row['expr'][2]
def subst(t):
 if t[0]=='var':return subst(rhs) if t[1]==17 else ['var',t[1]-(t[1]>17)]
 if t[0] in ('num','port'):return t[:]
 assert t[0] in ('add','sub','mul') and len(t)==3
 return [t[0],subst(t[1]),subst(t[2])]
out={'schema':'sign16_degree112_v_candidate_v1','status':'external conditional source-only candidate; nonnegative lift unproved','source':'../nine-sharing-sign17-degree96-vdifference-candidate/seed.json','source_sha256':pin,'coefficient_binding':seed['coefficient_binding'],'fixed_ports':seed['fixed_ports'],'distinguished_input_coordinate':0,'total_coordinates':17,'witness_count':16,'removed_old_coordinate':17,'removed_gate':'V','lift_expression':subst(rhs),'output':'sum of squares of the 7 displayed residuals','residuals':[dict(r,expr=subst(r['expr'])) for r in seed['residuals'] if r['gate']!='V']};encoded=json.dumps(out,indent=2,sort_keys=True)+'\n';target=here/'seed.json'
if sys.argv[1:]==['--write']:
 if target.exists():raise SystemExit('refusing to overwrite seed')
 target.write_text(encoded)
elif sys.argv[1:]==['--check']:
 assert target.read_text()==encoded;print(json.dumps({'status':'PASS','seed_sha256':hashlib.sha256(encoded.encode()).hexdigest()},sort_keys=True))
else:raise SystemExit('use --write or --check')
