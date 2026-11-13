#!/usr/bin/env python3
"""Draft conditional signed inner-coordinate elimination from the external sign16 seed."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;source=here.parent/'nine-sharing-sign16-degree112-v-candidate/seed.json';raw=source.read_bytes();pin='564ac66abad0fb5e286e5c0c05b5c3cbd05de13e68c9c9ac0b7c3a20a0c0b624';assert hashlib.sha256(raw).hexdigest()==pin;seed=json.loads(raw);row,=[r for r in seed['residuals'] if r['gate']=='cTminusR'];assert row['expr'][:2]==['sub',['var',16]];rhs=row['expr'][2]
def subst(t):
 if t[0]=='var':return subst(rhs) if t[1]==16 else ['var',t[1]-(t[1]>16)]
 if t[0] in ('num','port'):return t[:]
 assert t[0] in ('add','sub','mul') and len(t)==3
 return [t[0],subst(t[1]),subst(t[2])]
out={'schema':'sign15_inner_candidate_v1','status':'external conditional source-only candidate; noncircular nonnegative lift unproved','source':'../nine-sharing-sign16-degree112-v-candidate/seed.json','source_sha256':pin,'coefficient_binding':seed['coefficient_binding'],'fixed_ports':seed['fixed_ports'],'distinguished_input_coordinate':0,'total_coordinates':16,'witness_count':15,'removed_old_coordinate':16,'removed_gate':'cTminusR','lift_expression':subst(rhs),'output':'sum of squares of the 6 displayed residuals','residuals':[dict(r,expr=subst(r['expr'])) for r in seed['residuals'] if r['gate']!='cTminusR']};encoded=json.dumps(out,indent=2,sort_keys=True)+'\n';target=here/'seed.json'
if sys.argv[1:]==['--write']:
 if target.exists():raise SystemExit('refusing to overwrite seed')
 target.write_text(encoded)
elif sys.argv[1:]==['--check']:
 assert target.read_text()==encoded;print(json.dumps({'status':'PASS','seed_sha256':hashlib.sha256(encoded.encode()).hexdigest()},sort_keys=True))
else:raise SystemExit('use --write or --check')
