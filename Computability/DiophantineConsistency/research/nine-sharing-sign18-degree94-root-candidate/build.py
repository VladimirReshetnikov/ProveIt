#!/usr/bin/env python3
"""Eliminate positive main-root coordinate from the external sign19 seed."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;source=here.parent/'nine-sharing-sign19-degree44-y-candidate/seed.json';raw=source.read_bytes();pin='01bae1f7680ce07eb5c041d5ae6a625ead9e79e1c968472521458475a4eb94f1';assert hashlib.sha256(raw).hexdigest()==pin;seed=json.loads(raw);row,=[r for r in seed['residuals'] if r['gate']=='main_root'];assert row['kind']=='positive';lhs,rhs=row['expr'][1:];assert lhs==['add',['var',15],['num',1]] and row['expr'][0]=='sub';first,second,third=rhs[1][1],rhs[1][2],rhs[2];A=first[2];assert first==['mul',['add',['var',9],['num',1]],A] and A==['add',['mul',['port','beta'],['add',['var',1],['num',1]]],['num',1]];replacement=['add',['add',['add',['mul',['var',9],A],A[1]],second],third]
def subst(t):
 op=t[0]
 if op=='var':return subst(replacement) if t[1]==15 else ['var',t[1]-(t[1]>15)]
 if op in ('num','port'):return t[:]
 assert op in ('add','sub','mul') and len(t)==3
 return [op,subst(t[1]),subst(t[2])]
out={'schema':'sign18_degree94_root_candidate_v1','status':'external source-only candidate; no Lean bridge or endpoint','source':'../nine-sharing-sign19-degree44-y-candidate/seed.json','source_sha256':pin,'coefficient_binding':seed['coefficient_binding'],'fixed_ports':seed['fixed_ports'],'distinguished_input_coordinate':0,'total_coordinates':19,'witness_count':18,'removed_old_coordinate':15,'removed_gate':'main_root','lift_expression':subst(replacement),'output':'sum of squares of the 9 displayed residuals','residuals':[dict(r,expr=subst(r['expr'])) for r in seed['residuals'] if r['gate']!='main_root']};encoded=json.dumps(out,indent=2,sort_keys=True)+'\n';target=here/'seed.json'
if sys.argv[1:]==['--write']:
 if target.exists():raise SystemExit('refusing to overwrite seed')
 target.write_text(encoded)
elif sys.argv[1:]==['--check']:
 assert target.read_text()==encoded;print(json.dumps({'status':'PASS','seed_sha256':hashlib.sha256(encoded.encode()).hexdigest()},sort_keys=True))
else:raise SystemExit('use --write or --check')
