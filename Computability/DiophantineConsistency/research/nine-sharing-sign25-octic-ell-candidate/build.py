#!/usr/bin/env python3
"""Generate a 25-witness seed by substituting ell = v17*v18."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
p=Path(__file__).resolve().parent;source=p.parent/'nine-sharing-sign26-sextic-gap-congruence-candidate/seed.json';raw=source.read_bytes();pin='36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25'
if hashlib.sha256(raw).hexdigest()!=pin:raise SystemExit('source pin mismatch')
s=json.loads(raw)
def subst(t):
 if not isinstance(t,list) or not t:raise ValueError('invalid AST')
 if t[0]=='var' and len(t)==2:
  i=t[1]
  if i==19:return ['mul',['var',17],['var',18]]
  return ['var',i if i<19 else i-1]
 if t[0] in ('num','port') and len(t)==2:return t[:]
 if t[0] in ('add','sub','mul') and len(t)==3:return [t[0],subst(t[1]),subst(t[2])]
 raise ValueError('unknown AST')
rows=s['residuals'];matches=[r for r in rows if r['gate']=='ell']
if len(matches)!=1 or matches[0]['expr']!=['sub',['var',19],['mul',['var',17],['var',18]]]:raise ValueError('ell head mismatch')
out={'schema':'sign25_octic_ell_candidate_v1','status':'external source-only candidate; no Lean bridge or endpoint','source':'../nine-sharing-sign26-sextic-gap-congruence-candidate/seed.json','source_sha256':pin,'coefficient_binding':s['coefficient_binding'],'fixed_ports':s['fixed_ports'],'distinguished_input_coordinate':0,'total_coordinates':26,'witness_count':25,'removed_old_coordinate':19,'removed_gate':'ell','lift_expression':['mul',['var',17],['var',18]],'output':'sum of squares of the 16 displayed residuals','residuals':[dict(r,expr=subst(r['expr'])) for r in rows if r['gate']!='ell']}
encoded=json.dumps(out,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
 target=p/'seed.json'
 if target.exists():raise SystemExit('refusing to overwrite seed')
 target.write_text(encoded)
elif sys.argv[1:]==['--check']:
 if (p/'seed.json').read_text()!=encoded:raise SystemExit('seed mismatch')
 print(json.dumps({'status':'PASS','seed_sha256':hashlib.sha256(encoded.encode()).hexdigest()},sort_keys=True))
else:raise SystemExit('use --write or --check')
