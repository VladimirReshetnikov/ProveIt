#!/usr/bin/env python3
"""Build conditional signed-elimination candidate; no Lean/model proof."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent
old_path=here.parent/'nine-sharing-sign18-degree94-root-candidate/seed.json'
raw=old_path.read_bytes();assert hashlib.sha256(raw).hexdigest()=='d3fd0a00ed9f803a5c002481dbfb22aafe9a5ba34ac89c90069cefbdcaada3fb'
old=json.loads(raw);assert old['witness_count']==18 and old['total_coordinates']==19
row,=[r for r in old['residuals'] if r['gate']=='V2minusY2']
f=['add',['var',13],['num',1]];v=['var',17]
difference=['sub',['mul',f,f],['mul',v,v]]
assert row['kind']=='signed' and row['expr']==['sub',['var',18],difference]
def subst(e):
 op=e[0]
 if op=='var':
  i=e[1];assert 0<=i<=18
  return difference if i==18 else ['var',i]
 if op in ('num','port'):return e[:]
 assert op in ('add','sub','mul') and len(e)==3
 return [op,subst(e[1]),subst(e[2])]
res=[]
for r in old['residuals']:
 if r['gate']=='V2minusY2':continue
 res.append({**r,'expr':subst(r['expr'])})
new={'schema':'sign17_degree96_vdifference_candidate_v1','source':'../nine-sharing-sign18-degree94-root-candidate/seed.json',
     'source_sha256':hashlib.sha256(raw).hexdigest(),'status':'external candidate; conditional signed lift not formalized',
     'witness_count':17,'total_coordinates':18,'distinguished_input_coordinate':0,
     'fixed_ports':old['fixed_ports'],'coefficient_binding':old['coefficient_binding'],
     'removed_gate':'V2minusY2','removed_old_coordinate':18,'lift_expression':difference,
     'output':'sum of squares of the 8 displayed residuals','residuals':res}
data=(json.dumps(new,indent=2,ensure_ascii=False)+'\n').encode();target=here/'seed.json'
if sys.argv[1:]==['--write']:
 assert not target.exists(),'refusing to overwrite';target.write_bytes(data)
elif sys.argv[1:]==['--check']:
 assert target.read_bytes()==data
else:raise SystemExit('expected --write or --check')
print(json.dumps({'status':'PASS_BUILD','sha256':hashlib.sha256(data).hexdigest(),'scope':'external AST only'},sort_keys=True))
