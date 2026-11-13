#!/usr/bin/env python3
"""Produce source-pinned 27-witness seed by normalizing a positive norm root."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;src=P.parent/'nine-sharing-sign28-sextic-candidate/seed.json';raw=src.read_bytes();digest=hashlib.sha256(raw).hexdigest();assert digest=='b5ea881fefc64c14dafa59c8639a0786224e81b75bb2517eccb1e0021fbb10aa';old=json.loads(raw);assert old['witness_count']==28 and len(old['residuals'])==19
root=['add',['var',21],['num',1]];product=['mul',['var',21],['add',['var',21],['num',2]]]
row,= [r for r in old['residuals'] if r['gate']=='N1'];assert row['kind']=='norm' and row['expr']==['sub',['sub',['mul',['var',21],['var',21]],['var',22]],['num',1]]
def transform(t):
 op=t[0]
 if op=='var':
  i=t[1];assert type(i)==int and 0<=i<=28
  if i==21:return root
  if i==22:return product
  return ['var',i-(i>22)]
 if op in ('num','port'):return t[:]
 assert op in ('add','sub','mul') and len(t)==3
 return [op,transform(t[1]),transform(t[2])]
rows=[dict(r,expr=transform(r['expr'])) for r in old['residuals'] if r['gate']!='N1'];assert len(rows)==18
out={'schema':'sharing-sextic-positive-root-normalized-v1','source':'../nine-sharing-sign28-sextic-candidate/seed.json','source_sha256':digest,'witness_count':27,'total_coordinates':28,'distinguished_input_coordinate':0,'removed_norm':'N1','old_root_coordinate':21,'old_product_coordinate':22,'new_predecessor_coordinate':21,'old_root_as_new':root,'old_product_as_new':product,'fixed_ports':old['fixed_ports'],'coefficient_binding':old['coefficient_binding'],'residuals':rows,'output':'sum of squares of the 18 displayed residuals','status':'external candidate; natural predecessor and model embedding bridge unproved'}
encoded=(json.dumps(out,indent=2,sort_keys=True)+'\n').encode();target=P/'seed.json'
if sys.argv[1:]==['--write']:
 with target.open('xb') as f:f.write(encoded)
elif sys.argv[1:]==['--check']:
 assert target.read_bytes()==encoded;print(json.dumps({'status':'PASS_REPRODUCIBLE_AST_ONLY','sha256':hashlib.sha256(encoded).hexdigest()},sort_keys=True))
else:raise SystemExit('expected --write or --check')
