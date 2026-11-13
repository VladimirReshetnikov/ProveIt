#!/usr/bin/env python3
"""Remove gap via q³ congruence; external AST candidate only."""
import copy,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;src=P.parent/'nine-sharing-sign27-sextic-normalized-root-candidate/seed.json';raw=src.read_bytes();h=hashlib.sha256(raw).hexdigest();assert h=='5bd7f45de28980c6ac9d3974a0087b1d9f8faf9b060b8a115843ea0cc4adff3d';old=json.loads(raw);assert old['witness_count']==27 and len(old['residuals'])==18
v=lambda i:['var',i];num=lambda i:['num',i];add=lambda x,y:['add',x,y];sub=lambda x,y:['sub',x,y];mul=lambda x,y:['mul',x,y]
a=mul(['port','beta'],add(v(1),num(1)));q=add(a,num(1));n=add(v(2),num(1));t=add(v(3),num(1));g=sub(add(mul(a,q),t),mul(a,n));q2=mul(q,q);q3=mul(q2,q);Q=v(15);replacement=add(mul(sub(a,n),Q),mul(add(n,t),q2));oldprod=mul(v(22),q2)
gap,=[r for r in old['residuals'] if r['gate']=='gap'];assert gap['expr']==sub(v(22),g);assert old['residuals'][0]['gate']=='q3' and old['residuals'][0]['expr']==sub(Q,q3)
counts={'product':0,'bare':0}
def reindex(tree):
 if tree[0]=='var':
  i=tree[1];assert i!=22 and 0<=i<=27;return v(i-(i>22))
 if tree[0] in ('port','num'):return tree[:]
 assert tree[0] in ('add','sub','mul') and len(tree)==3
 return [tree[0],reindex(tree[1]),reindex(tree[2])]
def rewrite(tree):
 if tree==oldprod:counts['product']+=1;return copy.deepcopy(replacement)
 if tree==v(22):counts['bare']+=1;return copy.deepcopy(g)
 if tree[0] in ('var','port','num'):return tree[:]
 return [tree[0],rewrite(tree[1]),rewrite(tree[2])]
rows=[dict(r,expr=reindex(rewrite(r['expr']))) for r in old['residuals'] if r['gate']!='gap'];assert len(rows)==17 and counts=={'product':2,'bare':2}
out={'schema':'sharing-sextic-gap-q3-congruence-v1','source':'../nine-sharing-sign27-sextic-normalized-root-candidate/seed.json','source_sha256':h,'witness_count':26,'total_coordinates':27,'distinguished_input_coordinate':0,'removed_gate':'gap','old_gap_coordinate':22,'reconstructed_gap_before_drop':g,'replaced_gap_times_q_squared_before_drop':replacement,'q3_residual_before_drop':sub(Q,q3),'congruence':'g*q² - replacement = -(a-n)*(Q-q³)','fixed_ports':old['fixed_ports'],'coefficient_binding':old['coefficient_binding'],'residuals':rows,'output':'sum of squares of the 17 displayed residuals','status':'external candidate; q3 congruence and natural gap positivity model bridge unproved'}
encoded=(json.dumps(out,indent=2,sort_keys=True)+'\n').encode();target=P/'seed.json'
if sys.argv[1:]==['--write']:
 with target.open('xb') as f:f.write(encoded)
elif sys.argv[1:]==['--check']:
 assert target.read_bytes()==encoded;print(json.dumps({'status':'PASS_REPRODUCIBLE_AST_ONLY','sha256':hashlib.sha256(encoded).hexdigest()},sort_keys=True))
else:raise SystemExit('expected --write or --check')
