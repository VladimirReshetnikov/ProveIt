"""Independent DAG census and exact signed leading-monomial audit. No generator imports."""
import json,hashlib
from pathlib import Path
P=Path(__file__).resolve().parents[1]; L=5**32

def heads(d):
 out=[]
 for node in d['nodes']:
  k=node['kind']
  if k=='literal':v=(0,node['value'],0,False)
  elif k=='variable':v=(1,1,0,False)
  elif k=='fixed':v=(0,1,int(node['name']=='b_floor_odd'),node['name']!='b_floor_odd')
  else:
   a,b=out[node['left']],out[node['right']]
   if a is None or b is None:v=None
   elif k=='mul':v=(a[0]+b[0],a[1]*b[1],a[2]+b[2],a[3] or b[3]) if a[1] and b[1] else (0,0,0,False)
   else:
    if k=='sub':b=(b[0],-b[1],b[2],b[3])
    if not a[1]:v=b
    elif not b[1]:v=a
    elif a[0]!=b[0]:v=max((a,b),key=lambda x:x[0])
    elif a[2]!=b[2]:v=None
    else:v=(a[0],a[1]+b[1],a[2],a[3] or b[3]) if a[1]+b[1] else None
  out.append(v)
 return out

def census(d):
 seen=set();todo=[d['output']]
 while todo:
  i=todo.pop()
  if i in seen:continue
  seen.add(i); n=d['nodes'][i]
  if n['kind'] in ('add','sub','mul'):todo.extend([n['left'],n['right']])
 counts={k:sum(d['nodes'][i]['kind']==k for i in seen) for k in ('add','sub','mul','variable','fixed')}
 assert {k:counts[k] for k in ('add','sub','mul')}==d['operation_counts']
 return counts

r={}
for name,degree,coef,bexp,vc,oc in [('signed14',813056*L+2152,2**832*12**120,406528*L+8,14,1586),('signed15_linear',406528*L+2528,2**832*12**248,0,15,1594)]:
 f=P/'integers'/(name+'.json');d=json.loads(f.read_text()); hs=heads(d); h=hs[d['output']]
 assert h==(degree,coef,bexp,False),(name,h)
 cnt=census(d);assert cnt['variable']==vc and sum(cnt[k] for k in ('add','sub','mul'))==oc
 r[name]={'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'counts':cnt,'degree':degree,'coefficient_integer_factor':coef,'coefficient_Bodd_exponent':bexp,'fixed_index_independent':True}
for name,oc in [('nine31_signed_quadratic',1559),('nine31_signed_quadratic_positive',1554)]:
 f=P/'nine'/(name+'.json');d=json.loads(f.read_text());cnt=census(d);assert cnt['variable']==9 and sum(cnt[k] for k in ('add','sub','mul'))==oc
 r[name]={'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'counts':cnt}
(P/'audit'/'FINAL_CIRCUIT_CHECKS.json').write_text(json.dumps(r,indent=2)+'\n')
print('PASS: exact signed leading monomials, variable counts and all four live operation counts.')
