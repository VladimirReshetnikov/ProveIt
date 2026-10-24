#!/usr/bin/env python3
"""Pointwise ring-identity transport contraction for three frozen equations."""
from pathlib import Path
import json, hashlib, collections
class Poly:
 def __init__(self,terms=0):
  self.terms=terms if isinstance(terms,dict)else({():terms}if terms else{})
 def __add__(self,b):
  b=b if isinstance(b,Poly)else Poly(b);r=dict(self.terms)
  for k,v in b.terms.items():r[k]=r.get(k,0)+v
  return Poly({k:v for k,v in r.items()if v})
 __radd__=__add__
 def __neg__(self):return Poly({k:-v for k,v in self.terms.items()})
 def __sub__(self,b):return self+-b if isinstance(b,Poly)else self+(-b)
 def __rsub__(self,b):return -self+b
 def __mul__(self,b):
  b=b if isinstance(b,Poly)else Poly(b);r={}
  for k,u in self.terms.items():
   for l,v in b.terms.items():
    m=tuple(sorted(k+l));r[m]=r.get(m,0)+u*v
  return Poly({k:v for k,v in r.items()if v})
 __rmul__=__mul__
def variables(names):return [Poly({(n,):1})for n in names.split()]
HERE=Path(__file__).resolve().parent
ROOT=HERE/'parents'
OUT=HERE/'circuits'
OUT.mkdir(exist_ok=True)
SOURCES={
 'positive10_98_degree368':ROOT/'candidates/ten-positive-zero-offset/equation.json',
 'positive12_95_degree70':ROOT/'candidates/free-j-polarized-positive/equation.json',
 'positive13_87_degree51':ROOT/'candidates/free-j-polarized-positive/source/positive/p13_free_J.json',
}
def require(p,m):
 if not p:raise RuntimeError(m)
def metrics(obj):
 known=set(obj['witnesses']+obj['fixed_numerals']);deps={};dg={x:1 for x in obj['witnesses']};dg.update({x:0 for x in obj['fixed_numerals']})
 for n,op,a,b in obj['source']:
  require(n not in known and op in '+-*','fresh row '+n)
  require(all(isinstance(x,int)or x in known for x in (a,b)),'topology '+n)
  da,db=(0 if isinstance(x,int)else dg[x] for x in (a,b))
  dg[n]=da+db if op=='*'else max(da,db);known.add(n);deps[n]=(a,b)
 live=set();todo=[obj['output']]
 while todo:
  x=todo.pop()
  if isinstance(x,int)or x in live:continue
  live.add(x);todo.extend(deps.get(x,()))
 require(live==known,'all nodes/inputs/ports live: '+str(known-live))
 return {'operations':len(obj['source']),'operation_breakdown':dict(collections.Counter(r[1] for r in obj['source'])),'syntactic_degree':dg[obj['output']]}
def evaluate(obj,vals,mod):
 env=dict(vals)
 for n,op,a,b in obj['source']:
  a=a if isinstance(a,int)else env[a];b=b if isinstance(b,int)else env[b]
  env[n]=(a+b if op=='+'else a-b if op=='-'else a*b)%mod
 return env[obj['output']]
def main():
 receipts=[]
 # Universal scalar identity; no root, integrality, or positivity assumption.
 h,n,v,k,p,q,u,y,b,e,l=variables('h n v k p q u y b e l')
 old=(p*q)*u*(h*(n+v)+k)+h*(u*(q*y-p*(1+q*l)*b)-(p*q)*e)
 new=(p*q)*u*(h*(n+v-l*b)+k)+h*(u*(q*y-p*b)-(p*q)*e)
 require(not (old-new).terms,'full ten-variable center identity')
 a,r=variables('a r')
 old2=(p*q)*(a+l+r)+q*y-p*(1+q*l)*b
 new2=(p*q)*(a+l+r-l*b)+q*y-p*b
 require(not (old2-new2).terms,'full ordinary center identity')
 for name,path in SOURCES.items():
  raw=path.read_bytes();old=json.loads(raw);new=dict(old);rows=[];deleted=[];changed=[]
  isten=name.startswith('positive10')
  for row in old['source']:
   n,op,a,b=row
   if isten:
    if n in ['qm1L','W','WBt','q3WBt']:
     deleted.append(row);continue
    if n=='nV':
     rows.append(['folded_LBt','*','L','Bt']);rows.append(row);rows.append(['folded_nV','-','nV','folded_LBt']);continue
    if n=='Hn':
     nr=['Hn','*','Hp','folded_nV'];changed.append({'old':row,'new':nr});rows.append(nr);continue
    if n=='inner':
     rows.append(['folded_q3Bt','*','q3','Bt']);nr=['inner','-','qm1Y','folded_q3Bt'];changed.append({'old':row,'new':nr});rows.append(nr);continue
   else:
    if n in ['g22','W','g35','g36']:
     deleted.append(row);continue
    if n=='g31':
     rows.append(row);rows.append(['folded_kBt','*','k','Bt']);rows.append(['folded_g31','-','g31','folded_kBt']);continue
    if n=='g32':
     nr=['g32','*','M','folded_g31'];changed.append({'old':row,'new':nr});rows.append(nr);continue
    if n=='Z':
     rows.append(['folded_q3Bt','*','q3','Bt']);nr=['Z','-','g34','folded_q3Bt'];changed.append({'old':row,'new':nr});rows.append(nr);continue
   rows.append(row)
  new['source']=rows;new['name']=name;new.update(metrics(new));require(new['operations']==old['operations']-1,'strict gate reduction')
  new['coefficient_binding']='../coefficients/BINDING.json'
  new['proof']='../REPORT_SECTION.tex'
  new['parent_sha256']=hashlib.sha256(raw).hexdigest();new['status']='Identical polynomial by the universal affine-carrier contraction; exact degree and full zero set inherited pointwise.'
  new.pop('register_degrees',None)
  # Supplementary signed-domain controls only, not a proof of identity.
  import random
  rng=random.Random(8473)
  for prime in [1009,10007,1000003]:
   for trial in range(128):
    vals={x:rng.randrange(-2*prime,2*prime) for x in old['witnesses']+old['fixed_numerals']}
    require(evaluate(old,vals,prime)==evaluate(new,vals,prime),'complete modular control')
  target=OUT/(name+'.json');target.write_text(json.dumps(new,indent=2)+'\n')
  receipts.append({'name':name,'source':str(path.relative_to(ROOT)),'parent_sha256':hashlib.sha256(raw).hexdigest(),'child_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'metrics':metrics(new),'exact_degree':old['exact_degree'],'deleted':deleted,'changed':changed,'supplementary_evaluations':384})
 (OUT/'FOLD_TRANSPORT_CHECK.json').write_text(json.dumps({'universal_ring_identities':'PASS','receipts':receipts},indent=2)+'\n')
 print(json.dumps(receipts,indent=2))
if __name__=='__main__':main()
