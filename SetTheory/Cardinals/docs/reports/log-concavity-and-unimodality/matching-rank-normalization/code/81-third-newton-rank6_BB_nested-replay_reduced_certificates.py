"""Exact reader replay, without optimizer or producer polynomial routines.

For 130, rebuild the primitive numerator and Rayleigh polynomial from
Boolean assignment counts. For either profile, replay each rational
identity using an ascending sequence of unit translations.
"""
from pathlib import Path
from itertools import combinations_with_replacement
from fractions import Fraction as Q
from collections import Counter
from math import comb,factorial
import json,hashlib,sys,time,ast
ROOT=Path(__file__).resolve().parent;ZERO=(0,)*7;TYPES=(1,2,3,5,6,7)
def add(*ps):
 out={}
 for p in ps:
  for e,c in p.items():out[e]=out.get(e,Q(0))+c
 return {e:c for e,c in out.items() if c}
def scale(p,c):return {e:v*c for e,v in p.items() if v*c}
def mul(p,q):
 out={}
 for e,c in p.items():
  for f,d in q.items():
   v=tuple(a+b for a,b in zip(e,f));out[v]=out.get(v,Q(0))+c*d
 return {e:c for e,c in out.items() if c}
def var(i):
 e=[0]*7;e[i-1]=1;return {tuple(e):Q(1)}
one={ZERO:Q(1)}
def basis(masks):
 states={0}
 for mask in masks:
  nxt=set()
  for st in states:
   for i in range(3):
    if mask>>i&1 and not st>>i&1:nxt.add(st|1<<i)
  states=nxt
 return bool(states)
def choose(i,n):
 out=one
 for j in range(n):out=mul(out,add(var(i),scale(one,-j)))
 return scale(out,Q(1,factorial(n)))
def count_support(size,augment=(),projection=7):
 out={}
 for rows in combinations_with_replacement(TYPES,size):
  if not basis(tuple(x&projection for x in rows)+augment):continue
  term=one
  for i,n in Counter(rows).items():term=mul(term,choose(i,n))
  out=add(out,term)
 return out
def translate(poly,indices):
 out=poly
 for i in sorted(indices):
  nxt={}
  for e,c in out.items():
   for j in range(e[i-1]+1):
    f=list(e);f[i-1]=j;f=tuple(f);nxt[f]=nxt.get(f,Q(0))+c*comb(e[i-1],j)
  out={e:c for e,c in nxt.items() if c}
 return out
def payload(p):return json.dumps([[list(e),str(c)] for e,c in sorted(p.items()) if c],separators=(',',':'))
def need(cond,msg):
 if not cond:raise RuntimeError(msg)
p=count_support(2,projection=3);q=count_support(3);h=count_support(2,(3,));k=count_support(2,(2,))
n=add(*(var(i) for i in (1,3,5,7)));b=add(var(2),var(6));m=add(n,b);z=add(var(5),var(6),var(7));K=add(mul(p,h),scale(mul(m,q),-1));ray=scale(K,12)
# Shared Rayleigh certificate, independently reconstructed.
minor=add(mul(var(2),var(5)),scale(mul(var(1),var(6)),-1));base=add(ray,scale(mul(minor,minor),-6));bases=[v for v in combinations_with_replacement(TYPES,2) if basis(tuple(x&3 for x in v))]
need(len(bases)==15,'basis coverage');soscount=0
for bs in bases:
 rr=translate(base,bs);need(all(c>=0 for c in rr.values()),('Rayleigh SOS',bs));soscount+=len(rr)
name=sys.argv[1] if len(sys.argv)>1 else '130';data=json.loads((ROOT/f'reduced_{name}_target.json').read_text());P={tuple(e):Q(c) for e,c in data['coefficients']}
if name=='130':
 gamma=add(scale(mul(b,n),4),mul(b,p),scale(mul(n,n),2),scale(mul(n,p),2),mul(p,p),scale(p,-3))
 l=add(b,scale(n,2),p);linear=add(mul(n,h),mul(b,k),scale(mul(p,z),-1),mul(l,q))
 f=add(mul(gamma,add(scale(mul(add(q,h),add(q,k)),2),scale(mul(k,k),-1))),scale(mul(linear,linear),-2))
 need(P==scale(f,144),'fresh compact numerator')
if name=='170':
 # Independently compose the fresh matrix's formal numerator from these
 # Boolean-count polynomials; no producer expression/composition routine.
 data_expr=json.loads((ROOT/'aggregate_170.json').read_text())
 env=dict(n=n,b=b,p=p,q=q,h=h,k=k,z=z)
 cache={}
 def evaluate(node):
  key=ast.dump(node)
  if key in cache:return cache[key]
  if isinstance(node,ast.Name):v=env[node.id]
  elif isinstance(node,ast.Constant):v=scale(one,Q(node.value))
  elif isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):v=scale(evaluate(node.operand),-1)
  elif isinstance(node,ast.BinOp):
   if isinstance(node.op,ast.Add):v=add(evaluate(node.left),evaluate(node.right))
   elif isinstance(node.op,ast.Sub):v=add(evaluate(node.left),scale(evaluate(node.right),-1))
   elif isinstance(node.op,ast.Mult):v=mul(evaluate(node.left),evaluate(node.right))
   elif isinstance(node.op,ast.Pow):
    need(isinstance(node.right,ast.Constant) and isinstance(node.right.value,int) and node.right.value>=0,'polynomial power');v=one
    for j in range(node.right.value):v=mul(v,evaluate(node.left))
   else:raise RuntimeError('unsupported polynomial operation')
  else:raise RuntimeError('unsupported polynomial node')
  cache[key]=v;return v
 rebuilt=scale(evaluate(ast.parse(data_expr['simple_numerator'],mode='eval').body),576)
 need(P==rebuilt,'fresh 170 compact numerator')
 print('170 fresh Boolean numerator PASS',len(P),flush=True)
records=[];start=time.time()
for bs in bases:
 rec=json.loads((ROOT/(f'reduced_{name}_repair_'+'_'.join(map(str,bs))+'.json')).read_text());need(tuple(rec['basis'])==bs and rec['exact'],'certificate metadata')
 rem=translate(P,bs);rayt=translate(ray,bs);weights=0
 for exponent,weight in rec['weights']:
  weight=Q(weight);need(weight>=0,'negative multiplier');weights+=bool(weight)
  for e,c in rayt.items():
   f=tuple(a+b for a,b in zip(e,exponent));rem[f]=rem.get(f,Q(0))-weight*c
 rem={e:c for e,c in rem.items() if c};need(all(c>=0 for c in rem.values()),('remainder sign',bs));digest=hashlib.sha256(payload(rem).encode()).hexdigest();need(digest==rec['remainder_sha256'],('remainder hash',bs))
 records.append({'basis':bs,'multiplier_terms':weights,'remainder_terms':len(rem),'remainder_sha256':digest});print(name,bs,'PASS',flush=True)
out={'all_pass':True,'profile':name,'fresh_boolean_numerator':True,'pair_cones':len(records),'multiplier_terms':sum(v['multiplier_terms'] for v in records),'remainder_terms':sum(v['remainder_terms'] for v in records),'shared_Rayleigh_SOS_terms':soscount,'method':'independent Boolean row assignment counts and ascending unit shifts, exact rational arithmetic','records':records,'seconds':time.time()-start};(ROOT/f'replay_reduced_{name}.json').write_text(json.dumps(out,indent=2)+'\n');print('ALL PASS',out['multiplier_terms'],out['remainder_terms'])
