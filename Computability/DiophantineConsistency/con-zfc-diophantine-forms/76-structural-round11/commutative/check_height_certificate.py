#!/usr/bin/env python3
"""Independent finite checks, not a proof of the quantified source theorem."""
from collections import Counter,defaultdict
from itertools import product
from math import prod,lcm,gcd
from pathlib import Path
import json,random,hashlib,re
ROOT=Path(__file__).resolve().parent
obj=json.loads((ROOT/'height_shared_step.json').read_text())
def require(b,msg):
 if not b: raise AssertionError(msg)
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def polynomials(rows):
 a=[1];b=[1,1];r=2
 for p,q,c in rows:
  a=mul(a,[1,c]);b=mul(mul(b,[1,p]),[1,q]);r*=((p+1)*(q+1)+c)
 return a,b,r
def ev(a,x):
 y=0
 for c in reversed(a):y=y*x+c
 return y
def balance(rows):
 d=Counter({1:-1})
 for p,q,c in rows:
  if c:d[c]+=1
  if p:d[p]-=1
  if q:d[q]-=1
 return all(v==0 for v in d.values())
counts=Counter()
def check(rows):
 a,b,r=polynomials(rows);n=max(len(a),len(b));d=[(a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0) for i in range(n)]
 require(sum(a)<=r//2 and sum(b)<=r,'heightbound')
 require(max(map(abs,d))<=r,'coefficient bound')
 same=all(c==0 for c in d)
 require(same==balance(rows),'root multiplicity')
 for m in (r+1,r+2,2*r+1):require((ev(a,m)==ev(b,m))==same,'evaluation rigidity')
 counts['height_fixtures']+=1
for n in range(3):
 for data in product(range(4),repeat=3*n):check(list(zip(data[::3],data[1::3],data[2::3])))
for data in product(range(3),repeat=9):check(list(zip(data[::3],data[1::3],data[2::3])))
rng=random.Random(20261024)
for _ in range(1000):check([tuple(rng.randrange(20) for _ in range(3)) for _ in range(rng.randrange(3,9))])
# Exact no-height negative control: rule 1 -> 3, no axioms, target1 underivable.
a,b,r=polynomials([(1,0,3)])
require(ev(a,1)==ev(b,1) and not balance([(1,0,3)]) and r==10,'collision control')
require(1*(1+3)==2*(1+1),'unchecked accumulator collision')
counts['collision_controls']=1
# All natural monomial/source assertions use literal JSON rather than its builder.
def sparse(rows):
 d=defaultdict(int)
 for v in rows:d[tuple(sorted(v['monomial']))]+=v['coefficient']
 return {k:v for k,v in d.items() if v}
def sq(d):
 out=defaultdict(int)
 for m,a in d.items():
  for n,b in d.items():out[tuple(sorted(m+n))]+=a*b
 return out
h=obj['horn_source'];degrees=[]
for branch in h['branches']:
 ss=defaultdict(int)
 for row in branch['quadratic_residuals']:
  for m,a in sq(sparse(row)).items():ss[m]+=a
 require({m:a for m,a in ss.items() if a}==sparse(branch['sum_of_squares']),'Horn exact SOS')
 degrees.append(max(map(len,ss)))
 counts['horn_sos_identities']+=1
require(sum(degrees)==50,'exact product degree')
require(len(obj['witnesses'])==20 and len(set(obj['witnesses']))==20,'witness count')
require(obj['exposed_coordinates']==['S','Sp','R','Rp','M0'],'exposed order')
require(max(map(len,sparse(obj['extra_residuals'][0])))==5,'update degree')
require(max(map(len,sparse(obj['extra_residuals'][1])))==3,'height degree')
def rowev(rows,v):return sum(t['coefficient']*prod(v[x] for x in t['monomial']) for t in rows)
for _ in range(800):
 v={s:rng.randrange(0,100) for s in obj['exposed_coordinates']+obj['witnesses']};m=v['M0']+1
 e=v['Sp']*(1+v['v']*m)-v['S']*(1+v['p']*m)*(1+v['q']*m)
 f=v['Rp']-v['R']*((1+v['p'])*(1+v['q'])+v['v'])
 require(rowev(obj['extra_residuals'][0],v)==e,'literal E')
 require(rowev(obj['extra_residuals'][1],v)==f,'literal F')
 counts['local_formula_fixtures']+=1
# Construct proof trees, their open-obligation accumulators, and exact endpoints.
def tree(c,depth,rows):
 if depth==0 or rng.randrange(3)==0:rows.append((0,0,c));return
 p=rng.randrange(1,8);q=rng.randrange(0,8);rows.append((p,q,c))
 tree(p,depth-1,rows)
 if q:tree(q,depth-1,rows)
def crt(values,y):
 mods=[1+(i+1)*y for i in range(len(values))];x=0;b=1
 for v,m in zip(values,mods):
  require(v<m,'beta bound');require(gcd(b,m)==1,'pairwise coprime')
  x+=b*((v-x)*pow(b,-1,m)%m);b*=m
 return x
for k in range(100):
 rows=[];tree(1,3,rows);a,b,r=polynomials(rows);m=r+1;s=m+1;rr=2;ss=[s];rs=[rr];obligations=Counter({1:1})
 for p,q,c in rows:
  require(obligations[c]>0,'open obligation');obligations[c]-=1
  for d in (p,q):
   if d:obligations[d]+=1
  num=s*(1+p*m)*(1+q*m);den=1+c*m
  require(num%den==0,'integer S successor');s=num//den;rr*=((1+p)*(1+q)+c)
  require(s==prod((1+d*m)**n for d,n in obligations.items()),'obligation invariant');ss.append(s);rs.append(rr)
 require(s==1 and rr==r and m==rr+1 and balance(rows),'path endpoints')
 if k<12:
  n=len(rows);fac=lcm(*range(1,n+1)) if n else 1;y=fac*(max(ss+rs)+1)
  x=crt(ss,y);z=crt(rs,y)
  require([x%(1+(i+1)*y) for i in range(n+1)]==ss,'S beta')
  require([z%(1+(i+1)*y) for i in range(n+1)]==rs,'R beta')
  counts['simultaneous_beta_fixtures']+=1
 counts['proof_tree_paths']+=1
# Constructor syntactic audit is not a Lean typecheck.
lean=(ROOT/'HeightCommutativeEquation.lean').read_text()
require(lean.count('.boundedForall')==1,'one bounded universal block')
require('commonMultiple' not in lean and 'Fin 5 ⊕ Fin 20' in lean,'constructor shape')
require('(.var 3 - .var 4)' in lean and '(.var 2 - 2)' in lean,'height endpoints')
require('UNCOMPILED' in lean and 'UNMATERIALIZED' in lean,'status')
counts['constructor_shape_checks']=4
out={'status':'PASS','scope':'finite identities and fixtures, not kernel theorem or global polynomial','counts':dict(counts),'local_witnesses':20,'local_exact_degree':50,'global_bounded_forall_blocks':1,'source_sha256':hashlib.sha256((ROOT/'horn_shared_source.json').read_bytes()).hexdigest(),'literal_sha256':hashlib.sha256((ROOT/'height_shared_step.json').read_bytes()).hexdigest()}
(ROOT/'HEIGHT_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
