"""Exact certificate verification. No imports from the original symbolic generator.
All polynomial vectors use increasing powers of z=n-3. We certify 36*Delta,
since each support coefficient has denominator dividing 6 in this basis.
"""
from itertools import combinations, permutations, product
from math import comb
from collections import Counter
import json, pathlib, hashlib
HERE=pathlib.Path(__file__).resolve().parent.parent/'data'

def add(a,b):
 c=[0]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]+=x
 for i,x in enumerate(b):c[i]+=x
 while len(c)>1 and not c[-1]:c.pop()
 return tuple(c)
def scale(a,t):return tuple(x*t for x in a)
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 while len(c)>1 and not c[-1]:c.pop()
 return tuple(c)
# 6 binom(z+3,h), h=0,1,2,3. Obtained by integer multiplication.
CH=[]
for h in range(4):
 p=(1,)
 for j in range(h):p=mul(p,(3-j,1))
 f=(1,1,2,6)[h]
 CH.append(scale(p,6//f))
assert CH==[(6,), (18,6), (18,15,3), (6,11,6,1)]

def hall_full(core,I,J,h,l):
 """Existence, not number, of a perfect matching on this support.
 I selected A, J selected B, h selected L, l selected R.
 All neighborhood subsets are tested directly (Hall's theorem).
 """
 if I.bit_count()+h!=J.bit_count()+l:return False
 neighbors=[((core>>(3*i))&J)|(((1<<l)-1)<<3) for i in range(3) if I>>i&1]+[J]*h
 if len(neighbors)>6:return False
 unions=[0]*(1<<len(neighbors))
 for S in range(1,len(unions)):
  b=S&-S; idx=b.bit_length()-1
  unions[S]=unions[S^b]|neighbors[idx]
  if unions[S].bit_count()<S.bit_count():return False
 return True

def transversal_rank(core,I,J):
 # Independent brute injection enumeration, as a cross-check of the Hall oracle.
 rows=[i for i in range(3) if I>>i&1]
 cols=[j for j in range(3) if J>>j&1]
 for k in range(min(len(rows),len(cols)),-1,-1):
  for R in combinations(rows,k):
   for C in permutations(cols,k):
    if all(core>>(3*i+j)&1 for i,j in zip(R,C)):return k
 raise AssertionError

def support_table(core):
 out={}
 for J in range(8):
  for l in range(4):
   k=J.bit_count()+l;p=(0,)
   for I in range(8):
    h=k-I.bit_count()
    if 0<=h<=3 and hall_full(core,I,J,h,l):p=add(p,CH[h])
   out[J,l]=p
 return out

def orbit(core):
 return {sum(((core>>(3*i+j))&1)<<(3*rp[i]+cp[j]) for i in range(3) for j in range(3)) for rp in permutations(range(3)) for cp in permutations(range(3))}
seen=set();reps=[];sizes={}
for core in range(512):
 if core not in seen:
  O=orbit(core);assert not (O&seen)
  reps.append(core);sizes[core]=len(O);seen|=O
assert len(reps)==36 and seen==set(range(512))
# Verify exact existence formula on every label and every support type.
feasibility_checks=0
for core in range(512):
 for I,J in product(range(8),repeat=2):
  nu=transversal_rank(core,I,J)
  for l in range(4):
   h=J.bit_count()+l-I.bit_count()
   if not 0<=h<=3:continue
   expected=I.bit_count()>=l and nu>=I.bit_count()-l
   assert hall_full(core,I,J,h,l)==expected,(core,I,J,h,l)
   feasibility_checks+=1
print('Hall support checks:',feasibility_checks,flush=True)

# A monomial specifies each of three core exponents in 0..2, and numbers
# ro and rt of exterior variables occurring once and twice respectively.
# There are never more than six distinct exterior variables in a product.
patterns={}
for k in range(1,6):
 patterns[k]=[(v,ro,rt) for v in product(range(3),repeat=3) for rt in range(4) for ro in range(7-rt) if sum(v)+ro+2*rt==2*k]

def coefficient_product(T,d,e,v,ro,rt):
 # Choose which singleton core variables lie in first coefficient.
 # Doubled core and exterior variables necessarily lie in both.
 doubled=sum(1<<i for i in range(3) if v[i]==2)
 singles=[i for i in range(3) if v[i]==1]
 total=(0,)
 for S in range(1<<len(singles)):
  I=doubled|sum(1<<i for q,i in enumerate(singles) if S>>q&1)
  J=doubled|sum(1<<i for q,i in enumerate(singles) if not S>>q&1)
  x=d-I.bit_count();y=e-J.bit_count()
  if x+y!=ro+2*rt or not (0<=x<=3 and 0<=y<=3 and 0<=x-rt<=ro):continue
  total=add(total,scale(mul(T[I,x],T[J,y]),comb(ro,x-rt)))
 return total

def gap(T,k,pattern):
 return add(scale(coefficient_product(T,k,k,*pattern),k*(6-k)),scale(coefficient_product(T,k-1,k+1,*pattern),-(k+1)*(7-k)))
T0=support_table(0)
for J in range(8):
 for l in range(4):assert T0[J,l]==scale(CH[J.bit_count()],comb(3,l))
certificate=[];stats=[];gap1_neg=[]
for core in reps:
 T=support_table(core);counts=Counter()
 for k in range(1,6):
  for pat in patterns[k]:
   p=add(gap(T,k,pat),scale(gap(T0,k,pat),-1))
   if any(x<0 for x in p):
    if k>1:raise AssertionError((core,k,pat,p))
    gap1_neg.append([core,k,pat,p])
   if k>1:
    counts['checked']+=1
    if any(p):counts['nonzero']+=1
    counts['nonzero_scalar_coefficients']+=sum(x!=0 for x in p)
    certificate.append({'core':core,'k':k,'core_exponents':pat[0],'exterior_singletons':pat[1],'exterior_doubles':pat[2],'coefficients_36_gap_increment':p})
 stats.append({'core':core,'orbit_size':sizes[core],**counts})
 print(core,dict(counts),flush=True)
certpath=HERE/'exact_certificate.json'
stored=json.loads(certpath.read_text())
assert json.loads(json.dumps(certificate))==stored, 'The stored certificate does not match exact reconstruction'
summary={'status':'passed','method':'integer arithmetic; direct Hall-subset oracle; independent core injection oracle; no SymPy or imported original generator','feasibility_checks_all_512_masks':feasibility_checks,'orbits':len(reps),'labels':sum(sizes.values()),'patterns_per_gap':{k:len(v) for k,v in patterns.items()},'coefficient_polynomials_checked':len(certificate),'nonzero_increment_polynomials':sum(s.get('nonzero',0) for s in stats),'nonzero_scalar_coefficients':sum(s['nonzero_scalar_coefficients'] for s in stats),'negative_coefficients_gaps_2_to_5':0,'gap1_negative_increment_patterns':gap1_neg,'core_statistics':stats,'certificate_sha256':hashlib.sha256(certpath.read_bytes()).hexdigest()}
(HERE/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ('gap1_negative_increment_patterns','core_statistics')},indent=2))
