"""Independent standard-library verifier of all polynomial positivity certificates.
Reconstructs gaps from gamma coefficients; checks exact binomial / shifted-face
coverage; reconstructs every nonnegative monomial or weighted square with Fractions.
No numerical solver, NumPy, SymPy, or producer-module import is used.
"""
from pathlib import Path
from fractions import Fraction as F
import itertools,json,math,time
D=Path(__file__).parent
E=[e for e in itertools.product(range(5),repeat=3) if sum(e)<=4]
ZERO=(0,0,0)
def add(A,B,c=1):
 out=dict(A)
 for e,v in B.items():out[e]=out.get(e,0)+c*v
 return {e:v for e,v in out.items() if v}
def mul(A,B):
 out={}
 for a,u in A.items():
  for b,v in B.items():
   e=tuple(x+y for x,y in zip(a,b));out[e]=out.get(e,0)+u*v
 return {e:v for e,v in out.items() if v}
def monomial(e,v=1):return {tuple(e):v} if v else {}
def unit(i,k=1):return tuple(k if j==i else 0 for j in range(3))
def scaled_gamma(row):
 # Rebuild twice the binomial polynomial directly from the defining falling factors.
 out=monomial(ZERO,2*row[0])
 for i in range(3):
  out=add(out,monomial(unit(i),2*row[1+i]))
  falling=mul(monomial(unit(i)),add(monomial(unit(i)),monomial(ZERO,-1)))
  out=add(out,falling,row[4+i])
 for index,(i,j) in enumerate(((0,1),(0,2),(1,2)),7):out=add(out,mul(monomial(unit(i)),monomial(unit(j))),2*row[index])
 return out
S=[[0]*5 for _ in range(5)];S[0][0]=1
for n in range(1,5):
 for k in range(1,n+1):S[n][k]=S[n-1][k-1]+k*S[n-1][k]
def binomial(P):
 out={}
 for e,c in P.items():
  for f in itertools.product(*(range(v+1) for v in e)):
   value=c*math.prod(S[v][w]*math.factorial(w) for v,w in zip(e,f))
   if value:out[f]=out.get(f,0)+value
 return {e:v for e,v in out.items() if v}
def face(P,mask):
 out={}
 for e,c in P.items():
  if any(e[j] and not(mask>>j&1) for j in range(3)):continue
  for f in itertools.product(*(range(v+1) for v in e)):
   out[f]=out.get(f,0)+c*math.prod(math.comb(v,w) for v,w in zip(e,f))
 return {e:v for e,v in out.items() if v}
info=json.loads((D/'quartic_sos_basis.json').read_text());assert [tuple(e) for e in info['exponents']]==E
basis=[]
for record in info['basis']:
 if 'monomial' in record:basis.append(monomial(record['monomial']));continue
 m=record['multiplier'];u=record['u'];v=record['v']
 square=add(monomial(record['left'],u),monomial(record['right'],-v))
 basis.append(mul(monomial(m),mul(square,square)))
G={r['polynomial']:r for r in map(json.loads,(D/'quartic_general_sos.jsonl').read_text().splitlines())}
certified={};start=time.time();general_count=0
for r in map(json.loads,(D/'quartic_sos_certificates.jsonl').read_text().splitlines()):
 target={e:F(c) for e,c in zip(E,r['coefficients']) if c};total={}
 if r['terms'] is not None:
  for index,w in r['terms']:
   w=F(w);assert w>=0;total=add(total,basis[index],w)
 else:
  general_count+=1;record=G[r['polynomial']];assert record['terms'] is not None,r['polynomial']
  for w,poly,meta in record['terms']:
   w=F(w);assert w>=0;P={tuple(e):F(c) for e,c in poly};assert len(P)==len(poly)
   if meta is not None:
    m,z=meta;Z={tuple(e):F(c) for e,c in z};assert all(v>=0 for v in m)
    assert mul(monomial(m),mul(Z,Z))==P
   elif len(P)==1:assert next(iter(P.values()))>=0
   else:
    # Base fallback rays are exact two-term squares up to positive scale.
    neg=[(e,c) for e,c in P.items() if c<0];pos=[(e,c) for e,c in P.items() if c>0]
    assert len(neg)==1 and len(pos)==2 and len(P)==3
    (a,u),(b,v)=pos;(e,c),=neg
    assert all(x+y==2*z for x,y,z in zip(a,b,e)) and c*c==4*u*v
   total=add(total,P,w)
 assert total==target,r['polynomial'];certified[r['polynomial']]=target
print('All normalized SOS certificates verified',len(certified),'general',general_count,flush=True)
aliases={}
for a in json.loads((D/'quartic_sos_aliases.json').read_text()):
 key=(a['id'],a['gap'],a['face']);assert key not in aliases;aliases[key]=a
binomial_ids={r['gap']:set(r['binomial_positive_ids']) for r in json.loads((D/'coefficient_certificates.json').read_text())}
count=0;used_alias=set();counts={'binomial':0,'coefficient_faces':0,'SOS_faces':0}
for record in map(json.loads,(D/'a2_polynomials.jsonl').read_text().splitlines()):
 assert record['id']==count;gg=[scaled_gamma(r) for r in record['gamma']]
 for k,left,right in ((2,4,9),(3,3,8)):
  P=add({e:left*c for e,c in mul(gg[k],gg[k]).items()},mul(gg[k-1],gg[k+1]),-right)
  if count in binomial_ids[k]:
   assert all(c>=0 for c in binomial(P).values());counts['binomial']+=1;continue
  for mask in range(8):
   R=face(P,mask)
   if all(c>=0 for c in R.values()):counts['coefficient_faces']+=1;continue
   key=(count,k,mask);a=aliases[key];used_alias.add(key);p=info['permutations'][a['permutation']]
   permuted={tuple(e[j] for j in p):F(c) for e,c in R.items()}
   expected={e:a['scale']*v for e,v in certified[a['polynomial']].items()}
   assert a['scale']>0 and permuted==expected,key
   counts['SOS_faces']+=1
 count+=1
 if count%10000==0:print('Gamma polynomials verified',count,'seconds',time.time()-start,flush=True)
assert used_alias==set(aliases)
result={'polynomials':count,'gap_polynomial_instances':2*count,'normalized_SOS_polynomials':len(certified),'general_square_polynomials':general_count,'counts':counts,'status':'PASS','seconds':time.time()-start}
(D/'quartic_verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
