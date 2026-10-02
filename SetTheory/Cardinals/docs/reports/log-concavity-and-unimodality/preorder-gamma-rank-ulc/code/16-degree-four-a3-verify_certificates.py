"""Fresh standard-library exact replay of all a3 positivity certificates and faces.
Integer-encoded exponents speed polynomial arithmetic; no numerical tools or producer imports.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import json,itertools,math,time
D=Path(__file__).parent

def encode(e):
 assert all(isinstance(x,int) and 0<=x<16 for x in e)
 return sum(x<<(4*j) for j,x in enumerate(e))
def decode(code,d):return tuple((code>>(4*j))&15 for j in range(d))
def add(A,B,factor=1):
 out=dict(A)
 for e,c in B.items():out[e]=out.get(e,0)+factor*c
 return {e:c for e,c in out.items() if c}
def mul(A,B):
 out={}
 for a,u in A.items():
  for b,v in B.items():out[a+b]=out.get(a+b,0)+u*v
 return {e:c for e,c in out.items() if c}
def weighted_square(m,Z):return {encode(m)+e:c for e,c in mul(Z,Z).items()}
start=time.time();targets={}
for r in map(json.loads,(D/'normalized_faces.jsonl').read_text().splitlines()):
 targets[r['id']]={'d':r['variables'],'p':{encode(e):int(c) for e,c in r['polynomial']}}
count=0;general=0
for r in map(json.loads,(D/'certificates.jsonl').read_text().splitlines()):
 target=targets[r['id']];d=target['d'];total={};degree=max(sum(decode(e,d)) for e in target['p']);assert r['kind'] in('general','binomial')
 for weight,meta in r['terms']['squares']:
  weight=F(weight);assert weight>0
  if r['kind']=='binomial':
   m,a,b,u,v=meta;assert len(m)==len(a)==len(b)==d;Z=add({encode(a):F(u)},{encode(b):F(-v)})
  else:
   m,z=meta;assert len(m)==d;assert all(len(e)==d for e,c in z);Z={encode(e):F(c) for e,c in z};assert len(Z)==len(z)
  assert all(x>=0 for x in m);assert sum(m)+2*max(sum(decode(e,d)) for e in Z)<=degree
  total=add(total,weighted_square(m,Z),weight)
 for e,c in r['terms']['monomials']:
  c=F(c);assert c>0 and len(e)==d and sum(e)<=degree;total=add(total,{encode(e):c})
 assert total==target['p'],('SOS identity',r['id']);count+=1;general+=r['kind']=='general'
 if count%10000==0:print('Normalized exact certificates',count,'seconds',time.time()-start,flush=True)
assert count==len(targets);print('Every normalized target verified',count,flush=True)
# Independently reconstruct six times each gamma polynomial from falling factorials.
def gamma(row,quota,d):
 out={}
 for q,c in zip(quota,row):
  if not c:continue
  denominator=math.prod(math.factorial(v) for v in q);assert 6%denominator==0
  p={0:6*c//denominator}
  for j,k in enumerate(q):
   for a in range(k):p=mul(p,{1<<(4*j):1,0:-a})
  out=add(out,p)
 return out
S=[[0]*7 for _ in range(7)];S[0][0]=1
for n in range(1,7):
 for k in range(1,n+1):S[n][k]=S[n-1][k-1]+k*S[n-1][k]
@lru_cache(maxsize=None)
def binomial_terms(code,d):
 e=decode(code,d);out=[]
 for q in itertools.product(*(range(v+1) for v in e)):
  c=math.prod(S[v][w]*math.factorial(w) for v,w in zip(e,q))
  if c:out.append((encode(q),c))
 return out
def binomial(P,d):
 out={}
 for e,c in P.items():
  for q,v in binomial_terms(e,d):out[q]=out.get(q,0)+c*v
 return out
@lru_cache(maxsize=100000)
def shift_terms(code,d,mask):
 e=decode(code,d)
 if any(v and not(mask>>j&1) for j,v in enumerate(e)):return ()
 return tuple((encode(q),math.prod(math.comb(v,w) for v,w in zip(e,q))) for q in itertools.product(*(range(v+1) for v in e)))
def face(P,d,mask):
 out={}
 for e,c in P.items():
  for q,v in shift_terms(e,d,mask):out[q]=out.get(q,0)+c*v
 return {e:c for e,c in out.items() if c}
certinfo=json.loads((D/'coefficient_certificates.json').read_text());binomial_ids={(r['gap'],i) for r in certinfo for i in r['binomial_positive_ids']}
aliases={}
for a in json.loads((D/'face_aliases.json').read_text()):
 key=(a['id'],a['gap'],a['face']);assert key not in aliases;aliases[key]=a
rows=[json.loads(line) for line in(D/'a3_unique_gamma.jsonl').read_text().splitlines()];assert {r['id'] for r in rows}==set(range(len(rows)))
counts={'binomial':0,'coefficient_faces':0,'SOS_faces':0};used=set()
for n,r in enumerate(sorted(rows,key=lambda r:(len(r['types']),r['id']))):
 d=len(r['types']);gg=[gamma(row,r['quota'],d) for row in r['gamma']]
 for k,left,right in((2,4,9),(3,3,8)):
  P=add({e:left*c for e,c in mul(gg[k],gg[k]).items()},mul(gg[k-1],gg[k+1]),-right)
  if(k,r['id']) in binomial_ids:
   assert all(c>=0 for c in binomial(P,d).values());counts['binomial']+=1;continue
  for mask in range(1<<d):
   Q=face(P,d,mask)
   if all(c>=0 for c in Q.values()):counts['coefficient_faces']+=1;continue
   key=(r['id'],k,mask);a=aliases[key];used.add(key);active=[j for j in range(d) if mask>>j&1];perm=a['permutation'];assert len(set(perm))==len(perm) and all(0<=j<len(active) for j in perm)
   keep=[active[j] for j in perm];assert all(not any(e[j] for j in range(d) if j not in keep) for e in map(lambda code:decode(code,d),Q))
   transformed={encode(tuple(decode(e,d)[j] for j in keep)):c for e,c in Q.items()};target=targets[a['polynomial']];assert len(keep)==target['d'] and a['scale']>0
   assert transformed=={e:a['scale']*c for e,c in target['p'].items()},('face',key)
   counts['SOS_faces']+=1
 if(n+1)%500==0:print('Gamma polynomials',n+1,'seconds',time.time()-start,flush=True)
assert used==set(aliases)
# Check the coefficient-identical template-to-gamma reduction itself.
byid={r['id']:r for r in rows};mapping=json.loads((D/'a3_gamma_aliases.json').read_text());template_count=0
for r in map(json.loads,(D/'a3_polynomials.jsonl').read_text().splitlines()):
 g=byid[mapping[r['id']]];assert r['quota']==g['quota'] and r['gamma']==g['gamma'];template_count+=1
result={'status':'PASS','templates':template_count,'unique_gamma':len(rows),'gap_instances':2*len(rows),'normalized_targets':count,'general_square_targets':general,'counts':counts,'seconds':time.time()-start}
(D/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
