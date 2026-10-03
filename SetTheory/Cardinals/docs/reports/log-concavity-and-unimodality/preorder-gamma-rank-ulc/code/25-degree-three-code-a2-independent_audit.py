"""Independent exhaustive labeled-relation coverage and support/certificate audit.
Does not import any generator, support kernel, or certificate helper.
"""
import json,itertools,time,math
from pathlib import Path
from collections import defaultdict
from fractions import Fraction as F
D=Path(__file__).parent
T=json.loads((D/'templates.json').read_text())['templates']
start=time.time()
def trans(R):
 return all(not (R[j]&~R[i]) for i in range(len(R)) for j in range(len(R)) if R[i]>>j&1)
def key(R,S,TT):
 n=len(R); candidates=[]
 for sw in (False,True):
  for tail in itertools.permutations(range(2,n)):
   order=((1,0) if sw else (0,1))+tail
   for rev in (False,True):
    rows=tuple(sum(1<<j for j in range(n) if i!=j and ((R[order[j]]>>order[i]&1) if rev else (R[order[i]]>>order[j]&1))) for i in range(n))
    signs=tuple(S[i]*(-1 if rev else 1) for i in ((1,0) if sw else (0,1)))
    ts=tuple(sorted((((t&1)<<1)|((t&2)>>1)) if sw else t for t in TT))
    candidates.append((rows,signs,ts))
 return min(candidates)
expected={(tuple(r['core_rows']),tuple(r['signs']),tuple(r['types'])) for r in T}
assert len(expected)==len(T)
seen=set();counts={}
for n in range(2,6):
 count=0
 choices=[tuple((mask&((1<<i)-1))|((mask>>i)<<(i+1))|(1<<i) for mask in range(1<<(n-1))) for i in range(n)]
 for R in itertools.product(*choices):
  if not trans(R):continue
  count+=1
  for S in itertools.product((-1,1),repeat=2):
   TT=[]
   for t in (1,2,3):
    Q=list(R)+[1<<n]
    for a in (0,1):
     if t>>a&1:
      if S[a]<0:Q[a]|=1<<n
      else:Q[n]|=1<<a
    if trans(Q):TT.append(t)
   if TT:seen.add(key(R,S,TT))
 counts[n]=count
 print('coverage',n,count,len(seen),'seconds',time.time()-start,flush=True)
assert seen==expected, (len(seen-expected),len(expected-seen))

def supports(edges,N):
 out=[set() for _ in range(4)]
 def visit(start,used,A,B,k):
  out[k].add((A,B))
  if k==3:return
  for j in range(start,len(edges)):
   u,v=edges[j];bits=(1<<u)|(1<<v)
   if not used&bits:visit(j+1,used|bits,A|(1<<u),B|(1<<v),k+1)
 visit(0,0,0,0,0)
 return out
for index,r in enumerate(T):
 n=len(r['core_rows']);d=len(r['types']);G=[{} for _ in range(4)]
 for quota in itertools.product(range(3),repeat=d):
  if sum(quota)>2:continue
  ext=[t for t,c in zip(r['types'],quota) for _ in range(c)]
  edges=[(u,v) for u,row in enumerate(r['core_rows']) for v in range(n) if row>>v&1]
  for j,t in enumerate(ext):
   for a in (0,1):
    if t>>a&1:edges.append((a,n+j) if r['signs'][a]<0 else (n+j,a))
  mandatory=((1<<len(ext))-1)<<n
  for k,ss in enumerate(supports(edges,n+len(ext))):
   val=sum(((a|b)&mandatory)==mandatory for a,b in ss)
   if val:G[k][quota]=val
 assert G==[{tuple(e):v for e,v in p} for p in r['gamma']],r['id']
 if index%200==0:print('supports',index,'seconds',time.time()-start,flush=True)

# Sparse rational polynomial arithmetic, using ordinary monomials.
def add(A,B,c=F(1)):
 C=A.copy()
 for e,v in B.items():C[e]=C.get(e,F(0))+c*v
 return {e:v for e,v in C.items() if v}
def mul(A,B):
 C={}
 for a,u in A.items():
  for b,v in B.items():
   e=tuple(i+j for i,j in zip(a,b));C[e]=C.get(e,F(0))+u*v
 return {e:v for e,v in C.items() if v}
def binomial(p,d):
 C={}
 for e,v in p:
  term={(0,)*d:F(v)}
  for j,k in enumerate(e):
   unit=tuple(int(i==j) for i in range(d))
   for a in range(k):term=mul(term,{unit:F(1,a+1),(0,)*d:F(-a,a+1)})
  C=add(C,term)
 return C
def face(P,d,mask):
 active=[j for j in range(d) if mask>>j&1];Q={}
 for e,v in P.items():
  if any(e[j] for j in range(d) if j not in active):continue
  for f in itertools.product(*(range(e[j]+1) for j in active)):
   z=v*math.prod(math.comb(e[j],f[k]) for k,j in enumerate(active));Q[f]=Q.get(f,F(0))+z
 return {e:v for e,v in Q.items() if v}
byid={};polys={}
for r in T:
 d=len(r['types']);gs=[binomial(p,d) for p in r['gamma']]
 p=add(mul(gs[2],gs[2]),mul(gs[1],gs[3]),-3)
 assert p==binomial(r['gap2'],d),r['id']
 assert add(mul(gs[1],gs[1]),mul(gs[0],gs[2]),-3)==binomial(r['gap1'],d)
 gid=r['gamma_id']
 if gid in byid:assert byid[gid]['gamma']==r['gamma'] and byid[gid]['gap2']==r['gap2']
 byid[gid]=r;polys[gid]=p
certs=json.loads((D/'gap2_certificates.json').read_text())
assert len(certs)==len(byid)==448 and {c['gamma_id'] for c in certs}==set(byid)
stat={'templates':len(T),'labeled_preorders':counts,'unique_gamma':len(byid),'binomial_positive':0,'face_families':0,'verified_faces':0}
for c in certs:
 r=byid[c['gamma_id']];d=len(r['types'])
 if c['kind']=='binomial_positive':
  assert all(v>=0 for e,v in r['gap2']);stat['binomial_positive']+=1;continue
 assert c['kind']=='faces' and c['failures']==[]
 assert len(c['faces'])==1<<d and {f['mask'] for f in c['faces']}==set(range(1<<d))
 stat['face_families']+=1
 for f in c['faces']:
  m=f['mask'].bit_count();total={}
  for weight,pp,meta in f['terms']:
   weight=F(weight);assert weight>=0
   p={tuple(e):F(v) for e,v in pp};assert len(p)==len(pp)
   assert all(len(e)==m and all(isinstance(i,int) and i>=0 for i in e) for e in p)
   if meta is not None:
    mon,z=meta;mon=tuple(mon);z={tuple(e):F(v) for e,v in z}
    assert len(mon)==m and all(isinstance(i,int) and i>=0 for i in mon)
    assert all(len(e)==m and all(isinstance(i,int) and i>=0 for i in e) for e in z)
    assert p==mul({mon:F(1)},mul(z,z))
   elif len(p)==1:assert next(iter(p.values()))>=0
   else:
    assert len(p)==3
    pos=[(e,v) for e,v in p.items() if v>0];neg=[(e,v) for e,v in p.items() if v<0]
    assert len(pos)==2 and len(neg)==1
    (a,u),(b,v)=pos;(e,w),=neg
    assert tuple(i+j for i,j in zip(a,b))==tuple(2*i for i in e) and w*w==4*u*v
   total=add(total,p,weight)
  assert total==face(polys[c['gamma_id']],d,f['mask']),(c['gamma_id'],f['mask'])
  stat['verified_faces']+=1
# Classification is informational only, but independently verify its records.
from functools import lru_cache
classifications=json.loads((D/'classification.json').read_text())
assert len(classifications)==len(T)
for r,c in zip(T,classifications):
 n=len(r['core_rows']);edges={(min(i,j),max(i,j)) for i,row in enumerate(r['core_rows']) for j in range(n) if row>>j&1}
 N=n
 for t in r['types']:
  for _ in range(3):
   edges.update((a,N) for a in (0,1) if t>>a&1);N+=1
 adj=[set() for _ in range(N)]
 for a,b in edges:adj[a].add(b);adj[b].add(a)
 unseen=set(range(N));ranks=[];bip=True
 while unseen:
  component={min(unseen)};todo=list(component);colors={todo[0]:0}
  while todo:
   a=todo.pop()
   for b in adj[a]:
    if b in colors:
     if colors[b]==colors[a]:bip=False
    else:colors[b]=1-colors[a];component.add(b);todo.append(b)
  unseen-=component
  ce=tuple((a,b) for a,b in edges if a in component)
  @lru_cache(None)
  def maximum(vertices):
   if not vertices:return 0
   a=min(vertices);remaining=vertices-{a}
   return max([maximum(remaining)]+[1+maximum(remaining-{b}) for b in adj[a]&remaining])
  ranks.append(maximum(frozenset(component)))
 assert c=={'id':r['id'],'gamma_id':r['gamma_id'],'bipartite':bip,'component_ranks':ranks,'all_component_rank_le2':max(ranks,default=0)<=2}
stat['classifications_verified']=len(T)
stat['seconds']=time.time()-start
(D/'independent_audit.json').write_text(json.dumps(stat,indent=2)+'\n')
print('ALL INDEPENDENT CHECKS PASSED',stat,flush=True)
