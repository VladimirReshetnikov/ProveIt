import itertools,random,json
from collections import defaultdict
from pathlib import Path
D=Path(__file__).parent
source=(D.parent/'verify_balanced_monomer.py').read_text().split('rng=random.Random')[0]
source=source.replace('rows=[0,0,3,3]+[0]*len(types)','rows=[0,0]+list(core_rows)+[0]*len(types)')
exec(source.split('def kernel_merge')[0])

def kernel(types,u,v,mode):
 n=len(types);K=4+2*n;weights=v[:2]+u[2:4]+[w for i in range(n) for w in [v[4+i],u[4+i]]]
 def side(core,shift,copyoffset):
  items=[(core[0],1,1),(core[1],2,1)]
  for i,t in enumerate(types):
   mask=(t>>shift)&3
   if mask:items.append((4+2*i+copyoffset,mask,-1))
  L=[];B=[];R=[];A=[]
  for var,mask,sgn in items:
   ex=[0]*K;ex[var]=sgn;term=(ex,sgn);L.append(term)
   if mask==1:R.append(term)
   if mask|2==3:A.append(term)
  for (i,a,sa),(j,b,sb) in itertools.combinations(items,2):
   if a|b==3:
    ex=[0]*K;ex[i]=sa;ex[j]=sb;B.append((ex,sa*sb))
  return B,L,R,A
 BP,LP,RP,AP=side((2,3),2,0);BQ,LQ,RQ,AQ=side((0,1),0,1)
 terms=[]
 products=[(BP,BQ,1)]
 if mode=='star':products.append((AP,LQ,-1))
 else:products.extend([(LP,LQ,-1),(RP,RQ,1)]);terms.append(([0]*K,1))
 for A,B,sgn in products:
  for ex,c in A:
   for ey,d in B:terms.append(([a+b for a,b in zip(ex,ey)],sgn*c*d))
 out=defaultdict(int)
 for ex,c in terms:
  ex=ex[:]
  for j in range(4,K):ex[j]+=1
  assert all(e in (0,1) for e in ex)
  if any(ex[4+2*i]==0 and ex[5+2*i]==0 for i in range(n)):continue
  for j,e in enumerate(ex):
   if e==0:c*=weights[j]
  mask=sum(e<<j for j,e in enumerate(ex[:4]))
  for i in range(n):
   if ex[4+2*i] and ex[5+2*i]:mask|=1<<(4+i)
  out[mask]+=c
 return {m:c for m,c in out.items() if c}

rng=random.Random(18364)
cases=[[]]+[[x] for x in range(16)]+[list(x) for x in itertools.combinations_with_replacement(range(16),2)]
cases += [[rng.randrange(16) for _ in range(rng.randrange(3,6))] for _ in range(150)]
receipt={}
for mode,rows in [('star',(0,3)),('one_missing',(3,1))]:
 globals()['core_rows']=rows
 graphs=coeffs=zeros=0
 for types in cases:
  for style in range(2):
   N=4+len(types)
   if style==0:u=v=[1]*N
   else:u=[rng.randrange(4) for _ in range(N)];v=[rng.randrange(4) for _ in range(N)]
   zeros+=any(x==0 for x in u+v)
   a=direct(types,u,v);b=kernel(types,u,v,mode)
   assert a==b,(mode,types,u,v,a,b)
   graphs+=1;coeffs+=len(a)
 receipt[mode]={'graphs_with_activity_choices':graphs,'zero_activity_cases':zeros,'exact_monomer_coefficients':coeffs,'max_exterior_vertices':max(map(len,cases)),'exact_Hall_identity':True}
 print(mode,receipt[mode],flush=True)
(D/'incomplete_kernel_verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
