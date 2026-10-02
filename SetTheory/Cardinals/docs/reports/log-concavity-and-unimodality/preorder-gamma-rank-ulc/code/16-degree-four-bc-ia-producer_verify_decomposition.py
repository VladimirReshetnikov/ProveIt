"""Independent labeled support matching versus exterior disjoint convolution."""
import itertools,json,random
from functools import lru_cache
from pathlib import Path
D=Path(__file__).parent

def direct(types):
 n=4+len(types);rows=[0,0,3,3]+[0]*len(types)
 for j,t in enumerate(types):
  for a in range(4):
   if t>>a&1:
    if a>=2:rows[a]|=1<<(4+j)
    else:rows[4+j]|=1<<a
 @lru_cache(None)
 def match(a,b):
  if not a:return True
  i=(a&-a).bit_length()-1;opts=rows[i]&b
  while opts:
   bit=opts&-opts;opts-=bit
   if match(a^(1<<i),b^bit):return True
  return False
 full=(1<<n)-1;g=[0]*5
 for a in range(1<<n):
  k=a.bit_count()
  if k>4:continue
  comp=full^a;b=comp
  while True:
   if b.bit_count()==k and match(a,b):g[k]+=1
   if not b:break
   b=(b-1)&comp
 return g

def exterior(types):
 side=[]
 for shift in (2,0):
  masks=[(t>>shift)&3 for t in types];poly=[(0,1)]
  for i,a in enumerate(masks):
   if a:poly.append((1<<i,a.bit_count()))
  for i,j in itertools.combinations(range(len(types)),2):
   if masks[i] and masks[j] and masks[i]|masks[j]==3:poly.append(((1<<i)|(1<<j),1))
  side.append(poly)
 f=[0]*5
 for a,u in side[0]:
  for b,v in side[1]:
   if not a&b:f[(a|b).bit_count()]+=u*v
 m=sum(bool(t&12) for t in types);n=sum(bool(t&3) for t in types);r=sum(bool(t&12) and bool(t&3) for t in types);v=m*n-r
 g=f.copy();g[1]+=4;g[2]+=2*(m+n)+1;g[3]+=v
 if f[4]:
  assert 3*f[3]**2>=8*f[2]*f[4]
  assert v*v>=4*f[4]
  assert 3*m*n*f[3]>=10*(m+n)*f[4]
  assert 6*v*f[3]+3*v*v>=8*(2*(m+n)+1)*f[4]
 assert 3*g[3]*g[3]>=8*g[2]*g[4]
 return g,f
rng=random.Random(319742);cases=[[],[15],[15]*4,[5,6,9,10],[1,2,4,8],[3]*3+[12]*3]
for _ in range(250):cases.append([rng.randrange(1,16) for _ in range(rng.randrange(7))])
for i,ts in enumerate(cases):
 gd=direct(ts);ge,f=exterior(ts);assert gd==ge,(ts,gd,ge)
receipt={'independent_labeled_graphs':len(cases),'max_exterior_vertices':max(map(len,cases)),'all_gamma_decompositions_match':True,'all_counting_bounds_checked':True,'status':'passed'}
(D/'decomposition_verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
