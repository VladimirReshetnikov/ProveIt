import math
#!/usr/bin/env python3
"""Independent Pollard-rho bounded screen and source pins; no Lean."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def need(b,s):
    if not b:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=Path(__file__).resolve().parents[2]; d=base/'research/p64-qcube72-first-index-gap-analysis'; lean=base/'Lean/DiophantineConsistency'; graph=base/'research/p64-qcube72-free-main-candidate/graph.json'
pins={d/'README.md':'4397d88cd5fb0486f420dcd66475dccc8838c4074d855b2fcb7b6c5ca329f458',
 d/'screen.py':'d3bc1569bea74c30c631e11508d839d7d025ed96816c3c0351ebd9d4b4c545a6',
 d/'screen-result.json':'6d9f9bd2da81f2a64a85acaf5c3aa2ddec5fd88d73d76714e946a98152e6b0ed',
 graph:'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806',
 lean/'ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390',
 lean/'ArithmeticPellClassification.lean':'77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78',
 lean/'Compact44/P64Early.lean':'4db7d2153b1849d4646503244f7a5f2df031ddbeda4f135194b836ea125a02c1',
 lean/'Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
 lean/'Compact44/P72Power.lean':'f46584fb3977ae5fc33b31bee18e8c27435d97bea10138f163af2de5ee66d462'}
for p,h in pins.items():need(sha(p)==h,'pin mismatch '+str(p))
source_tokens={
 lean/'ArithmeticPellClassification.lean':['theorem solution_index (b x y : V)','xcoord time b=x ∧ ycoord time b=y'],
 lean/'ArithmeticPellPowerRecovery.lean':['theorem projection_quotient (a t : V)','xcoord t a=Exp.exp t+a*ycoord t a+(4*a+3)*z'],
 lean/'Compact44/P64Early.lean':['theorem gcd_dvd_nine','theorem early','(2 * n) % μ = R + 1'],
 lean/'Compact44/P72Exact.lean':['theorem indices_ordinary','m = R ∧ 2 * n = R + 1'],
 lean/'Compact44/P72Power.lean':['theorem power_of_mod','(hnR : 2 * n = R + 1) (hmR : m = R)']}
for path,tokens in source_tokens.items():
    text=path.read_text()
    for token in tokens:need(token in text,'source interface '+token)
author=json.loads((d/'screen-result.json').read_text())
need(author['status']=='PASS_EXHAUSTIVE_BOUNDED_SCREEN' and author['R']==[43,47] and author['s_min']==1 and author['s_max']==30 and author['first_index_max']=='R','author domain')


def prime(n):
 if n<2:return False
 for p in (2,3,5,7,11,13,17,19,23,29,31,37):
  if n%p==0:return n==p
 if n>=2**64:raise ValueError('prime bound')
 d=n-1;s=0
 while d%2==0:s+=1;d//=2
 for a in (2,325,9375,28178,450775,9780504,1795265022):
  x=pow(a%n,d,n)
  if a%n==0 or x in (1,n-1):continue
  for k in range(s-1):
   x=x*x%n
   if x==n-1:break
  else:return False
 return True

def factors(n):
 ret=[];todo=[n]
 while todo:
  x=todo.pop()
  if x==1:continue
  if prime(x):ret.append(x);continue
  if x%2==0:todo.extend((2,x//2));continue
  div=None
  for c in range(1,40):
   a=b=2
   for i in range(100000):
    a=(a*a+c)%x;b=(b*b+c)%x;b=(b*b+c)%x;g=math.gcd(abs(a-b),x)
    if g!=1:
     if g!=x:div=g
     break
   if div:break
  if not div:raise ValueError(('rho',x))
  todo.extend((div,x//div))
 out={}
 for p in ret:out[p]=out.get(p,0)+1
 need(math.prod(p**e for p,e in out.items())==n,'factor product')
 return out

def mul(A,B,D):return A[0]*B[0]+D*A[1]*B[1],A[0]*B[1]+A[1]*B[0]
def pp(x,y,D,k):
 r=(1,0);b=(x,y)
 while k:
  if k&1:r=mul(r,b,D)
  k//=2
  if k:b=mul(b,b,D)
 return r

candidates=[]; matches=[]
for R in (43,47):
 for s in range(1,31):
  Y=27*s;U=Y*Y;Q=4*Y*(2**R+1)+3;fq=factors(Q);fu=factors(U)
  for p,e in fu.items():fq[p]=fq.get(p,0)+e
  divs=[1]
  for p,e in fq.items():divs=[v*p**i for v in divs for i in range(e+1)]
  for H in divs:
   if H<=4*Y+3 or (H-(4*Y+3))%(12*Y):continue
   X=(H-4*Y-3)//(4*Y);w=X//3;a=Y*(X+1);D=(a+2)**2-1;P=X*U
   g,c=pp(a+2,1,D,R)
   need(U*(g-X-a*c)%H==0,'projection identity')
   candidates.append((R,s,w,H))
   for j in range(1,R+1):
    t,k=pp(2*P+1,2,P*(P+1),j)
    if Y*k<c<(Y+1)*k:matches.append((R,s,w,j))
need(candidates==[(47,8,6351,16462659),(47,26,10021896201,84424453600035)] and matches==[],'independent screen result')
need(author['projection_candidate_count']==len(candidates) and author['first_main_scale_candidate_count']==len(matches),'count mismatch')
out={'status':'PASS_INDEPENDENT_BOUNDED_SCREEN','script_sha256':sha(__file__),
     'author_readme_sha256':pins[d/'README.md'],'author_screen_sha256':pins[d/'screen.py'],
     'graph_sha256':pins[graph],'R':[43,47],'s_range':[1,30],'q':3,'first_index_range':'1..R',
     'projection_candidates':[{'R':r,'s':s,'w':w,'H':h} for r,s,w,h in candidates],
     'scale_matches':matches,'scope':'Independent bounded integer screen and source review only; no Lean, general existence or compact44 claim.'}
print(json.dumps(out,indent=2,sort_keys=True))
