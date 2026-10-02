"""Independent replay of the 35k-witness degree-two direction certificate."""
from pathlib import Path
import json,random
ROOT=Path(__file__).resolve().parents[1]
T=(ROOT/'source/UniversalTM15x2.tm.txt').read_text().splitlines()[0].split('_')
rules=[]
for q,c in enumerate(T):
 for s in [0,1]:
  z=c[s*3:s*3+3]
  if z!='---':rules.append((q,s,int(z[0]),z[1],ord(z[2])-65))

def run(L,R,limit):
 q=s=0;b=[];counts=[];states=[]
 for _ in range(limit+1):
  states.append([q,s,L,R])
  if (q,s)==(9,1):return b,counts,states
  if len(b)==limit:return None
  i=next(i for i,t in enumerate(rules) if t[:2]==(q,s))
  _,_,w,D,qp=rules[i]
  X,Y=(L,R) if D=='L' else (R,L);Q,r=divmod(X,2)
  v=[0]*35;v[i]=1;v[29:]=[Q,r,Y,0,0,0] if D=='L' else [0,0,0,Q,r,Y];b.append(v)
  counts.append(6+3*Q+r+3*Y)
  L,R=(Q,2*Y+w) if D=='L' else (2*Y+w,Q);q,s=qp,r

def polynomial(L0,R0,C,tau,b):
 k=len(b)
 if not k:return 1,[],[]
 rs=[];cs=[];prevL,prevR,prevq,prevs=L0,R0,0,0;count=6*k
 for v in b:
  assert len(v)==35 and all(type(x)==int and x>=0 for x in v)
  e=v[:29];ql,rl,yl,qr,rr,yr=v[29:]
  el=sum(x for x,t in zip(e,rules) if t[3]=='L');er=sum(e)-el
  wl=sum(x*t[2] for x,t in zip(e,rules) if t[3]=='L')
  wr=sum(x*t[2] for x,t in zip(e,rules) if t[3]=='R')
  a=sum(x*t[0] for x,t in zip(e,rules));s=sum(x*t[1] for x,t in zip(e,rules))
  bp=sum(x*t[4] for x,t in zip(e,rules))
  il=2*ql+rl+yr;ir=yl+2*qr+rr
  ol=ql+2*yr+wr;orr=2*yl+wl+qr
  rs.extend([sum(e)-1,a-prevq,s-prevs,il-prevL,ir-prevR])
  cs.extend([er*(ql+rl+yl),el*(qr+rr+yr)])
  prevL,prevR,prevq,prevs=ol,orr,bp,rl+rr
  count+=3*(ql+qr+yl+yr)+rl+rr
 rs.extend([prevq-9,prevs-1,C-count,tau-1-2*C-7*k])
 assert len(rs)==5*k+4 and len(cs)==2*k and all(c>=0 for c in cs)
 return sum(x*x for x in rs)+sum(cs),rs,cs

runs=0
for L in range(32):
 for R in range(32):
  result=run(L,R,100)
  if result is None:continue
  b,counts,states=result;C=sum(counts);tau=1+2*C+7*len(b)
  assert polynomial(L,R,C,tau,b)[0]==0
  assert polynomial(L,R,C+1,tau,b)[0]>0
  assert polynomial(L,R,C,tau+1,b)[0]>0
  runs+=1
b,counts,states=run(6,0,100);k=len(b);C=sum(counts);tau=1+2*C+7*k
assert (k,C,tau)==(7,189,428)
mutations=0
for v in b:
 for i in range(35):
  old=v[i]
  for new in [old+1]+([old-1] if old else []):
   v[i]=new;assert polynomial(6,0,C,tau,b)[0]>0;mutations+=1
  v[i]=old
rng=random.Random(9615162)
for _ in range(1000):
 arbitrary=[[rng.randrange(4) for _ in range(35)] for _ in range(7)]
 assert polynomial(6,0,C,tau,arbitrary)[0]>0
# Exact negative-curvature witness within the positive orthant.
direction=[0]*35
for source,coefficient in [((0,0),-5),((1,0),7),((2,0),1),((3,0),-3)]:
 i=next(i for i,t in enumerate(rules) if t[:2]==source);direction[i]=coefficient
direction[29:]=[-1,0,-2,1,0,2]
center=[10]*35
plus=[x+d for x,d in zip(center,direction)]
minus=[x-d for x,d in zip(center,direction)]
curvature=polynomial(6,0,189,428,[plus])[0]+polynomial(6,0,189,428,[minus])[0]-2*polynomial(6,0,189,428,[center])[0]
assert curvature==-24
# Align the exported symbolic compiler with this independent numeric evaluator.
from grouped_quadratic import DirectionalQuadratic,TABLE
assert TABLE == T
aligned=0
for horizon in [1,2,7,8]:
 cert=DirectionalQuadratic(horizon)
 for _ in range(100):
  env={name:rng.randrange(5) for name in cert.parameters+cert.witnesses}
  blocks=[[env[f'e{j}_{i}'] for i in range(29)]+[env[f'{name}{j}'] for name in ['QL','rL','YL','QR','rR','YR']] for j in range(horizon)]
  assert cert.energy(env)==polynomial(env['L0'],env['R0'],env['C'],env['tau'],blocks)[0]
  aligned+=1
out={'status':'PASS','witnesses':'35k','squared_linear_residuals':'5k+4','nonnegative_quadratic_products':'2k',
 'degree':2,'symbolic_numeric_alignment_cases':aligned,'nonconvex_second_difference':curvature,'halting_inputs_tested':runs,'single_coordinate_mutations_rejected':mutations,
 'arbitrary_natural_assignments_checked':1000,'example':{'L':6,'R':0,'k':k,'C':C,'tau':tau,'witnesses':b},
 'assurance':'Independent implementation plus mathematical audit; bounded-k family only'}
(ROOT/'receipts/quadratic-independent.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='example'},indent=2))
