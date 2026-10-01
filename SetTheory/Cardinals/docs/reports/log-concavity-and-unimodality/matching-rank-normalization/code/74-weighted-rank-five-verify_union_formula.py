"""Independent exact endpoint enumeration for the two-row union formula."""
from random import Random
from pathlib import Path
import json

def coeffs(adj,u,v):
 n=len(v);wp=[1]*(1<<n)
 for J in range(1,1<<n):
  b=J&-J;wp[J]=wp[J-b]*v[b.bit_length()-1]
 out=[0]*(min(len(u),n)+1)
 for I in range(1<<len(u)):
  reach={0};w=1
  for i in range(len(u)):
   if I>>i&1:
    w*=u[i];reach={J|(1<<j) for J in reach for j in adj[i] if not J>>j&1}
    if not reach:break
  if I.bit_count()<len(out):out[I.bit_count()]+=w*sum(wp[J] for J in reach)
 return trim(out)
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(*ps):return trim([sum(p[i] if i<len(p) else 0 for p in ps) for i in range(max(map(len,ps)))])
def scale(a,c):return [c*x for x in a]
def shift(a,k=1):return [0]*k+a
def mul(a,b):
 p=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):p[i+j]+=x*y
 return trim(p)
def difference(a,*bs):return add(a,*[scale(b,-1) for b in bs])

def check(q,S1,S2,rng):
 L=[rng.randrange(1<<q) for _ in range(rng.randrange(6))]
 R=[rng.randrange(4) for _ in range(rng.randrange(6))]
 ul=[rng.randrange(1,10) for _ in L];vr=[rng.randrange(1,10) for _ in R]
 v=[rng.randrange(1,10) for _ in range(q)];x,y=[rng.randrange(1,10) for _ in range(2)]
 H=[{j for j in range(q) if M>>j&1} for M in L]
 def poly(extra):return coeffs(H+[{j for j in range(q) if M>>j&1} for M in extra],ul+[1]*len(extra),v)
 f=poly([]);gs=[]
 for S in [S1,S2,S1|S2]:
  diff=difference(poly([S]),f);assert diff[0]==0
  gs.append(diff[1:] or [0])
 g1,g2,gU=gs
 dif=difference(poly([S1,S2]),f,shift(g1),shift(g2));assert all(t==0 for t in dif[:2])
 h=dif[2:] or [0]
 a=sum(w for M,w in zip(R,vr) if M==1);b=sum(w for M,w in zip(R,vr) if M==2)
 common=[w for M,w in zip(R,vr) if M==3];c=sum(common);d=sum(common[i]*common[j] for i in range(len(common)) for j in range(i))
 rhs=add(mul(f,[1,x*(a+c)+y*(b+c),x*y*(a*b+a*c+b*c+d)]),shift(add(scale(g1,x),scale(g2,y))),shift(scale(add(h,scale(g2,a),scale(g1,b),scale(gU,c)),x*y),2))
 adj=[{j for j in range(q) if S>>j&1}|{q+j for j,M in enumerate(R) if M>>i&1} for i,S in enumerate([S1,S2])]+H
 lhs=coeffs(adj,[x,y]+ul,v+vr)
 assert lhs==rhs,(q,S1,S2,L,R,ul,vr,v,x,y,lhs,rhs)
 return bool(S1&S2),bool(S1&~S2==0 or S2&~S1==0),bool(S1==0 or S2==0)

if __name__=='__main__':
 rng=Random(425031);total=overlap=nested=empty=0
 for q,reps in [(1,10),(2,10),(3,10),(4,2)]:
  for S1 in range(1<<q):
   for S2 in range(1<<q):
    for _ in range(reps):
     flags=check(q,S1,S2,rng);total+=1;overlap+=flags[0];nested+=flags[1];empty+=flags[2]
 report={'exact_formula_checks':total,'q_values':[1,2,3,4],'overlap_cases':overlap,'nested_cases':nested,'empty_neighborhood_cases':empty,'all_checks_passed':True,'seed':425031,'method':'Boolean endpoint enumeration without matching multiplicities'}
 (Path(__file__).resolve().parents[1]/'data'/'union_formula_verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
