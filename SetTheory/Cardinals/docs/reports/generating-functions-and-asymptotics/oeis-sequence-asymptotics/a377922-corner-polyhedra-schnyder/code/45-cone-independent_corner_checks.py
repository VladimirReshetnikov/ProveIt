from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
(ROOT / "results").mkdir(exist_ok=True)
"""Independent finite and exact-algebra audit. Not a substitute for proofs."""
import itertools,json
from collections import defaultdict
import sympy as s
x,y,u=s.symbols('x y u');D=(1-1/(3*x*x))*(1-y*y/3)
K=s.Matrix([[2*y*y/(27*D),2*x/(3*y)+2*y/(27*x*D)],[2*x/(3*y)+2*y/(27*x*D),2/(27*x*x*D)]])
ev=lambda f:s.simplify(f.subs({x:1,y:1,u:1})); dg=lambda f,z:z*s.diff(f,z)
P=K.subs({x:1,y:1});h=[s.Rational(1,10),-s.Rational(1,10)]
for mat,hh in [(K,h),(K.T.subs({x:1/x,y:1/y},simultaneous=True),[-v for v in h])]:
    assert mat.subs({x:1,y:1})==s.Matrix([[s.Rational(1,6),s.Rational(5,6)],[s.Rational(5,6),s.Rational(1,6)]])
    for i in range(2):
        assert all(ev(dg(sum(mat[i,j] for j in range(2)),z))+sum(P[i,j]*(hh[j]-hh[i]) for j in range(2))==0 for z in [x,y])
for i in range(2):
    j=1-i; R=u*K[i,i]+u*u*K[i,j]*K[j,i]/(1-u*K[j,j])
    assert ev(s.diff(R,u))==2
    assert [ev(dg(R,v)) for v in [x,y]]==[0,0]
    assert [[ev(dg(dg(R,v),w)) for w in [x,y]] for v in [x,y]]==[[s.Rational(32,5),s.Rational(-18,5)],[s.Rational(-18,5),s.Rational(32,5)]]
# Finite exhaustive cycle shape audit, from origin, including reversed paths.
off=[(1,-1)]+[(-2*i-1,2*j+1) for i in range(3) for j in range(3)]
mid=[(-2*i,2*j) for i in range(1,3) for j in range(3)]
checked=0
for m in range(4):
 for a,b in itertools.product(off,repeat=2):
  for middle in itertools.product(mid,repeat=m):
   path=[(0,0)]
   for z in [a,*middle,b]:path.append(tuple(path[-1][r]+z[r] for r in range(2)))
   end=path[-1]
   assert all(z[r]>=min(0,end[r])-1 for z in path for r in range(2))
   rev=[tuple(z[r]-end[r] for r in range(2)) for z in path[::-1]]
   assert all(z[r]>=min(0,-end[r])-1 for z in rev for r in range(2))
   checked+=1
# Exact unweighted counting, finite because only one unit y decrease per step.
def count(N):
 d={(0,0):1}
 for t in range(N):
  nxt=defaultdict(int); remain=N-t-1
  for (a,b),c in d.items():
   if b>0 and b-1<=remain:nxt[a+1,b-1]+=c
   for i in range(a+1):
    for j in range(max(0,remain-b)+1):
     if b+j>remain or (i+j)%2:continue
     if (b%2==0 and j==0) or (b%2==1 and i==0):continue
     nxt[a-i,b+j]+=c
  d=nxt
 return sum(c for (a,b),c in d.items() if b==0 and a>0)
terms=[count(n) for n in range(1,16)]
assert terms[:12]==[0,0,1,0,3,4,15,39,122,375,1212,3980]
report={'symbolic_kernel_and_correctors':'PASS','both_cycle_covariances':'PASS','exhaustive_nontrivial_cycles':checked,'cycle_minimum_bound_and_reverse':'PASS','walk_counts_n_1_to_15':terms,'paper_first_terms_match':'PASS'}
print(json.dumps(report,indent=2))
open(ROOT / "results" / "independent-corner-checks.json",'w').write(json.dumps(report,indent=2))
