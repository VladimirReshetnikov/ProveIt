"""Exact finite coefficient certificate and symbolic SOS identities.
Every quartic monomial uses at most four exterior vertices; neighborhood masks
run through all seven nonempty subsets of a three-vertex shore.
"""
from itertools import product,combinations,combinations_with_replacement,permutations
from functools import lru_cache
from collections import Counter
from pathlib import Path
import json
import sympy as s

@lru_cache(None)
def match(rows):
 if not rows:return 1
 return int(any(all(rows[i]>>col&1 for i,col in enumerate(cols)) for cols in __import__('itertools').permutations(range(3),len(rows))))
CORES=[(1,2),(1,3),(1,6),(1,7),(3,3),(3,5),(3,7),(7,7)]
PARTS=[((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2))]
BAD={(2,3,4,5),(2,3,5,5),(3,3,4,5),(3,3,5,5)}

def coefficient(core,ls,squared=False):
 s1,s2=core
 pairs=list(combinations(range(len(ls)),2))
 p={ij:match((s1,ls[ij[0]],ls[ij[1]])) for ij in pairs}
 q={ij:match((s2,ls[ij[0]],ls[ij[1]])) for ij in pairs}
 o={ij:p[ij]*q[ij] for ij in pairs}
 if squared:
  return 4*(p[0,1]*q[0,2]+p[0,2]*q[0,1])-4*o[0,1]*o[0,2]-3*match(core+(ls[0],))*match(ls)
 return 4*sum(p[a]*q[b]+p[b]*q[a] for a,b in PARTS)-4*sum(o[a]*o[b] for a,b in PARTS)-3*sum(match(core+(ls[i],))*match(tuple(ls[j] for j in range(4) if j!=i)) for i in range(4))

def verify():
 # Verify the eight representatives cover exactly the 46 labeled rank-two cores.
 covered=set()
 for core in CORES:
  for pp in permutations(range(3)):
   mapped=tuple(sum(1<<pp[j] for j in range(3) if row>>j&1) for row in core)
   covered.add(mapped);covered.add(mapped[::-1])
 expected={core for core in product(range(8),repeat=2) if match(core)}
 assert covered==expected and len(covered)==46
 records=[];checked=0
 for core in CORES:
  repeated=Counter();squarefree=Counter();negative=[]
  for ls in product(range(1,8),repeat=3):
   z=coefficient(core,ls,True);assert z>=0,(core,ls,z);repeated[z]+=1;checked+=1
  for ls in combinations_with_replacement(range(1,8),4):
   z=coefficient(core,ls);squarefree[z]+=1;checked+=1
   if z<0:negative.append((ls,z))
  assert set(ls for ls,z in negative)==(BAD if core in[(1,6),(1,7)] else set())
  assert all(z==-4 for ls,z in negative)
  records.append({'core':core,'repeated_exponent_coefficients':dict(sorted(repeated.items())),'squarefree_coefficients':dict(sorted(squarefree.items())),'negative_patterns':negative})
 a,b,c,d,U,V=s.symbols('a b c d U V',nonnegative=True);u=a+b;v=c+d
 def I(B,D):return s.expand(4*u*v*((a+c)*(b+d)+b*d+B+D)-2*(a*d+b*c+b*d)**2-3*(u+v)*(v*(a*b+B)+u*(c*d+D)))
 P00=2*(a*d-b*c)**2+u*v*(a*b+c*d)+(a*c+b*d)*(a*d+b*c)+2*b*b*d*d
 R01=a*a*(b*d+c*d)+a*(b*b*d/2+b*c*c+c*c*d+c*d*d/2)+b*b*(2*c*c+c*d)+b*(c*c*d+c*d*d/2+d**3/2)
 P01=d*d*(a-b)**2/2+a*d*(b-d)**2/2+a*c*(b-d)**2+b*c*(a-d)**2+R01
 P11=b*d*(u-v)**2/2+(a*d+b*c+3*a*c)*(b-d)**2/2+(b+d)*(a*c*(a+c)+(a*a*d+b*c*c)/2)
 for got,want in [(P00,I(0,0)),(P01,I(0,d*d/2)),(P01.xreplace({a:c,b:d,c:a,d:b}),I(b*b/2,0)),(P11,I(b*b/2,d*d/2))]:assert s.expand(got-want)==0
 # The second exceptional core adds ac to P2 and to O, leaving C,T fixed.
 P1=u*v;P2=(a+c)*(b+d)+b*d+U+V;O=a*d+b*c+b*d;T=v*(a*b+U)+u*(c*d+V)
 core57=4*P1*(P2+a*c)-2*(O+a*c)**2-3*(u+v)*T
 assert s.expand(core57-I(U,V)-2*a*a*c*c)==0
 assert s.Poly(R01,a,b,c,d).coeffs() and all(t>=0 for t in s.Poly(R01,a,b,c,d).coeffs())
 # Exact quadratic identity used to pass from the target to all right classes.
 p,q,o,A,B,c=s.symbols('p q o A B c',positive=True)
 lhs=(q*A+p*B-o*c)**2-(4*p*q-2*o*o)*(A*B-c*c/2)
 rhs=(1-o*o/(2*p*q))*(q*A-p*B)**2+(o*(q*A+p*B)-2*p*q*c)**2/(2*p*q)
 assert s.simplify(lhs-rhs)==0
 report={'coefficient_cases':checked,'labeled_rank_two_cores_covered':len(covered),'core_orbits':len(CORES),'coefficient_lemma_passed':True,'four_corner_identities_passed':True,'right_class_quadratic_identity_passed':True,'records':records}
 (Path(__file__).resolve().parents[1]/'data'/'forced_core_verification.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items() if k!='records'},indent=2))
if __name__=='__main__':verify()
