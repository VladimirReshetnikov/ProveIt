"""Independent six-variable integer-ring degree audit; standard library only.
No producer, verifier, or retained polynomial library is imported. The whole
product center is constructed by coefficient division, not its circuit formula.
"""
import hashlib,json,sys
from collections import defaultdict
from pathlib import Path
N=6; Z=(0,)*N
class R:
 def __init__(self,x=0):self.p=x if isinstance(x,dict) else ({Z:x} if x else {})
 @staticmethod
 def v(i):
  m=list(Z);m[i]=1;return R({tuple(m):1})
 def __add__(a,b):
  if not isinstance(b,R):b=R(b)
  d=defaultdict(int,a.p)
  for m,c in b.p.items():d[m]+=c
  return R({m:c for m,c in d.items() if c})
 __radd__=__add__
 def __neg__(a):return R({m:-c for m,c in a.p.items()})
 def __sub__(a,b):return a+-b if isinstance(b,R) else a+-R(b)
 def __rsub__(a,b):return R(b)+-a
 def __mul__(a,b):
  if not isinstance(b,R):b=R(b)
  d=defaultdict(int)
  for m,c in a.p.items():
   for n,e in b.p.items():d[tuple(x+y for x,y in zip(m,n))]+=c*e
  return R({m:c for m,c in d.items() if c})
 __rmul__=__mul__
 def __pow__(a,n):
  out=R(1)
  for _ in range(n):out=out*a
  return out
 def __eq__(a,b):return isinstance(b,R) and a.p==b.p
 def quo(a,j):return R({(m[0]-j,)+m[1:]:c for m,c in a.p.items() if m[0]>=j})
 def top(a,w):
  d=max(sum(x*y for x,y in zip(m,w)) for m in a.p)
  return d,R({m:c for m,c in a.p.items() if sum(x*y for x,y in zip(m,w))==d})
 def subst(a,xs):
  out=R()
  for m,c in a.p.items():
   t=R(c)
   for x,e in zip(xs,m):t=t*x**e
   out=out+t
  return out
 def hash(a):return hashlib.sha256(json.dumps(sorted(a.p.items()),separators=(',',':')).encode()).hexdigest()
def need(q,msg):
 if not q:raise ValueError(msg)
A,t,k,u,b,c=[R.v(i) for i in range(N)]
ell=t*(A-t-1)*k;E=1+ell*(ell+k);D=A*A-1;G=E*(1+D*u*u*E);V=(1+2*D*u*u*E)*b-c
S=E.quo(1);constant=E-A*S
need(constant==1+k*k*t*(t+1)*(t*(t+1)-1),'full Euclidean division of E')
center2=2*A*u*E-u*S
F=E*V;q3=F.quo(3)
need(all(v%2==0 for v in q3.p.values()),'integral half-quotient')
center4=u*(4*A*F-2*F.quo(1)-R({m:v//2 for m,v in q3.p.items()}))
defect2=center2**2-4*G;defect4=center4**2-16*G*V**2
weights=[4,2,1,5,4,2]
cd2,ct2=center2.top(weights);cd4,ct4=center4.top(weights)
d2,top2=defect2.top(weights);d4,top4=defect4.top(weights)
need((cd2,cd4,d2,d4)==(23,59,34,94),'center and whole-defect weighted degrees')
need(top2==4*u*u*A*A*t**6*k**4,'scalar full leader')
need(top4==8*A**6*t**8*k**8*u**6*b*b*(A*A-6*t**4),'whole norm-defect full leader')
need(len(center4.p)==84 and len(defect4.p)==594,'complete whole-center and defect monomial counts')
q,f,w,s,i,h=[R.v(j) for j in range(N)]
subs=[q*q*w*s,q*s,h,i*h*h*s*s,-q**3*(q-f),h*s]
AA,TT,KK,UU,BB,CC=subs;EE=(TT*AA*KK)**2
QQ=4*AA**6*UU**4*EE**2;MM=24*q**8*AA;VV=2*AA**2*UU**2*EE*BB
leader202=QQ*MM**2*top2.subst(subs)*VV**2
leader190=QQ*MM**2*top4.subst(subs)
need(leader202==9*2**12*q**80*w**22*s**56*i**10*h**32*(q-f)**2,'dependent scalar complete leading form')
need(leader190==9*2**11*q**74*w**18*s**52*i**10*h**32*(q-f)**2*(w*w-6*s*s),'dependent whole complete leading form')
root=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/release/scalar')
source_path=root/'source_centers/exact_polynomials.json';source=json.loads(source_path.read_text())
def vector_literal(ts):
 out={}
 for coefficient,exponents in ts:
  need(type(coefficient) is int and coefficient!=0 and type(exponents) is list and len(exponents)==N and all(type(e) is int and e>=0 for e in exponents),'strict exponent-vector literal')
  key=tuple(exponents);need(key not in out,'unique exponent-vector monomial');out[key]=coefficient
 return R(out)
need(source['variables']==['A','Y','k','U','b','c'],'source-center variables; Y is current N')
need(vector_literal(source['center'])==center4 and vector_literal(source['norm_defect'])==defect4,'every retained formal center/defect coefficient independently recollected')
old_degree,old_top=defect4.top(source['weights'])
need(source['weights']==[4,2,1,7,4,3] and old_degree==106==source['norm_defect_weighted_degree'] and vector_literal(source['norm_defect_leading_terms'])==old_top,'historical-weight source metadata explicitly distinguished')
rows=[]
for degree,ops,center,defect,leader,other in [(202,99,center2,defect2,leader202,[180,197,70,142]),(190,120,center4,defect4,leader190,[154,184,70,142])]:
 actual,top=leader.top([1]*N);need(actual==degree and top==leader,'exact homogeneous degree')
 need(max(other)<degree,'strict smaller-degree other output terms')
 # q=beta J with beta nonzero and h=eta+zeta, an injective substitution
 # on this polynomial ring, so neither the leader nor its degree disappears.
 rows.append({'exact_degree':degree,'live_operations_expected':ops,'center_terms':len(center.p),'whole_defect_terms':len(defect.p),'center_weighted_degree':center.top(weights)[0],'defect_weighted_degree':defect.top(weights)[0],'defect_coefficient_sha256':defect.hash(),'leading_form_sha256':leader.hash(),'other_output_degree_bounds':other})
print(json.dumps({'status':'PASS','method':'Fresh standard-library integer exponent-tuple ring; no producer, verifier or retained polynomial library imports; centers obtained by exact A-division','weighted_variables':['A','N','k','U','b','c'],'weights':weights,'all_leading_dependencies_substituted':True,'retained_formal_literal_recollection':{'path':'source_centers/exact_polynomials.json','sha256':hashlib.sha256(source_path.read_bytes()).hexdigest(),'center_terms':84,'defect_terms':594,'historical_weighted_degree':old_degree,'new_weighted_degree':d4},'fixed_beta_nonzero_required':True,'results':rows,'boundary':'Exact finite algebra and degree check. Ordinary signed majorants, witness directions and unbounded native calibration are separate proof obligations.'},indent=2))
