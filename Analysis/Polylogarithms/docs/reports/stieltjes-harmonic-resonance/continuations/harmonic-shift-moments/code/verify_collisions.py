"""Independent finite-part quadratures and exact collision coefficient checks.
The quadrature integrates the original periodic digamma product after local
Taylor subtraction. It does not use the collision theorem.
"""
import json
from pathlib import Path
from itertools import combinations
import mpmath as mp
import sympy as s

mp.mp.dps=70
ROOT=Path(__file__).resolve().parents[1]/'results'
ROOT.mkdir(parents=True,exist_ok=True)

def f(x):return -mp.digamma(x)
def fp_interval(etas,length):
 residue=mp.fprod(f(x) for x in etas)
 derivative=mp.fsum(-mp.polygamma(1,etas[i])*mp.fprod(f(etas[j]) for j in range(len(etas)) if j!=i) for i in range(len(etas)))
 limit=derivative+mp.euler*residue
 def integrand(t):
  if abs(t)<mp.mpf('1e-50'):return limit
  smooth=mp.fprod(f(x+t) for x in etas)
  return (smooth-residue)/t+f(1+t)*smooth
 # The integration grid adapts to all close arguments.
 pts={mp.mpf(0),length/16,length/4,length/2,length}
 for x in etas:
  for p in [1,4,16]:
   if 0<x*p<length:pts.add(x*p)
 return mp.quad(integrand,sorted(pts))+residue*mp.log(length)

def separated(shifts):
 boundaries=sorted([(mp.frac(-a),i) for i,a in enumerate(shifts)])
 ans=mp.mpf(0)
 for n,(point,idx) in enumerate(boundaries):
  following=boundaries[n+1][0] if n+1<len(boundaries) else boundaries[0][0]+1
  etas=[mp.frac(point+shifts[j]) for j in range(len(shifts)) if j!=idx]
  ans+=fp_interval(etas,following-point)
 return ans

def conv(a,b):
 ans=[mp.mpf(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):ans[i+j]+=x*y
 return ans

def merged(d,split=mp.mpf(1)/8,count=100):
 coeff=[mp.mpf(1),mp.euler]+[(-1)**k*mp.zeta(k+1) for k in range(1,count)]
 prod=[mp.mpf(1)]
 for _ in range(d):prod=conv(prod,coeff)
 local=mp.fsum(c*split**(j-d+1)/(j-d+1) if j!=d-1 else c*mp.log(split) for j,c in enumerate(prod))
 return local+mp.quad(lambda x:f(x)**d,[split,mp.mpf('0.4'),1])

def counterterm(a):
 d=len(a);ans=mp.mpf(0)
 for m in range(d):
  for i in range(m+1,d):
   term=mp.log(a[i]-a[m])/(a[i]-a[m])
   term*=mp.fprod(f(1+a[k]-a[i]) for k in range(m))
   term*=mp.fprod(f(a[k]-a[i]) for k in range(m+1,d) if k!=i)
   ans+=term
 return ans

def exact_linear_ct(c):
 e=s.symbols('e'); G=s.symbols('gamma'); zs={k:s.Symbol('zeta'+str(k)) for k in range(2,len(c)+1)}
 def hh(x):return G+sum((-1)**k*zs[k+1]*x**k for k in range(1,len(c)))
 const=0;logco=0
 for m in range(len(c)):
  for i in range(m+1,len(c)):
   p=s.Integer(1)
   for k in range(m):p*=hh((c[k]-c[i])*e)
   for k in range(m+1,len(c)):
    if k!=i:
     x=(c[k]-c[i])*e;p*=1/x+hh(x)
   v=s.expand(p).coeff(e,1)/(c[i]-c[m]);const+=v*s.log(c[i]-c[m]);logco+=v
 return s.expand(const),s.expand(logco)

def exact_hierarchy(p,q):
 # Direct expansion of the only counterterm with a non-monomial log.
 # The other two have pure multiples of log(e), hence no log-free CT.
 e=s.symbols('e');G=s.Symbol('gamma');d=p-q;N=q//d+2
 w=sum(-s.harmonic(n)*e**(n*d-q) for n in range(1,N+1))
 hh=G+sum(s.zeta(k+1)*e**(q*k) for k in range(1,N+1))
 return s.expand(w*hh).coeff(e,0)

def exact_right_hierarchy(p,q):
 e=s.symbols('e');G=s.Symbol('gamma');gap=p-q;N=(p+q)//gap+2
 w=sum((-1)**(n+1)*s.harmonic(n)*e**(n*gap) for n in range(1,N+1))
 ff=-e**(-p-q)+G*e**(-q)+sum(s.zeta(k+1)*e**(p*k-q) for k in range(1,N+1))
 return s.expand(w*ff).coeff(e,0)

def main():
 exact=[]
 for p in range(2,13):
  for q in range(1,p):
   v=exact_hierarchy(p,q);want=-s.Symbol('gamma')*s.harmonic(q//(p-q)) if q%(p-q)==0 else 0
   assert s.simplify(v-want)==0
   right=exact_right_hierarchy(p,q);gap=p-q
   target=s.Integer(0)
   if (p+q)%gap==0:
    nn=(p+q)//gap;target+=(-1)**nn*s.harmonic(nn)
   if q%gap==0:
    nn=q//gap;target+=s.Symbol('gamma')*(-1)**(nn+1)*s.harmonic(nn)
   assert s.simplify(right-target)==0
   exact.append({'p':p,'q':q,'left_constant':str(v),'right_constant':str(right)})
 quartic_constant,lc=exact_linear_ct(list(map(s.Integer,[0,1,2,3])))
 G=s.Symbol('gamma');Z2=s.Symbol('zeta2');Z3=s.Symbol('zeta3')
 want=G*Z2*(2*s.log(2)+s.log(3))-s.Rational(3,2)*Z3*(3*s.log(2)+s.log(3))
 assert s.simplify(quartic_constant-want)==0
 c2,lc2=exact_linear_ct(list(map(s.Integer,[0,1,2,4])))
 wantdiff=G*Z2*(s.Rational(7,2)*s.log(2)+s.log(3))-Z3*(s.log(2)+7*s.log(3))/6
 assert s.simplify(c2-quartic_constant-wantdiff)==0
 qs={d:merged(d) for d in [2,3,4]}
 rows=[]
 tests=[('linear_quartic',[0,1,2,3],None),('hierarchy_2_1',None,(2,1)),('hierarchy_3_2',None,(3,2)),('right_hierarchy_2_1',None,(2,1)),('right_hierarchy_3_1',None,(3,1))]
 for name,c,pq in tests:
  for power in [2,3]:
   e=mp.mpf(10)**(-power)
   if c is not None:a=[mp.mpf(x)*e for x in c]
   elif name.startswith('right_'):a=[mp.mpf(0),e**pq[1],e**pq[1]+e**pq[0]]
   else:a=[mp.mpf(0),e**pq[0],e**pq[1]]
   v=separated(a);ct=counterterm(a);res=v-ct-qs[len(a)]
   row={'case':name,'epsilon':str(e),'separated_fp':mp.nstr(v,55),'counterterm':mp.nstr(ct,55),'regular_remainder_minus_merged':mp.nstr(res,40),'residual_div_max_shift':mp.nstr(res/max(a),30)}
   rows.append(row);print(name,e,mp.nstr(res,25),flush=True)
 # Curved binary arc has constant discrepancy b by elementary composition.
 for b in [mp.mpf(-2),mp.mpf(3)]:
  for power in [3]:
   e=mp.mpf(10)**(-power);a=[mp.mpf(0),e+b*e**2]
   v=separated(a);ct=counterterm(a);res=v-ct-qs[2]
   rows.append({'case':'curved_binary','b':str(b),'epsilon':str(e),'regular_remainder_minus_merged':mp.nstr(res,40),'predicted_plain_constant':mp.nstr(qs[2]+b,45)})
 output={'precision_digits':mp.mp.dps,'method':'Original periodic product, independent local Taylor-subtracted quadrature; floating-point diagnostics, not certified intervals.','merged_moments':{str(k):mp.nstr(v,60) for k,v in qs.items()},'hierarchy_exact_checks':exact,'quartic_constant':str(quartic_constant),'quartic_log_coefficient':str(lc),'quartic_rate_difference':str(s.expand(c2-quartic_constant)),'numeric_checks':rows}
 (ROOT/'collision_hierarchy_checks.json').write_text(json.dumps(output,indent=2)+'\n')

if __name__=='__main__':main()
