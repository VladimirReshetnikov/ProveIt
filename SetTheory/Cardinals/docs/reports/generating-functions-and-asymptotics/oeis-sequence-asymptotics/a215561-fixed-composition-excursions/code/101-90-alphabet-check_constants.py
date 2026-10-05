"""Exact small-alphabet constants and diagnostic root products.

The root products for r>=6 are numerical orientation, not certificates.
"""
from pathlib import Path
import sympy as s,json
z=s.symbols('z');records=[]
for r in range(2,11):
    steps=list(range(-(r-1),r,2)) if r%2==0 else list(range(-(r//2),r//2+1))
    h=max(steps);poly=r*z**h-sum(z**(h+j) for j in steps)
    q,rem=s.div(poly,(z-1)**2,z)
    if rem!=0 or q.subs(z,1)==0:raise RuntimeError(('critical multiplicity',r))
    roots=s.nroots(q,maxsteps=1000,n=35) if s.degree(q,z)>0 else []
    inner=[v for v in roots if abs(complex(v))<1]
    if len(inner)!=h-1:raise RuntimeError(('root split',r,len(inner),h-1))
    er=s.N((-1)**(h-1)*r*s.prod(inner),30)
    if abs(float(s.im(er)))>1e-25 or s.re(er)<=0:raise RuntimeError(('positive value',r,er))
    records.append({'r':r,'steps':steps,'critical_quotient':str(q),'inner_root_count':len(inner),'critical_excursion_value_numeric':str(s.re(er)),'OEIS_pi_free_constant_numeric':str(s.N(s.re(er)/(s.sqrt(r)*2**s.Rational(r-1,2)),20))})

phi=(1+s.sqrt(5))/2
e4=4*(phi-s.sqrt(phi));e5=5*(3-s.sqrt(5))/2
# The r4 conjugate inner-root product p satisfies p+1/p=2phi.
p=e4/4
if s.simplify(p*p-2*phi*p+1)!=0:raise RuntimeError('r4 product identity')
if not 0<float(p)<1:raise RuntimeError('r4 small product')
if s.simplify(e4/(s.sqrt(4)*2**s.Rational(3,2))-(phi-s.sqrt(phi))/s.sqrt(2))!=0:raise RuntimeError('r4 OEIS constant')
if s.simplify(e5/(s.sqrt(5)*4)-(3*s.sqrt(5)-5)/8)!=0:raise RuntimeError('r5 OEIS constant')
out={'exact_checks_passed':True,'exact_e2':'2','exact_e3':'3','exact_e4':str(e4),'exact_e5':str(e5),'numeric_orientation':records}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
