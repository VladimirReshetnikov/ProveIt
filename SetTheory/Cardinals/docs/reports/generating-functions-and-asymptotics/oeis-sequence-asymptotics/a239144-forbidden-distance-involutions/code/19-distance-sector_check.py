# Independent two-sector numerical quadrature for disjoint triangles.
import mpmath as m, sympy as s, json
from pathlib import Path
m.mp.dps=65
import os
out=Path(os.environ.get("OUTPUT_DIR",Path(__file__).resolve().parents[1]/"results")).resolve()
out.mkdir(parents=True, exist_ok=True)
src=out
a=s.symbols('a1:5');D=[s.sympify(x) for x in json.loads((src/'coefficients.json').read_text())['sector']]
av={a[j-1]:s.Rational(3**(j-1),j) for j in range(1,5)};ds=[m.mpf(str(s.N(x.subs(av),70))) for x in D]
rows=[]
# n/3 disjoint triangles: mu(y)=y^(n/3)*(y^2-3)^(n/3), degree bound2 and cutoff B2.
for n in [60,150,300,600]:
 for sig in [1,-1]:
  root=m.sqrt(n);logL=-m.log(2)/2+n*(m.log(n)-1)/2+sig*root-m.mpf(1)/4-1
  def f(y):return m.exp(m.mpf(n)/3*(m.log(y)+m.log(y*y-3))-(y-sig)**2/2-m.log(2*m.pi)/2-logL)
  val=m.quad(f,[2,max(m.mpf(2),root-10),root,root+10,m.inf]);approx=sum(ds[h]*sig**h*n**(-m.mpf(h)/2) for h in range(7))
  rows.append({'n':n,'sigma':sig,'relative_sector_value':str(val),'order6_scaled_error':str((val-approx)*n**m.mpf('3.5'))})
(out/'sector-checks.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
