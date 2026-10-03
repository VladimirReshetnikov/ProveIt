"""Tests selected smooth inverse models only; no amplitude digits are assumed."""
import mpmath as m,json
from pathlib import Path
m.mp.dps=70
z=m.airyaizero(1)
cs=[53*z*z/90,623*z/432,m.mpf(3497)/4480-1304*z**3/42525]
def F(x,g):return m.log(g)+m.loggamma(x+1)+x*m.log(8)+3*z*x**(m.mpf(1)/3)+m.mpf(7)/8*m.log(x)+sum(c*x**(-m.mpf(k)/3) for k,c in enumerate(cs,1))
def D(x):return m.digamma(x+1)+m.log(8)+z*x**(-m.mpf(2)/3)+m.mpf(7)/(8*x)-sum(m.mpf(k)/3*c*x**(-m.mpf(k)/3-1) for k,c in enumerate(cs,1))
out=[]
for g in [1,10,100]:
 for x in [50,1000,1000000]:
  x=m.mpf(x);Y=F(x,g);w=m.lambertw(8/m.e*Y);X=Y/w
  first=X-(3*z*X**(m.mpf(1)/3)+m.mpf(11)/8*m.log(X)+m.log(g*m.sqrt(2*m.pi)))/(1+w)
  root=m.findroot(lambda t:F(t,g)-Y,(x*m.mpf('.99'),x*m.mpf('1.01')))
  assert abs(root-x)<m.mpf('1e-55') and D(x)>0
  assert abs(m.diff(lambda t:F(t,g),x)-D(x))<m.mpf('1e-60')
  out.append({'trial_gamma':g,'x':str(x),'first_index_error':str(first-x),'model_inverse_error':str(root-x)})
r={'scope':'Trial positive amplitude models only; no enclosure of true gamma or discrete thresholds','precision_digits':70,'cases':out}
Path(__file__).with_name('inverse-checks.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
