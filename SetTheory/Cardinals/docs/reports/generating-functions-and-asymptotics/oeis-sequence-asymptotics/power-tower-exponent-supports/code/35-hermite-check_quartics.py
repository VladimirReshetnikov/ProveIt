"""Exact independent completion-of-square and squarefreeness checks."""
import sympy as s
from pathlib import Path
import json
N,k,K=s.symbols('N k K')
P4=80*N**2-(120*k*k+1480*k+4128)*N+15*k**4+390*k**3+3485*k**2+12558*k+15232
P5=80*N**2-(40*k*k+680*k+2368)*N+3*k**4+106*k**3+1277*k*k+6102*k+9840
f4=150*K**4-120*K*K-30*K+196
f5=10*K**4-40*K*K-30*K+256
Z=20*N-15*K*K-5*K+54
Y=20*N-5*K*K-5*K+64
if s.expand(5*P4.subs(k,K-6)-(Z*Z-f4))!=0: raise RuntimeError('defect-four identity')
if s.expand(5*P5.subs(k,K-8)-(Y*Y-f5))!=0: raise RuntimeError('defect-five identity')
data=json.loads(Path(__file__).with_name('hermite_checks.json').read_text())
residuals={item['defect']:s.sympify(item['residual'],locals={'N':N,'k':k}) for item in data['records']}
if s.expand(residuals[4]-P4/92160)!=0: raise RuntimeError('residual-four transcription')
if s.expand(residuals[5]+(k+8)*P5/368640)!=0: raise RuntimeError('residual-five transcription')
records=[]
for r,f in [(4,f4),(5,f5)]:
    gcd=s.Poly(s.gcd(f,s.diff(f,K)),K,domain=s.QQ).monic().as_expr()
    disc=s.discriminant(f,K)
    if gcd!=1 or disc==0: raise RuntimeError(('squarefreeness', r))
    records.append({'defect':r,'quartic':str(f),'monic_gcd_with_derivative':str(gcd),'discriminant':str(disc)})
out={'completion_of_square_identities':True,'records':records,'scope':'exact algebra only; finiteness additionally uses the stated Siegel theorem'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
