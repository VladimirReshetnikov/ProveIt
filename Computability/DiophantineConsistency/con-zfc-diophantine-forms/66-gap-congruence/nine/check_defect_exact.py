"""Re-expand the refined majorant defect exactly; optional SymPy check."""
from pathlib import Path
import json
import sympy as s
root=Path(__file__).resolve().parent
A,C,i=s.symbols('A C i');J=4*A-5;D=(A*A-1)*C*C+1;k=i*J*C
F=1+k*k*D*D*(D-1);L=C*D+1-A;G=A+F*L
B8=8*D*D-4*D-1
T6=k*(128*B8*(2*G+L)-k*k*(16*(B8+D)-8)*L+C*(14*k*k-192))
T=T6+i**3*(C*(C*(576*A-2151)-(896*A*A-4256*A+8442))+1024)+288*i+2048
actual=s.Poly(s.expand(T*T-2048**2*D*F*G*G),A,C,i)
saved=json.loads((root/'data/defect.json').read_text())
expected={tuple(t['powers']):t['coefficient'] for t in saved['terms']}
if actual.as_dict()!=expected:raise ValueError('exact defect expansion differs')
out={'status':'PASS','terms':len(expected),'identity':'T^2-2048^2 D F G^2 equals the supplied literal polynomial','coordinatewise_maxima':[max(e[j] for e in expected) for j in range(3)]}
(root/'generated/DEFECT_IDENTITY.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
