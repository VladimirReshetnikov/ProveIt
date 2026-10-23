"""Independent exact polynomial identities used by the new bounds."""
import sympy as s,json
from pathlib import Path
D,t,G,H=s.symbols('D t G H');DF=t*t*D**3*(D-1)+D;approx=t*(8*D*D-4*D-1)
assert s.expand(approx**2-64*DF-(t*t*(8*D+1)-64*D))==0
I=(G*G-1)*H*H+1;V=approx*G*H+1
assert s.expand(V*V-64*DF*I-((t*t*(8*D+1)-64*D)*G*G*H*H+64*DF*(H*H-1)+2*approx*G*H+1))==0
c,g,k,e=s.symbols('c g k e');delta=g*(c-g)*k*k-c*c*e*e
assert s.expand(c*c*(k*k-4*e*e)-4*delta-(c-2*g)**2*k*k)==0
out={'exact_DF_approximant_identity':True,'exact_scaled_product_error':True,'exact_merged_guard_identity':True,'method':'Symbolic expansion over Z; inequalities require hypotheses in proofs.'}
Path(__file__).with_name('norm_guard_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
