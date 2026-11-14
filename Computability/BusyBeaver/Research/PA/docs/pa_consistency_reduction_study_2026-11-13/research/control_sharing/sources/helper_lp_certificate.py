#!/usr/bin/env python3
"""Research search; relative-path packaging adaptation, algorithm unchanged."""
from pathlib import Path
if not __debug__:
    raise SystemExit("Assertions are required; do not use -O or PYTHONOPTIMIZE.")
exec(Path(__file__).with_name('arbitrary_helpers_milp.py').read_text().split("print('MILP'")[0])
from scipy.optimize import linprog
from fractions import Fraction as F
lp=linprog(obj,A_ub=A.tocsr(),b_ub=np.array(ub),bounds=(0,1),method='highs')
print('LP',lp.success,lp.fun,flush=True)
y=[F(float(v)).limit_denominator(1000000) for v in lp.ineqlin.marginals]
z=[F(float(v)).limit_denominator(1000000) for v in lp.upper.marginals]
print('DUAL',[(i,str(v))for i,v in enumerate(y)if v],[(i,str(v))for i,v in enumerate(z)if v],flush=True)
assert all(v<=0 for v in y+z)
cols=[F(0) for _ in obj]
for row,coef in zip(constraints,y):
 for j,v in row.items():cols[j]+=coef*v
assert all(cols[j]+z[j]<=int(obj[j])for j in range(len(obj)))
bound=sum(F(int(b))*yy for b,yy in zip(ub,y))+sum(z)
assert bound==F(-7)
record={'scope':'Primary PA194 raw201 grammar, arbitrary number of direct selector helpers with existing raw-state destinations, disjoint incoming-bit folds. A relaxation, so obstruction applies before simultaneous compatibility. Not a lower bound on general TMs or re-associated grammars.', 'variables':nh+ne,'helpers':allhelpers,'fold_pairs':edges,'objective':list(map(int,obj)),'constraints':[{str(j):v for j,v in row.items()}for row in constraints],'upper_bounds':list(map(int,ub)),'dual_constraints':[str(v)for v in y],'dual_upper_variables':[str(v)for v in z],'lower_bound':str(bound),'final_state_lower_bound':len(qs)+int(bound)}
(OUTPUT_DIR/'helper_lp_certificate.json').write_text(json.dumps(record,separators=(',',':'))+'\n')
print('VERIFIED EXACT DUAL',bound,'FINAL>=',len(qs)+int(bound),flush=True)
