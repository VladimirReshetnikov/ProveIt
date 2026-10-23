"""Independent coefficient-elimination and random specialization review."""
from pathlib import Path
import json,hashlib,random
import sympy as s
base=Path(__file__).resolve().parent.parent/'low_degree'
p=json.loads((base/'upstream/integer51_degree4_odd_scale.json').read_text())
n=json.loads((base/'quartic50.json').read_text())
ss={k:s.Symbol(k) for k in p['variables']+p['fixed_numerals']}
old=[s.sympify(r,locals=ss) for r in p['residuals']]
new=[s.sympify(r,locals=ss) for r in n['residuals']]
G=ss['G']; N=ss['N']
# Solve the two defining linear equations independently, then compare all rows.
gsol=s.solve(old[12],G); nsol=s.solve(old[1],N)
assert len(gsol)==len(nsol)==1
mapped=[r.subs(G,gsol[0]) for k,r in enumerate(old) if k!=12]
for a,b in zip(mapped,new): assert s.expand((a-b).subs(N,nsol[0]))==0
assert all(G not in r.free_symbols for r in new)
assert len(n['variables'])==50 and len(new)==29
assert max(s.Poly(r,*[ss[v] for v in n['variables']]).total_degree() for r in new)==2
assert sum(s.Poly(r,ss['tau']).coeff_monomial(ss['tau']**2)**2 for r in new)==1
rng=random.Random(419991); trials=0
for _ in range(128):
 vals={v:rng.randrange(-9,10) for v in ss.values()}
 vals[N]=int(nsol[0].subs(vals)); vals[G]=int(gsol[0].subs(vals))
 assert [int(r.subs(vals)) for k,r in enumerate(old) if k!=12]==[int(r.subs(vals)) for r in new]
 trials+=1
result={'exact_linear_elimination':True,'all_retained_rows_agree_on_N_equation':True,
'variables':50,'quadratic_rows':29,'tau_fourth_coefficient':1,
'signed_specializations':trials,
'candidate_sha256':hashlib.sha256((base/'quartic50.json').read_bytes()).hexdigest()}
Path(__file__).with_name('QUARTIC50_INDEPENDENT_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
