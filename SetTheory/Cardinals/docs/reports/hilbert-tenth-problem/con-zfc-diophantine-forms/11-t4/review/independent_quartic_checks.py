"""Adversarial quartic audit; no upstream executable code is imported."""
import json
from pathlib import Path
import sympy as sp

ROOT=Path(__file__).resolve().parents[1]
checks={}
for stem in ['quartic33_normalized','quartic33_ordinary']:
    data=json.loads((ROOT/'quartic'/f'{stem}.json').read_text())
    names=data['variables']; syms={n:sp.Symbol(n) for n in names}
    syms.update({n:sp.Symbol(n) for n in ['beta','K','MC','MF']})
    syms['q']=syms['beta']*syms['J']+1
    syms['k']=syms['eta']+syms['zeta']
    residuals=[sp.sympify(r,locals=syms) for r in data['residuals']]
    for e,r in zip(data['equations'],residuals,strict=True):
        left,right=e.split(' = ')
        assert sp.expand(sp.sympify(left,locals=syms)-sp.sympify(right,locals=syms)-r)==0
    assert len(names)==len(set(names))==33
    assert len(residuals)==24
    degrees=[sp.Poly(r,*(syms[n] for n in names)).total_degree() for r in residuals]
    assert max(degrees)==2
    tau=syms['tau']
    assert [i+1 for i,r in enumerate(residuals) if r.has(tau)]==[8]
    assert sp.Poly(residuals[7],tau).coeff_monomial(tau**2)==1
    assert sum(sp.expand(r*r).coeff(tau,4) for r in residuals)==1
    checks[stem]={'variables':33,'equations':24,'maximum_residual_degree':2,
        'tau_fourth_coefficient':1,'equation_JSON_residual_match':True}

# Match every unchanged normalized equation against the pinned old quartic.
old=json.loads((ROOT/'quartic'/'sources'/'start_only_quartic34.json').read_text())
new=json.loads((ROOT/'quartic'/'quartic33_normalized.json').read_text())
all_names=set(old['variables']+new['variables']+['Bm1','Kconstant','MC','MF','beta'])
s={n:sp.Symbol(n) for n in all_names}
renames={'Jrep':'J','transport_quotient':'z','auxiliary_quotient':'old_o',
         'tau_root':'tau','y_aux':'y','K':'A','Baux':'B','Bm1':'beta','Kconstant':'K'}
rename_map={s[k]:sp.Symbol(v) for k,v in renames.items()}
old_r=[sp.sympify(r,locals=s).xreplace(rename_map) for r in old['residual_polynomials']]
new_r=[sp.sympify(r,locals=s) for r in new['residuals']]
unchanged=[(i,i) for i in range(10)]+[(13,12),(14,13),(15,14),(16,15),
    (20,19),(21,20),(22,21),(24,23)]
for a,b in unchanged:
    assert sp.expand(old_r[a]-new_r[b])==0
checks['unchanged_source_residuals_matched']=len(unchanged)

# Independently verify factorization, forward identities, reverse identities,
# and both exact inverse quotient formulas in the strong-relation quotient ring.
a,c,f,i,R,T,o,j=sp.symbols('a c f i R T o j')
delta=(a+1)*(a+3)
S=f*f-1-delta*i*i*c**4
U=(a+1)*c
H=(a+1)*(f-1)
assert sp.expand(U*(U+2*c)-delta*c*c)==0
assert sp.expand(H*(H+2*a+2*f+4)-delta*(f*f-1))==0
V=c*(T*f-1)-R*f*f
onew=c*T-R*f
jnew=T*f-R*delta*i*i*c**3-1
assert sp.expand(V-(onew*f-c))==0
assert sp.expand(V-(jnew*c-R)+R*S)==0
assert sp.expand((onew+R*f)/c-T)==0
Tback=(o+R*f)/c
assert sp.expand(c*Tback-R*f-o)==0
# New quotient residual relation: c*j=o*f+R-c.
Q=c*j-o*f-R+c
assert sp.expand(c*(Tback*f-R*delta*i*i*c**3-1-j)-R*S+Q)==0
checks['factorization_and_exact_inverse_identities']='passed'

# Both integer bound polynomials used in the normalized positive lift.
q=sp.symbols('q')
upper=(q*q-q-1)*(q*q-1)+(q-1)*(1+2*q)
assert sp.expand(upper-(q**4-q**3))==0
# v^2-1 >= (B-1)(2v+1); for integers 2<=v<=2B-2, contradiction.
# Substitute v=2B-2-t with 0<=t<=2B-4: the left side becomes
# -B-t(2B-2-t) < 0.
B,t=sp.symbols('B t')
v=2*B-2-t
assert sp.expand(v*v-1-(B-1)*(2*v+1)-(-B-t*(2*B-2-t)))==0
checks['positivity_bound_identities']='passed'
checks['scope']='Symbolic identities, counts and degree only. Integrality and unbounded positivity are reviewed in QUARTIC_REVIEW.md; compiler and endpoint are imported obligations.'
out=ROOT/'review'/'QUARTIC_INDEPENDENT_CHECKS.json'
out.write_text(json.dumps(checks,indent=2)+'\n')
print(out.read_text())
