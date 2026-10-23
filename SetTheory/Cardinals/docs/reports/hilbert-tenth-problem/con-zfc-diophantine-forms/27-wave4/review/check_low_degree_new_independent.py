#!/usr/bin/env python3
"""Independent exact SymPy audit of odd-scale low-degree substitutions."""
from pathlib import Path
import hashlib,json
import sympy as sp
ROOT=Path(__file__).resolve().parents[1]
oldroot=ROOT/'integers/sources/previous-deliverable/domains'
records=[]
for name in ['integer51_degree4','integer42_degree6','integer36_degree8']:
    p=json.loads((ROOT/'integers'/f'{name}.json').read_text())
    oldpath=oldroot/p['source_parent'];q=json.loads(oldpath.read_text())
    assert hashlib.sha256(oldpath.read_bytes()).hexdigest()==p['source_parent_sha256']
    constants=p['fixed_numerals'];symbols={n:sp.Symbol(n) for n in set(q['variables']+p['variables']+constants)}
    old=[sp.sympify(v,locals=symbols) for v in q['residuals']]
    new=[sp.sympify(v,locals=symbols) for v in p['residuals']]
    guard=symbols['s']-1-symbols['s_pos1']**2-symbols['s_pos2']**2-symbols['s_pos3']*(symbols['s_pos3']+1)
    indices=[j for j,r in enumerate(old) if sp.expand(r-guard)==0]
    assert len(indices)==1
    expected=[sp.expand(r.subs(symbols['s'],2*symbols['s_odd']+1)) for j,r in enumerate(old) if j!=indices[0]]
    assert len(expected)==len(new)
    assert all(sp.expand(a-b)==0 for a,b in zip(expected,new))
    assert set().union(*(r.free_symbols for r in new))=={symbols[n] for n in p['variables']+constants}
    assert len(p['variables'])==p['variable_count'] and len(new)==p['equation_count']
    vari=[symbols[n] for n in p['variables']]
    degrees=[sp.Poly(r,*vari).total_degree() for r in new]
    assert degrees==p['residual_degrees']
    sos=sp.Poly(sp.expand(sum(r*r for r in new)),*vari)
    assert sos.total_degree()==p['exact_degree']
    if p['exact_degree']==4:
        cert=sos.coeff_monomial(symbols['tau']**4);assert cert==1
    elif p['exact_degree']==6:
        cert=sos.coeff_monomial(symbols['Jrep']**2*symbols['L']**2*symbols['s_odd']**2);assert cert==4*symbols['Bm1']**2
    else:
        cert=sos.coeff_monomial(symbols['Jrep']**6*symbols['s_odd']**2);assert cert==4*symbols['Bm1']**6
    records.append({'packet':name,'unknowns':len(vari),'equations':len(new),'exact_degree':sos.total_degree(),'coefficient_certificate':str(cert),'parent_hash_verified':True,'exact_residual_substitutions_verified':len(new)})
receipt={'scope':'Exact polynomial substitutions, liveness, and degree certificates. Signed-domain semantics are reviewed separately and depend on source rank/compiler theorems.','packets':records}
(ROOT/'review/LOW_DEGREE_NEW_INDEPENDENT_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
