#!/usr/bin/env python3
"""Remove only the s positivity guard using the proved odd signed-scale domain.
This preserves the old literal low-degree residuals under s=2*s_odd+1.
"""
from pathlib import Path
import sys,json,hashlib
HERE=Path(__file__).resolve().parent
OLD=HERE/'sources/previous-deliverable/domains'
sys.path.insert(0,str(OLD));from sparse_poly import Poly
from build_integer24 import BIND
TARGETS=[('integer54_quartic.json',51,4),('integer45_degree6.json',42,6),('integer39_degree8.json',36,8)]
checks=[]
for filename,count,degree in TARGETS:
    p=json.loads((OLD/filename).read_text());names=p['variables'];constants=p.get('fixed_numerals',p.get('fixed_integer_coefficients'))
    env={n:Poly.var(n) for n in names+constants};old=[eval(x,{'__builtins__':{}},env) for x in p['residuals']]
    added=['s_pos1','s_pos2','s_pos3'];assert set(added)<=set(names) and 's' in names
    guard=Poly.var('s')-1-Poly.var(added[0])**2-Poly.var(added[1])**2-Poly.var(added[2])*(Poly.var(added[2])+1)
    assert old.count(guard)==1
    sub={'s':2*Poly.var('s_odd')+1}
    res=[x.substitute(sub) for x in old if x!=guard]
    variables=[('s_odd' if n=='s' else n) for n in names if n not in added]
    assert len(variables)==count and len(set(variables))==count
    assert set().union(*(x.symbols for x in res))==set(variables+constants)
    degs=[x.degree(variables) for x in res];assert max(degs)==degree//2
    polynomial=sum((x*x for x in res),Poly(0));assert polynomial.degree(variables)==degree
    # Recover the removed positivity parameters only after arithmetic soundness has proved s>0.
    if degree==4:assert polynomial.terms[(('tau',4),)]==1;cert={'monomial':'tau^4','coefficient':'1'}
    elif degree==6:
        key=(('Bm1',2),('Jrep',2),('L',2),('s_odd',2));assert polynomial.terms[key]==4;cert={'monomial':'Jrep^2 L^2 s_odd^2','coefficient':'4 Bm1^2 > 0'}
    elif degree==8:
        key=(('Bm1',6),('Jrep',6),('s_odd',2));assert polynomial.terms[key]==4;cert={'monomial':'Jrep^6 s_odd^2','coefficient':'4 Bm1^6 > 0'}
    else:cert={'proof':'Highest homogeneous component is a sum of squares of at least one nonzero highest residual form; disjoint substitutions preserve nonvanishing.'}
    out={'name':f'integer{count}_degree{degree}','domain':'unrestricted integers','variables':variables,'variable_count':count,'fixed_numerals':constants,'coefficient_binding':dict(BIND,local_port_aliases={n: {'Bm1':'beta','Kconstant':'K0'}.get(n,n) for n in constants}),'source_parent':filename,'source_parent_sha256':hashlib.sha256((OLD/filename).read_bytes()).hexdigest(),'transformation':'Remove s=Pos guard and its three parameters; substitute s=2*s_odd+1. All other residuals unchanged.','residuals':[str(x) for x in res],'equation_count':len(res),'residual_degrees':degs,'exact_degree':degree,'single_polynomial':'sum of squares of the listed residuals','exact_degree_certificate':cert,'expanded_symbolic_terms':len(polynomial.terms),'proof':'LOW_DEGREE_PROOF.md','verification_scope':'Finite exact polynomial identities and degree audit; ordinary signed-domain proof, not kernel checked.'}
    (HERE/(out['name']+'.json')).write_text(json.dumps(out,indent=2)+'\n');checks.append({k:out[k] for k in ['name','variable_count','equation_count','exact_degree','exact_degree_certificate','expanded_symbolic_terms']})
(HERE/'LOW_DEGREE_CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n');print(json.dumps(checks,indent=2))
