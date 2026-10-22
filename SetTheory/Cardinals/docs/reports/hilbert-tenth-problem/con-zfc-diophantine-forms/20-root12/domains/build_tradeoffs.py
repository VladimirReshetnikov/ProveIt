#!/usr/bin/env python3
"""Exact guarded-coordinate elimination frontier for the frozen low-degree parents."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from instance_binding import binding
import hashlib,itertools,json
from sparse_poly import Poly
ROOT=Path(__file__).resolve().parent
PARENTS=ROOT/'sources/15-release/evidence/diophantine_zfc_round2/quadratic'
GUARDS='Jrep F alpha transport_quotient s eta zeta'.split()
CONSTANTS=['Bm1','Kconstant','MC','MF']
results=[]
for filename,targets in [('ordinary_octic20.json',[4,5,6,8]),('start_only_sextic25.json',[3])]:
    packet=json.loads((PARENTS/filename).read_text())
    names=packet['variables']
    env={n:Poly.var(n) for n in names+CONSTANTS}
    original=[eval(s,{'__builtins__':{}},env) for s in packet['residual_polynomials']]
    sub={'i':2*Poly.var('r')+1,'w':Poly.var('u')**2}
    parameters=[]
    for v in GUARDS:
        us=[f'{v}_pos{j}' for j in (1,2,3)]
        x,y,z=map(Poly.var,us)
        parameters+=us
        sub[v]=1+x*x+y*y+z*(z+1)
    all_vars=set(names+parameters+['r','u'])-{'i'}
    choices=GUARDS+['w']
    for target in targets:
        feasible=[]
        for count in range(9):
            for vs in itertools.combinations(choices,count):
                selected={k:v for k,v in sub.items() if k=='i' or k in vs}
                residuals=[p.substitute(selected) for p in original]
                vars=[('r' if n=='i' else n) for n in names if n not in vs]+parameters+['u']
                # All eight constraints remain necessary unless eliminated identically.
                residuals += [Poly.var(v)-sub[v] for v in choices if v not in vs]
                degrees=[p.degree(vars) for p in residuals]
                if max(degrees)<=target:
                    feasible.append((len(vars),vs,vars,residuals,degrees))
        n,removed,vars,res,degrees=min(feasible,key=lambda x:(x[0],x[1]))
        poly=sum((p*p for p in res),Poly(0))
        degree=poly.degree(vars)
        assert degree==2*target
        exact_certificate={}
        if filename=='start_only_sextic25.json':
            key=(('Bm1',2),('Jrep',2),('L',2),('s',2))
            assert poly.terms[key]==1
            exact_certificate={'variable_monomial':'Jrep^2*L^2*s^2','coefficient':'Bm1^2 > 0'}
        elif n==39:
            key=(('Bm1',6),('Jrep',6),('s',2))
            assert poly.terms[key]==1
            exact_certificate={'variable_monomial':'Jrep^6*s^2','coefficient':'Bm1^6 > 0'}
        assert len(set(vars))==n
        assert set().union(*(p.symbols for p in res))==set(vars+CONSTANTS)
        # Evaluation identity after eliminating remaining constraints.
        assert [p.substitute(sub) for p in res[:len(original)]]==[p.substitute(sub) for p in original]
        assert all(p.substitute(sub)==0 for p in res[len(original):])
        name=f'integer{n}_degree{degree}'
        artifact={
            'name':name,'domain':'unrestricted integers','variables':vars,'variable_count':n,
            'fixed_numerals':CONSTANTS,'coefficient_binding':binding(CONSTANTS),
            'historical_source_provenance':{'old_binding':'ORIGINAL_COEFFICIENTS.json, coherent original blank67 tuple','role':'Historical parent only; the complete selected tuple is in coefficient_binding'},
            'source_commit':'f0ae4e0991ca44a7bb4e5671d42e33d775e48035',
            'parent_file':str((PARENTS/filename).relative_to(ROOT)),
            'parent_sha256':hashlib.sha256((PARENTS/filename).read_bytes()).hexdigest(),
            'direct_substitutions':{v:str(sub[v]) for v in removed},
            'odd_multiplier':str(sub['i']),
            'retained_guard_coordinates':[v for v in choices if v not in removed],
            'residuals':[str(p) for p in res],'equation_count':len(res),
            'residual_degrees':degrees,'exact_degree':degree,
            'single_polynomial':'sum of squares of the listed residuals',
            'exact_degree_certificate':exact_certificate,
            'expanded_symbolic_terms':len(poly.terms),
            'proof':'DOMAIN_REDUCTION_PROOF.md, Low-degree elimination frontier appendix',
            'scope':'Exact sparse-polynomial audit plus ordinary signed-domain proof; not kernel checked'
        }
        (ROOT/(name+'.json')).write_text(json.dumps(artifact,indent=2)+'\n')
        results.append({k:artifact[k] for k in ['name','variable_count','equation_count','exact_degree','direct_substitutions','retained_guard_coordinates','expanded_symbolic_terms']})
(ROOT/'TRADEOFF_CHECKS.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
