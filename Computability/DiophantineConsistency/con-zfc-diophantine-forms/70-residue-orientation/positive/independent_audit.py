#!/usr/bin/env python3
"""Independent named-cut polynomial audit, authored separately from build.py."""
from pathlib import Path
import json
from collections import Counter
from independent_ring import Ring, expand, require

ROOT = Path(__file__).resolve().parent


def audit(path):
    d = json.loads(path.read_text())
    is12 = len(d['witnesses']) == 12
    formulas = {
        'J':'3*j+1', 'qm':'J*beta', 'q':'qm+1', 'q2':'q*q', 'q3':'q*q2',
        'qF':'q-F', 'C':'qF-alpha', 'E':'X*Y', 'k':'eta+zeta', 'kY':'k*Y',
        'c':'kY+eta', 'c2':'c*c', 'I':'i*c2', 'a':'E+Y', 'H':'4*a+3',
        'Delta':'a*a+H', 'ac':'a*c', 'b0':'X+ac', 'ell':'E*kY',
        'W':'1+qm*ikc' if is12 else '1+qm*k', 'M':'q3*qm',
        'Bt':'(q*K0+X)*C-q*F',
        'Z0':'M*(ell+k+n)+qm*Y-q3*W*Bt' if is12 else
             'M*(ell+k+r)+qm*Y-q3*W*Bt',
        'rad0':'ell*(ell+k)+1', 'M2':'M*M', 'I2':'I*I',
        'G':'qm*qF+alpha', 'R':'G*(q2-1)+(MC+q*MF)*J',
        'r0':'k-R-1', 'S':'4*q*Y', 'U':'q*S',
        'shift':'U*gamma+S*X-r0', 'Dstar':'U*b0+H*shift',
        'A1':'Dstar*Dstar-U*U*(1+Delta*c2)',
        'Kaux':'Delta*f2m', 'V':('Df' if is12 else 'f2')+'*(c*T-R)-c',
        'y2':'(V+u)*(V+u)', 'Aa':'y2-Kaux*(y2-V*V)-1',
    }
    if is12:
        formulas.update({'ikc':'i*k*c','f2m':'Delta*I2','Df':'f2m+1',
                         'L':'(a+2)*I','Zbar':'Z0+M*L',
                         'center':'Zbar*Zbar-M2*(Df+rad0)',
                         'normtail':'4*M2*M2*Df*rad0','N':'center*center-normtail'})
    else:
        formulas.update({'A0':'Z0*Z0-M2*rad0','f2':'f*f','f2m':'f2-1',
                         'As':'f2m-Delta*I2'})
    names = d['witnesses'] + d['fixed_numerals'] + [row[0] for row in d['source']]
    require(len(names) == len(set(names)), 'duplicate gate or leaf name')
    symbols = {x:Ring.variable(x) for x in names}
    env = {x:symbols[x] for x in d['witnesses']+d['fixed_numerals']}
    counts = Counter()
    seen = set()
    deps = {}
    for name, op, left, right in d['source']:
        a = Ring.numeral(left) if isinstance(left,int) else env[left]
        b = Ring.numeral(right) if isinstance(right,int) else env[right]
        require(op in ['+','-','*'], 'nonpolynomial gate')
        value = a+b if op=='+' else a-b if op=='-' else a*b
        deps[name] = {x for x in [left,right] if isinstance(x,str)}
        counts[op] += 1
        if name in formulas:
            require(value == expand(formulas[name], symbols), 'cut identity failed: '+name)
            seen.add(name)
            env[name] = symbols[name]
        else:
            env[name] = value
    require(seen == set(formulas), 'unchecked/missing named cut')
    expected = sum(symbols[x]**2 for x in d['residuals'])
    require(env[d['output']] == expected, 'final sum of squares mismatch')
    live=set()
    def visit(x):
        if x in live:
            return
        live.add(x)
        for y in deps.get(x,()):
            visit(y)
    visit(d['output'])
    require(live == set(names), 'dead gate or leaf')
    require(sum(counts.values()) == d['operations'], 'operation count mismatch')
    require(dict(counts) == d['operation_breakdown'], 'operation breakdown mismatch')
    require(d['operations'] == (103 if is12 else 94), 'wrong expected comparison count')
    return {'name':d['name'], 'variables':len(d['witnesses']),
            'operations':sum(counts.values()),'breakdown':dict(counts),
            'exact_named_cuts':len(seen),'all_gates_and_inputs_live':True}


def main():
    circuits = [audit(ROOT/'p12_positive_degree84.json'),
                audit(ROOT/'p13_positive_degree30.json')]
    sy={x:Ring.variable(x) for x in
        ['Z','M','a','b','L','I','T','j','beta','K0','F','alpha','i','eta','zeta','X','Y']}
    # Generic norm identity, including the formula supplying the rational strong root.
    norm = expand('(Z*Z-M*M*(a+b))**2-4*M**4*a*b',sy)
    alternative = expand('(Z*Z+M*M*(b-a))**2-4*M*M*Z*Z*b',sy)
    require(norm == alternative,'generic norm identity')
    # Resolve the degree cancellation without evaluating a bounded sample.
    env=dict(sy,Z=sy['T']+sy['M']*sy['L'],b=sy['L']**2+1-sy['I']**2)
    center=expand('Z*Z-M*M*(a+b)',env)
    centered=expand('T*T+2*M*L*T-M*M*(1-I*I+a)',sy)
    require(center==centered,'center cancellation identity')
    # Validate the displayed leading forms and fixed-port-independent coefficients.
    q0=3*sy['beta']*sy['j']; k0=sy['eta']+sy['zeta']
    bt=(sy['K0']*q0+sy['X'])*(q0-sy['F']-sy['alpha'])-q0*sy['F']
    top84=16*q0**32*sy['i']**8*k0**16*sy['X']**4*sy['Y']**16*bt**4
    top30=4*q0**16*k0**4*sy['X']**2*sy['Y']**4*bt**2
    unknowns={'j','F','alpha','i','eta','zeta','X','Y'}
    require(top84.degree(unknowns)==84,'degree84 homogeneous leader')
    require(top30.degree(unknowns)==30,'degree30 homogeneous leader')
    c84=top84.coefficient({'j':32,'i':8,'eta':16,'X':8,'Y':16,'alpha':4},unknowns)
    c30=top30.coefficient({'j':16,'eta':4,'X':4,'Y':4,'alpha':2},unknowns)
    require(c84==16*(3*sy['beta'])**32,'degree84 coefficient')
    require(c30==4*(3*sy['beta'])**16,'degree30 coefficient')
    result={'status':'PASS','scope':'independent exact gate contracts, cut-ring identities, liveness, counts, degree leaders',
            'circuits':circuits,'generic_norm_identity':True,'center_cancellation_identity':True,
            'selected_degree84_coefficient':'16*(3*beta)^32',
            'selected_degree30_coefficient':'4*(3*beta)^16',
            'degree_upper_bound_proof':'See independent mathematical review; N<=42, A1<=13, Aa<=37; unique top component gives84.'}
    (ROOT/'INDEPENDENT_AUDIT.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
