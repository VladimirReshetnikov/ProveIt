#!/usr/bin/env python3
"""Generate and audit squared-modulus auxiliary quotient circuits.

Only Python's standard library is needed.  This script verifies finite source
identities, liveness, degree, and recurrence examples.  It does not certify
the unbounded native-window compiler or the consistency equivalence.
"""
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PIN = '124c07c0b77a9e20e84676514d8b1ff78536ea3f'


def require(b, message):
    if not b:
        raise ValueError(message)


def plus(p, q, sign=1):
    r = dict(p)
    for a, c in q.items():
        r[a] = r.get(a, 0) + sign*c
        if not r[a]:
            del r[a]
    return r


def times(p, q):
    r = {}
    for a, c in p.items():
        for b, d in q.items():
            k = tuple(x+y for x, y in zip(a, b))
            r[k] = r.get(k, 0) + c*d
    return {a: c for a, c in r.items() if c}


def ring(names):
    z = (0,)*len(names)
    def const(n):
        return {z: n} if n else {}
    def var(n):
        p = list(z)
        p[names.index(n)] = 1
        return {tuple(p): 1}
    return const, var


def power(p, n, one):
    r = one
    for _ in range(n):
        r = times(r, p)
    return r


OLD_BLOCK = [
    ['auxiliary_Tf', '*', 'T', 'f'],
    ['auxiliary_Tf_minus_one', '-', 'auxiliary_Tf', 1],
    ['auxiliary_c_Tf', '*', 'R10a', 'auxiliary_Tf_minus_one'],
    ['auxiliary_R_f2', '*', 'r_lhs', 'L16'],
    ['aux_u_rhs', '-', 'auxiliary_c_Tf', 'auxiliary_R_f2'],
]
NEW_BLOCK = [
    ['auxiliary_c_T', '*', 'R10a', 'T'],
    ['auxiliary_c_T_minus_R', '-', 'auxiliary_c_T', 'r_lhs'],
    ['auxiliary_f2_times_inner', '*', 'L16', 'auxiliary_c_T_minus_R'],
    ['aux_u_rhs', '-', 'auxiliary_f2_times_inner', 'R10a'],
]


def transform(p, source_name, degree):
    p = deepcopy(p)
    rows = p['source']
    start = next(i for i, r in enumerate(rows) if r[0] == 'auxiliary_Tf')
    require(rows[start:start+5] == OLD_BLOCK, 'unexpected parent V block')
    p['source'] = rows[:start] + NEW_BLOCK + rows[start+5:]
    p['name'] = 'square_modulus_' + p['name']
    p['exact_degree'] = degree
    p.pop('ledger', None)
    p.pop('proof', None)
    p['provenance'] = dict(commit=PIN, source='../upstream/'+source_name,
                           sha256=sha256((ROOT/'upstream'/source_name).read_bytes()).hexdigest(),
                           change='Replace the five-gate V block by four gates, imposing T_old=f*T.')
    p['coefficient_binding'] = dict(file='../coefficients/COEFFICIENT_BINDING.json',
                                   aliases=dict(beta='beta', K0='K', MC='MC', MF='MF_source'),
                                   warning='Use the complete package-36 tuple; MF_source is already shifted.')
    p['proof_boundary'] = ('Existential projection, not identical zero sets. Soundness is the literal '
                          'substitution T_old=f*T. Completeness uses the proved squared-modulus '
                          'Chebyshev congruence and the inherited authentic-compiler theorem. '
                          'No new Lean kernel certificate is claimed.')
    return p


def local_identities():
    c, v = ring(['c', 'f', 'T', 'R', 'a', 'X', 'H', 'gamma'])
    C, F, T, R, a, X, H, g = [v(n) for n in ['c','f','T','R','a','X','H','gamma']]
    f2 = times(F,F)
    old = plus(times(C, plus(times(times(F,T),F), c(1), -1)), times(R,f2), -1)
    new = plus(times(f2, plus(times(C,T),R,-1)), C, -1)
    require(old == new, 'exact V pullback identity')
    ac = times(a,C)
    xg = plus(X,times(g,H))
    D = plus(ac,xg)
    delta = plus(times(a,a),H)
    norm = plus(times(D,D), times(delta,times(C,C)), -1)
    reduced = plus(plus(times(c(2),times(ac,xg)),times(xg,xg)),times(H,times(C,C)),-1)
    require(norm == reduced, 'exact main norm cancellation identity')
    return dict(V_pullback=True, main_norm_cancellation=True)


def audit_graph(p):
    witnesses, fixed = p['witnesses'], p['fixed_numerals']
    names = witnesses + fixed
    const, var = ring(names)
    one = const(1)
    deg = {n: (1 if n in witnesses else 0, var(n)) for n in names}
    prods = {}
    count = Counter()
    def get(x):
        if type(x) is int:
            return 0,const(x)
        require(x in deg, 'undefined operand '+str(x))
        return deg[x]
    for row in p['source']:
        require(len(row)==4, 'row size')
        n, op, a, b = row
        require(n not in deg and op in ('+','-','*'), 'gate definition')
        da,pa = get(a)
        db,pb = get(b)
        if op=='*':
            d,t = da+db,times(pa,pb)
        else:
            d=max(da,db)
            t=plus(pa if da==d else {},pb if db==d else {},1 if op=='+' else -1)
        if n=='norm_main':
            # The exact all-ring identity was checked independently above.
            # Here a,c,X,H,gamma have degrees 6,5,2,6,1 respectively.
            a_top=deg['R12'][1]
            c_top=deg['R10a'][1]
            t=times(const(8),times(var('gamma'),times(times(a_top,a_top),c_top)))
            d=18
        require(all(sum(e[:len(witnesses)])==d for e in t), 'inhomogeneous top')
        deg[n]=(d,t)
        prods[n]=(a,b)
        count[op]+=1
    live=set()
    todo=[p['output']]
    while todo:
        n=todo.pop()
        if type(n) is int or n in live:
            continue
        live.add(n)
        if n in prods:
            todo.extend(prods[n])
    require(live==set(deg), 'dead gates or ports '+str(set(deg)-live))
    d,top=deg[p['output']]
    require(d==p['exact_degree'] and top, 'exact degree mismatch')
    if len(p['source'])==66:
        target=dict(J=92,h=1,gamma=1,i=4,eta=13,w=13,s=26,T=2,f=4,z=1,beta=92)
        coefficient=8
    elif len(p['source'])==74:
        target=dict(J=40,eta=8,i=4,w=4,s=12,beta=40)
        coefficient=1
    elif len(p['source'])==72:
        target=dict(J=50,eta=6,gamma=2,w=8,s=14,beta=50)
        coefficient=64
    elif len(p['source'])==68:
        target=dict(J=64,h=1,gamma=1,i=2,eta=9,w=9,s=18,T=2,f=6,z=1,beta=64)
        coefficient=8
    else:
        raise ValueError('unexpected circuit size')
    require(top.get(tuple(target.get(n,0) for n in names))==coefficient,'leading certificate')
    return dict(operations=len(p['source']),multiplications=count['*'],
                additions=count['+'],subtractions=count['-'],all_gates_live=True,
                all_ports_live=True,witnesses=len(witnesses),fixed_ports=len(fixed),
                exact_degree=d,distinguished_monomial={k:v for k,v in target.items() if k!='beta'},
                distinguished_coefficient=str(coefficient)+'*beta^'+str(target['beta']),
                nonvanishing_hypothesis='beta != 0',
                factor_degrees={n:deg[n][0] for n in ['norm_first','norm_main','norm_aux','norm_index','norm_transport']})


def evaluate(p, values, modulus):
    e=dict(values)
    def get(x): return x if type(x) is int else e[x]
    for n,op,a,b in p['source']:
        aa,bb=get(a),get(b)
        e[n]=({'+' : lambda:aa+bb,'-':lambda:aa-bb,'*':lambda:aa*bb}[op]())%modulus
    return e[p['output']]


def pell(a,n):
    x,y=1,0
    for _ in range(n):
        x,y=a*x+(a*a-1)*y,x+a*y
    return x,y


def polynomial_quotient_examples():
    cases=0
    # Genuine auxiliary reconstructions for small independent Pell fibers.
    # These are not asserted to encode a K215 computation.
    for A in range(2,6):
        for R in [3,7]:
            delta=A*A-1
            _,c=pell(A,R)
            # Directly use a modulus of the required form for congruence
            # tests; no claim that this modulus is a square is needed here.
            for i in [1,2,3]:
                F2=1+delta*i*i*c**4
                S=delta*i*c*c
                x,y=pell(S,R)
                require(x%S==0,'odd quotient integral')
                V=x//S
                require((V+c)%F2==0,'squared-modulus congruence')
                require((V+R)%c==0,'main-ordinate congruence')
                numerator=V+c+R*F2
                require(numerator%(c*F2)==0,'CRT quotient integral')
                T=numerator//(c*F2)
                require(T>0 and V==F2*(c*T-R)-c,'positive reconstruction')
                require(S*S*(V*V-y*y)+y*y==1,'auxiliary norm')
                cases+=1
    return cases


def main():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    require(pins['commit']==PIN,'source commit mismatch')
    for item in pins['files']:
        require(sha256((ROOT/item['file']).read_bytes()).hexdigest()==item['sha256'],
                'source hash mismatch: '+item['file'])
    local=local_identities()
    specs=[('product67.json','p66_degree157.json',157),
           ('p69_unscaled.json','p68_degree113.json',113),
           ('p73_sos.json','p72_degree80.json',80),
           ('p75_sos.json','p74_degree68.json',68)]
    receipts={}
    for source,output,degree in specs:
        parent=json.loads((ROOT/'upstream'/source).read_text())
        child=transform(parent,source,degree)
        audit=audit_graph(child)
        for seed in range(1,101):
            inputs={n:(seed*seed+17*j+seed*j*j)%1009-500
                    for j,n in enumerate(parent['witnesses']+parent['fixed_numerals'])}
            old=dict(inputs)
            old['T']=inputs['f']*inputs['T']
            require(evaluate(parent,old,1000000007)==evaluate(child,inputs,1000000007),
                    'full pullback diagnostic')
        encoded=json.dumps(child,indent=2)+'\n'
        (ROOT/'generated'/output).write_text(encoded)
        audit['circuit_sha256']=sha256(encoded.encode()).hexdigest()
        audit['source_sha256']=child['provenance']['sha256']
        audit['full_pullback_modular_examples']=100
        receipts[output]=audit
    result=dict(commit=PIN,exact_cut_identities=local,
                auxiliary_reconstruction_examples=polynomial_quotient_examples(),
                circuits=receipts,
                limitation='Finite audits do not prove the unbounded compiler or Con(ZFC) equivalence.')
    (ROOT/'generated'/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
