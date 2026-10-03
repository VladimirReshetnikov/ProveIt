"""The literal gamma=rho*sigma 86-gate shortcut has empty valid slices.

Finite exact audits support the accompanying all-index proof.  This is
an obstruction packet, not a universal 86-operation representation.
"""
import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import random

import sympy as sp
import complete75_normalized_strong87 as parent


def sources():
    _, old, pairs, _ = parent.sources()
    nodes = {n:(op,a,b) for n,op,a,b in old}
    assert nodes.pop('gamma_sum') == ('+', 'rho', 'sigma')
    assert nodes['gam'] == ('*', 'gamma_sum', 'a4m5')
    assert nodes['modulus_multiple'] == ('*', 'rho', 'a4m5')
    nodes['gam'] = ('*', 'sigma', 'modulus_multiple')
    free = parent.RETAINED + parent.eliminated.baseline.prior.CONSTANTS + [
        'x','Bm1','Kconstant','twice_cell_bits']
    done, active, source = set(free), set(), []
    def visit(n):
        if type(n) is int or n in done:
            return
        assert n not in active, n
        active.add(n)
        op,a,b = nodes[n]
        visit(a); visit(b)
        source.append((n,op,a,b))
        active.remove(n); done.add(n)
    for a,b in pairs:
        visit(a); visit(b)
    assert len(source) == len(nodes) == 85
    before = {n:(op,a,b) for n,op,a,b in old}
    assert set(before)-set(nodes) == {'gamma_sum'}
    assert {n for n in nodes if nodes[n] != before[n]} == {'gam'}
    assert pairs == [('eight_units',1)]
    return source, pairs, source+[('polynomial','-','eight_units',1)]


def trim(p):
    p = list(p)
    while len(p)>1 and not p[-1]:
        p.pop()
    return p


def add(p,q):
    r = [0]*max(len(p),len(q))
    for i,c in enumerate(p): r[i] += c
    for i,c in enumerate(q): r[i] += c
    return trim(r)


def scale(p,c):
    return trim([c*v for v in p])


def evaluate(p,x):
    out = 0
    for c in reversed(p): out = out*x+c
    return out


def norm(p):
    return sum(abs(c) for c in p)


def gamma_polynomials(limit):
    out = [[0],[0],[1]]
    for n in range(3,limit+1):
        out.append(add(add([0]+scale(out[-1],2),scale(out[-2],-1)),[2**(n-2)]))
    return out[:limit+1]


def pseudo_remainder(f,g):
    """Return r,Q,s with r=lc(g)^s*f-Q*g, deg(r)<deg(g)."""
    r,Q,s = list(f),[0],0
    a0,d = g[-1],len(g)-1
    while r != [0] and len(r)-1 >= d:
        shift, lead = len(r)-1-d,r[-1]
        r = add(scale(r,a0),[0]*shift+scale(g,-lead))
        Q = add(scale(Q,a0),[0]*shift+[lead])
        s += 1
    return r,Q,s


def verify_source():
    source,pairs,polynomial = sources()
    oldpoly = parent.sources()[3]
    counts = Counter('M' if op=='*' else 'A' for _,op,_,_ in polynomial)
    assert counts == {'M':48,'A':38}
    rng = random.Random(860316)
    cases = Counter()
    for case in range(384):
        signed = case >= 256
        v = {n:rng.randrange(-7,8) if signed else rng.randrange(1,8)
             for n in parent.RETAINED+['x']}
        if case < 32: v['sigma'] = 1
        B = (16,32,64,256)[case%4]
        fixed = dict(B=B,DC=3,DR=5,MC=B-2,MF=4,
                     cell_bits=B.bit_length()-1,inner_bits=3)
        new = parent.eliminated.run(polynomial,parent.eliminated.fixed_inputs({**v,**fixed}))
        restored = {**v,'sigma':v['rho']*(v['sigma']-1)}
        old = parent.eliminated.run(oldpoly,parent.eliminated.fixed_inputs({**restored,**fixed}))
        assert all(new[n] == old[n] for n,_,_,_ in source)
        assert new['polynomial'] == old['polynomial']
        product = 1
        for n in parent.FACTOR_NAMES: product *= new[n]
        assert new['polynomial'] == product-1
        cases['complete_source_identities'] += 1
        cases['signed_assignments'] += signed
        cases['positive_assignments'] += not signed
        cases['sigma_one_boundary_assignments'] += case < 32
        cases['nonpositive_algebraic_parent_sigma'] += restored['sigma'] <= 0
    return dict(certificate=dict(operations=85,multiplications=48,additions_subtractions=37,
                                 equations=1,witnesses=19),
                polynomial=dict(operations=86,multiplications=48,additions_subtractions=38,
                                witnesses=19),
                parent_sha256=sha256(json.dumps(oldpoly).encode()).hexdigest(),
                retained_positive_witnesses=parent.RETAINED,comparisons=pairs,
                polynomial_schedule=polynomial,checks=dict(cases),
                identity='sigma_parent=rho*(sigma_candidate-1), over integers only')


def verify_polynomials():
    z = sp.Symbol('A')
    gs = gamma_polynomials(99)
    chi,psi = [1],[0]
    checks = Counter()
    for n in range(100):
        left = add([0]+scale(gs[n],4),scale(gs[n],-5))
        right = add(add(chi,scale(add([0]+psi,scale(psi,-2)),-1)),[-2**n])
        assert left == right
        checks['exact_projection_polynomial_identities'] += 1
        if n>=2:
            assert len(gs[n])-1 == n-2 and gs[n][-1] == 2**(n-2)
            assert norm(gs[n]) <= 4**(n-2)
            checks['degree_leading_coefficient_norm_checks'] += 1
        # Multiplication by A+sqrt(A^2-1), independent of G recurrence.
        chi,psi = (add([0]+chi,add([0,0]+psi,scale(psi,-1))),
                   add(chi,[0]+psi))
    endpoints = []
    for u in range(3,40,2):
        lo,hi = evaluate(gs[u],-1),evaluate(gs[u],Fraction(-5,4))
        assert lo >= 0 and hi < 0 and (lo == 0) == (u == 3)
        endpoints.append(dict(u=u,G_minus_one=lo,G_minus_five_fourths=str(hi)))
    records = []
    for u in range(3,20,2):
      for R in range(u+2,4*u+4,2):
        f,g = gs[R],gs[u]
        r,Q,s = pseudo_remainder(f,g)
        assert r != [0] and len(r)-1 < u-2 and s <= R-u+1
        exponent = 2*R-4+(2*u-3)*(R-u+1)
        assert norm(r) <= 2**exponent < 2**((2*u-1)*R)
        F,G = sp.Poly.from_list(list(reversed(f)),z),sp.Poly.from_list(list(reversed(g)),z)
        rr = sp.Poly.from_list(list(reversed(r)),z)
        QQ = sp.Poly.from_list(list(reversed(Q)),z)
        assert g[-1]**s*F-QQ*G == rr
        assert (g[-1]**s*F).rem(G) == rr
        checks['independent_exact_pseudo_remainders'] += 1
        if R == 4*u+1:
            records.append(dict(u=u,R=R,steps=s,remainder_degree=len(r)-1,
                                coefficient_norm_bits=norm(r).bit_length(),
                                bound_exponent=exponent,remainder=r))
    return dict(checks=dict(checks),negative_root_endpoints=endpoints,
                selected_remainders=records)


def verify_large_parameters():
    gs = gamma_polynomials(65)
    records = []
    for u in range(3,16,2):
      for offset in (1,3,5):
        R = 4*u+offset
        X = 2**R
        floor_xi = (X+1)**(R-1)//X**((R-1)//2)
        assert floor_xi % 2 == 0
        Y = floor_xi//2
        A = Y*(X+1)+2
        g,f = gs[u],gs[R]
        r,_,s = pseudo_remainder(f,g)
        assert A >= 2**(R*(R+1)//2-1) > 2**((2*u-1)*R) > norm(r)
        gu,gr,rr = evaluate(g,A),evaluate(f,A),evaluate(r,A)
        assert gu > A**(u-2) > abs(rr) > 0
        assert (g[-1]**s*gr-rr) % gu == 0 and gr % gu != 0
        # Compare the independently exponentiated Pell coefficients too.
        for n,gn in ((u,gu),(R,gr)):
            chi,psi = parent.pell(A,n)
            assert chi-(A-2)*psi-2**n == (4*A-5)*gn
        records.append(dict(u=u,R=R,A_bits=A.bit_length(),
                            gamma_u_bits=gu.bit_length(),gamma_R_bits=gr.bit_length(),
                            nonzero_remainder_bits=abs(rr).bit_length()))
    inequalities = 0
    for q in (16,17,32,64,256,1024):
      for u in range(3,2*q,2):
       for R in (q*q+1,q*q+3,2*q*q+1):
        assert R>4*u and R*(R+1)//2-1 > (2*u-1)*R
        inequalities += 1
    return dict(actual_half_binomial_parameter_fixtures=records,
                compiler_range_exponent_checks=inequalities,
                scope='Parameter/divisibility fixtures only; no complete compiler zeros are asserted.')


def verify():
    return dict(status='PASS_MULTIPLICATIVE_GAMMA86_EMPTY_VALID_SLICES',
                source=verify_source(),polynomials=verify_polynomials(),
                large_parameters=verify_large_parameters(),
                scope='Only the guarded gamma=rho*sigma shortcut, with the full unchanged compiler contract. '
                      'No positive zeros on any valid slice; no universal 86-operation bound.')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result,indent=2)+'\n')
    else: assert json.loads(path.read_text()) == json.loads(json.dumps(result))
    print(result['status'])
    print(result['source']['polynomial'])


if __name__ == '__main__': main()
