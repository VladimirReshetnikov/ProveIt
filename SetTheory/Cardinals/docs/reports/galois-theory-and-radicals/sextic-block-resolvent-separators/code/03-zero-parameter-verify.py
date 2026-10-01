"""Reproduce exact checks; defaults to rerun/ so delivered records stay intact."""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import combinations
from pathlib import Path
import json
import platform
import random
import time
import sympy as sp
from sympy.polys.numberfields import galois_group
from sextic_resolvents import (
    X, Z, companion, matching_resolvent, triple_resolvent,
    zero_matching_resolvent, rational_roots, decide_irreducible_sextic,
    pfaffian, middle_pairing, wedge_matrix, triple_operator,
)


def matchings(vertices):
    if not vertices:
        yield ()
        return
    i, *rest = vertices
    for j in rest:
        for tail in matchings([k for k in rest if k != j]):
            yield ((i, j),) + tail


M = list(matchings(list(range(6))))
PENTADS = [p for p in combinations(range(15), 5)
           if len({e for i in p for e in M[i]}) == 15]
TRIPLES = [(I, tuple(i for i in range(6) if i not in I))
           for I in combinations(range(6), 3) if 0 in I]


def abc(roots, matching):
    p = [roots[i]*roots[j] for i, j in matching]
    s = [roots[i]+roots[j] for i, j in matching]
    return (sum(p), sum(s[i]*p[j] for i in range(3) for j in range(3) if i != j),
            sum(p[i]*p[j] for i in range(3) for j in range(i+1, 3)))


def direct_resolvents(roots):
    A = [abc(roots, m)[0] for m in M]
    B = [sp.prod(roots[i] for i in I)+sp.prod(roots[i] for i in J)
         for I, J in TRIPLES]
    C = [abc(roots, m)[2] for m in M]
    return tuple(sp.Poly(sp.prod(Z-r for r in values), Z)
                 for values in (A, B, [-v for v in C]))


# Explicitly transcribed from SymPy 1.14.0's degree-six Galois test cases.
# These are regression examples, not a classification used in the proof.
SEEDS = [
    ('C6', X**6+X**3+1),
    ('S3', X**6+108),
    ('D6', X**6+2),
    ('A4', X**6-3*X**2-1),
    ('G18', X**6+3*X**3+3),
    ('A4xC2', X**6-3*X**2+1),
    ('S4p', X**6-4*X**2-1),
    ('S4m', X**6-3*X**5+6*X**4-7*X**3+2*X**2+X-4),
    ('G36m', X**6+2*X**3-2),
    ('S4xC2', X**6+2*X**2+2),
    ('PSL2F5', X**6+10*X**5+55*X**4+140*X**3+175*X**2+170*X+25),
    ('PGL2F5', X**6+10*X**5+55*X**4+140*X**3+175*X**2-3019*X+25),
    ('G36p', X**6+6*X**4+2*X**3+9*X**2+6*X-4),
    ('G72', X**6+2*X**4+2*X**3+X**2+2*X+2),
    ('A6', X**6+24*X-20),
    ('S6', X**6+X+1),
]


def roots_json(poly):
    return {str(r): int(m) for r, m in rational_roots(poly).items()}


def run():
    start = time.monotonic()
    checks = {}
    # 1. The proof certificate is a universal polynomial identity.
    a,b,c,d = sp.symbols('a b c d')
    F = [-a*b+b*d-c*d+c, -a*b+a*c-c*d+d,
         -a*b+a*d+b-c*d, -a*b+a+b*c-c*d]
    H = [-(a*a*b-a*a*c+a*b-a-b*c+b+2*c*d-2*d),
         a*a-a*b*b+a*b*c+a*b-a*c+b*b-2*b*d,
         (b-1)*(a*b-a*c+a-c), (a*a+1)*(b-c)]
    assert sp.expand(sum(h*f for h,f in zip(H,F))-2*c*(c-1)*d*(d-1)) == 0
    canon = [((0,1),(2,3),(4,5)), ((0,2),(1,4),(3,5)),
             ((0,3),(1,5),(2,4)), ((0,4),(1,3),(2,5)),
             ((0,5),(1,2),(3,4))]
    av = [abc([0,1,a,b,c,d], m)[0] for m in canon]
    assert all(sp.expand(av[i+1]-av[0]-F[i]) == 0 for i in range(4))
    checks['pentad_identity'] = True
    # 2. Incidence geometry, affine formulas, sum identities.
    assert len(M)==15 and len(PENTADS)==6 and len(TRIPLES)==10
    assert all(sum(i in p for p in PENTADS)==2 for i in range(15))
    assert all(len(set(p)&set(q))==1 for p,q in combinations(PENTADS,2))
    roots = sp.symbols('r0:6'); t=sp.Symbol('t')
    vals = [abc(roots,m) for m in M]
    shifted = [abc([r+t for r in roots],m) for m in M]
    for i in range(1,15):
        da,db,dc = (vals[i][j]-vals[0][j] for j in range(3))
        assert sp.expand(shifted[i][0]-shifted[0][0]-da)==0
        assert sp.expand(shifted[i][1]-shifted[0][1]-db-2*t*da)==0
        assert sp.expand(shifted[i][2]-shifted[0][2]-dc-t*db-t*t*da)==0
    for pentad in PENTADS:
        for k,mult,col in [(2,1,0),(3,3,1),(4,1,2)]:
            e=sum(sp.prod(q) for q in combinations(roots,k))
            assert sp.expand(sum(vals[i][col] for i in pentad)-mult*e)==0
    checks['incidence_and_affine_identities']=True
    # 3. Four-root cubic and translated-root rank formula.
    r0,r1,r2,r3=sp.symbols('u0:4')
    four=[r0,r1,r2,r3]
    ee=[sum(sp.prod(q) for q in combinations(four,k)) for k in range(1,5)]
    Q=Z**3-ee[1]*Z**2+(ee[0]*ee[2]-4*ee[3])*Z-(ee[0]**2*ee[3]+ee[2]**2-4*ee[1]*ee[3])
    assert sp.expand(Q-(Z-r0*r1-r2*r3)*(Z-r0*r2-r1*r3)*(Z-r0*r3-r1*r2))==0
    checks['quartic_completion_identity']=True
    # 4. Root-level comparisons, including repeated and zero roots.
    tuples=[(1,4,10,23,51,109),(-3,0,1,2,3,4),(-3,-2,-1,1,2,3),
            (0,0,1,1,2,2),(0,0,0,0,0,0),(-2,-2,1,1,3,3),
            (sp.Rational(1,2),sp.Rational(2,3),1,2,3,5)]
    root_cases=[]
    for r in tuples:
        f=sp.Poly(sp.prod(X-v for v in r),X)
        ma,ta,ca=direct_resolvents(r)
        assert matching_resolvent(f)==ma.set_domain(sp.QQ)
        assert triple_resolvent(f)==ta.set_domain(sp.QQ)
        assert triple_resolvent(f,method='pfaffian')==ta.set_domain(sp.QQ)
        if all(v!=0 for v in r):
            assert zero_matching_resolvent(f)==ca.set_domain(sp.QQ)
        if len(set(r))==6:
            for p in PENTADS:
                mat=sp.Matrix([[abc(r,M[i])[j]-abc(r,M[p[0]])[j] for j in range(3)] for i in p[1:]])
                assert mat.rank()>=2
        root_cases.append([str(v) for v in r])
    checks['split_root_cases']=root_cases
    # 5. All 16 transitive group types, with translated/scaled coordinates.
    records=[]
    for expected,expr in SEEDS:
        for scale,shift in [(1,0),(1,1),(2,-1)]:
            f=sp.Poly(sp.expand(scale**6*expr.subs(X,(X-shift)/scale)),X,domain=sp.QQ)
            assert f.is_irreducible
            group,_=galois_group(f)
            name,_=galois_group(f,by_name=True)
            assert name.name==expected, (expected,name)
            m=matching_resolvent(f); tr=triple_resolvent(f); zero=zero_matching_resolvent(f)
            mr,br,cr = rational_roots(m),rational_roots(tr),rational_roots(zero)
            sol=bool(group.is_solvable)
            assert bool(mr or br)==sol
            assert bool(cr or br)==sol
            if not sol:
                assert not mr and not br and not cr
            if scale==1 and shift==0:
                assert tr==triple_resolvent(f,method='pfaffian')
            records.append(dict(group=expected,order=int(group.order()),solvable=sol,
                                scale=scale,shift=shift,coefficients=[str(q) for q in f.all_coeffs()],
                                matching_roots=roots_json(m),triple_roots=roots_json(tr),
                                zero_matching_roots=roots_json(zero)))
    # 6. Pfaffian sign, congruence and square checks at arbitrary matrices.
    rng=random.Random(20260930)
    for n in [0,2,4,6,8]:
        for _ in range(4):
            B=sp.Matrix(n,n,[rng.randrange(-3,4) for _ in range(n*n)])
            A=B-B.T
            assert pfaffian(A)**2==A.det()
    for _ in range(3):
        C=sp.Matrix(6,6,[rng.randrange(-2,3) for _ in range(36)])
        J=middle_pairing();D=wedge_matrix(C,3);H=D-J*D.T*J
        assert D.T*J*D==C.det()*J
        assert (J*H).T==-J*H
        for z in [0,1,-2]:
            assert pfaffian(J*(z*sp.eye(20)-H))**2==(z*sp.eye(20)-H).det()
    checks['pfaffian_random_checks']=29
    # 7. Failure of branch labels despite correct solvability decision.
    example=sp.Poly(X**6+X**3+2,X)
    gm,_=galois_group(example)
    mm=matching_resolvent(example);tt=triple_resolvent(example)
    assert gm.order()==36 and rational_roots(mm).get(0)==3
    examples=dict(polynomial=str(example.as_expr()),galois_order=36,
                  matching_factorization=str(sp.factor(mm.as_expr())),
                  triple_factorization=str(sp.factor(tt.as_expr())))
    # API validation.
    for bad in [X**5+1,X**6-1]:
        try:
            decide_irreducible_sextic(bad)
            raise AssertionError('Invalid input accepted.')
        except ValueError:
            pass
    summary=Counter(('solvable' if r['solvable'] else 'nonsolvable') for r in records)
    return dict(all_checks_passed=True,python=platform.python_version(),sympy=sp.__version__,
                elapsed_seconds=round(time.monotonic()-start,3),checks=checks,
                group_case_count=len(records),summary=dict(summary),group_cases=records,
                example=examples)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'rerun'/'verification.json')
    args=parser.parse_args()
    result=run()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in {'group_cases','checks'}},indent=2))
    print('Written:',args.output)
