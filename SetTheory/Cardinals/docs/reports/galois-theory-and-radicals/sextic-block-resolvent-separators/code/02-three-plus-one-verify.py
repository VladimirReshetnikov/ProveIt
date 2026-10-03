"""Reproducible exact checks for Three Plus One sextic resolvents.

The proof is in article.tex. These tests are finite implementation checks, not
formal proofs. The independent Galois classifier is used ONLY by this test file.
The 16 seed sextics are the examples in SymPy 1.14.0's test_galoisgroups.py,
which attributes them to Henri Cohen's computational number theory text.
"""
from __future__ import annotations
from itertools import combinations
from pathlib import Path
import json, platform, random, time
import sympy as s
from sextic_resolvents import SexticResolvents, decide_irreducible_sextic

X, Z, T, U, V = s.symbols('x z t u v')


def matchings(items):
    if not items:
        yield ()
        return
    first, rest = items[0], items[1:]
    for j, other in enumerate(rest):
        for tail in matchings(rest[:j] + rest[j+1:]):
            yield ((first, other),) + tail


MATCHINGS = tuple(matchings(tuple(range(6))))
TRIPLES = tuple((B, tuple(i for i in range(6) if i not in B))
                for B in combinations(range(6), 3) if 0 in B)
PENTADS = tuple(C for C in combinations(range(15), 5)
                if len({e for i in C for e in MATCHINGS[i]}) == 15)


def esym(values, k):
    return sum(s.prod(c) for c in combinations(values, k))


def matching_coeffs(roots, matching):
    ps = [roots[i]*roots[j] for i, j in matching]
    ss = [roots[i]+roots[j] for i, j in matching]
    A = sum(ps)
    B = sum(ss[i]*ps[j] for i in range(3) for j in range(3) if i != j)
    C = sum(ps[i]*ps[j] for i in range(3) for j in range(i+1, 3))
    return A, B, C


def h_value(roots, matching, t):
    A, B, C = matching_coeffs(roots, matching)
    return A*t*t+B*t-C


def k_value(roots, partition, t):
    a = sum(esym([roots[i] for i in B], 2) for B in partition)
    b = sum(s.prod(roots[i] for i in B) for B in partition)
    return a*t-b


def symbolic_checks():
    assert len(MATCHINGS) == 15 and len(TRIPLES) == 10 and len(PENTADS) == 6
    assert all(len(set(A)&set(B)) == 1 for A, B in combinations(PENTADS, 2))
    assert all(sum(i in A for A in PENTADS) == 2 for i in range(15))
    roots = s.symbols('a:6')
    e = [s.Integer(1)] + [esym(roots, k) for k in range(1, 7)]
    coeff = [matching_coeffs(roots, P) for P in MATCHINGS]
    count = 0
    for i, j in combinations(range(15), 2):
        common = set(MATCHINGS[i]) & set(MATCHINGS[j])
        if not common:
            continue
        (a, b), = common
        q = T*T+(roots[a]+roots[b])*T-roots[a]*roots[b]
        assert s.expand(h_value(roots, MATCHINGS[i], T)-h_value(roots, MATCHINGS[j], T)
                        -(coeff[i][0]-coeff[j][0])*q) == 0
        count += 1
    assert count == 45
    for P in PENTADS:
        for j, target in enumerate((e[2], 3*e[3], e[4])):
            assert s.expand(sum(coeff[i][j] for i in P)-target) == 0
    # Verify all 25 descriptor compression identities without specializing roots.
    f = s.prod(U-a for a in roots)
    for i, P in enumerate(MATCHINGS):
        A, B, C = coeff[i]
        direct = s.prod(V-s.prod(U-roots[j] for j in block) for block in P)
        formula = (V**3-(3*U**2-e[1]*U+A)*V**2
                   +(3*U**4-2*e[1]*U**3+(e[2]+A)*U**2-B*U+C)*V-f)
        assert s.expand(direct-formula) == 0
    for P in TRIPLES:
        direct = s.prod(V-s.prod(U-roots[j] for j in block) for block in P)
        formula = V**2-(2*U**3-e[1]*U**2+k_value(roots,P,U))*V+f
        assert s.expand(direct-formula) == 0
    # Quartic pairing cubic, used in the coefficient-only construction.
    a,b,c,d = roots[:4]
    r = [s.Integer(1)] + [esym((a,b,c,d), k) for k in range(1,5)]
    cubic = (Z-(a*b+c*d))*(Z-(a*c+b*d))*(Z-(a*d+b*c))
    formula = Z**3-r[2]*Z**2+(r[1]*r[3]-4*r[4])*Z-(r[3]**2+r[1]**2*r[4]-4*r[2]*r[4])
    assert s.expand(cubic-formula) == 0
    return {'matching_count':15, 'triple_partition_count':10, 'pentad_count':6,
            'pentad_intersections_checked':15, 'matching_memberships_checked':15,
            'shared_edge_identities':count, 'pentad_sum_identities':18,
            'descriptor_identities':25, 'quartic_identity':1,
            'pentads_matching_indices_zero_based':PENTADS}


def split_checks():
    rng = random.Random(20260929)
    tuples = [(-3,0,1,2,3,4), (1,4,10,23,51,109), (-5,-3,-1,2,4,8)]
    tuples += [tuple(rng.sample(range(-11, 12), 6)) for _ in range(5)]
    tuples += [tuple(s.Rational(a, 2) for a in (-7,-3,1,4,8,13)),
               tuple(s.Rational(a, 3) for a in (-8,-4,-1,2,7,11))]
    result = []
    repeated = 0
    for roots in tuples:
        f = s.Poly(s.prod(X-a for a in roots), X)
        builder = SexticResolvents(f, X)
        row = {'roots':list(map(str,roots)), 'parameters':[]}
        for t in (1,2,3):
            p = builder.pair(t, Z)
            direct = s.Poly(s.prod(Z-h_value(roots,P,t) for P in MATCHINGS), Z, domain=s.QQ)
            assert p == direct
            mult = max(p.ground_roots().values())
            repeated += (mult > 1)
            entry = {'t':t, 'pair_identity':True, 'pair_max_multiplicity':int(mult)}
            # Use a nearby rational test when f(t)=0; this only affects this
            # general separable/split identity test, not the irreducible rule.
            u = s.Rational(t) if f.eval(t) != 0 else s.Rational(2*t+1, 2)
            while f.eval(u) == 0:
                u += s.Rational(1,7)
            p3 = builder.triple(u,Z)
            direct3 = s.Poly(s.prod(Z-k_value(roots,P,u) for P in TRIPLES),Z,domain=s.QQ)
            assert p3 == direct3
            entry.update({'triple_parameter':str(u), 'triple_identity':True,
                          'triple_max_multiplicity':int(max(p3.ground_roots().values()))})
            row['parameters'].append(entry)
        result.append(row)
    return {'tuples':result, 'pair_identities':30, 'triple_identities':30,
            'pair_tests_with_repeated_roots':int(repeated)}


SEEDS = [
 ('C6', X**6+X**5+X**4+X**3+X**2+X+1),
 ('S3', X**6+108), ('D6', X**6+2), ('A4', X**6-3*X**2-1),
 ('G18', X**6+3*X**3+3), ('A4xC2',X**6-3*X**2+1),
 ('S4p',X**6-4*X**2-1),
 ('S4m',X**6-3*X**5+6*X**4-7*X**3+2*X**2+X-4),
 ('G36m',X**6+2*X**3-2), ('S4xC2',X**6+2*X**2+2),
 ('PSL2F5',X**6+10*X**5+55*X**4+140*X**3+175*X**2+170*X+25),
 ('PGL2F5',X**6+10*X**5+55*X**4+140*X**3+175*X**2-3019*X+25),
 ('G36p',X**6+6*X**4+2*X**3+9*X**2+6*X-4),
 ('G72',X**6+2*X**4+2*X**3+X**2+2*X+2),
 ('A6',X**6+24*X-20), ('S6',X**6+X+1)
]


def irreducible_checks():
    rows = []
    branches = {}
    for name, expr in SEEDS:
        # Affine transformations preserve the splitting field and the group.
        # Tests are still at the fixed points 1,2,3, so these are not repetitions
        # of the same specialized numerical resolvent values.
        for tag, transformed in [('seed',expr), ('translate',s.expand(expr.subs(X,X+2))),
                                 ('rescale',s.expand(64*expr.subs(X,X/2)))]:
            f = s.Poly(transformed,X,domain=s.QQ)
            assert f.is_irreducible
            group, _ = s.polys.numberfields.galois_group(f, by_name=True)
            assert group.name == name
            truth = bool(group.get_perm_group().is_solvable)
            builder = SexticResolvents(f,X)
            p3 = builder.triple(1,Z)
            triple_roots = p3.ground_roots()
            pair_roots = [builder.pair(t,Z).ground_roots() for t in (1,2,3)]
            decision = bool(triple_roots) or all(bool(r) for r in pair_roots)
            assert decision == truth
            if not truth:
                assert p3.is_sqf and not triple_roots
                for t,r in zip((1,2,3),pair_roots):
                    mu = (builder.e[2]*t*t+3*builder.e[3]*t-builder.e[4])/5
                    assert len(r) <= 1 and all(c == mu and m == 5 for c,m in r.items())
                assert sum(bool(r) for r in pair_roots) <= 2
            api = decide_irreducible_sextic(f,X)
            assert api['solvable'] == truth
            branches[api['reason']] = branches.get(api['reason'],0)+1
            row = {'group':name,'variant':tag,'polynomial':str(f.as_expr()),
                   'group_order':int(group.get_perm_group().order()), 'solvable':truth,
                   'triple_roots':{str(k):int(v) for k,v in triple_roots.items()},
                   'pair_roots':[{str(k):int(v) for k,v in r.items()} for r in pair_roots],
                   'api_reason':api['reason']}
            rows.append(row)
            print(name,tag,'solvable='+str(truth),'roots=',[len(triple_roots)]+[len(r) for r in pair_roots],flush=True)
    return {'cases':rows, 'count':len(rows), 'group_types':len(SEEDS), 'api_branches':branches}


def validation_checks():
    bad = [X**5+X+1, (X-1)*(X**5+X+1), 0]
    for f in bad:
        try:
            decide_irreducible_sextic(f,X)
        except ValueError:
            pass
        else:
            raise AssertionError('Malformed/reducible input was not rejected.')
    for points in ((1,1,2),(1,2),(0,1,2)):
        try:
            decide_irreducible_sextic(X**6+X+1,X,points)
        except ValueError:
            pass
        else:
            raise AssertionError('Invalid test parameters were not rejected.')
    return {'invalid_inputs_rejected':6}


def main():
    started=time.time()
    out={'environment':{'python':platform.python_version(),'sympy':s.__version__,
                        'repository_pin':'e47ed8547bd021f9bd85bdcf767c94a2fcb41001'},
         'status':'finite exact checks; not a formal proof'}
    out['symbolic']=symbolic_checks()
    print('symbolic checks passed',flush=True)
    out['split']=split_checks()
    print('split-root identity checks passed',flush=True)
    out['irreducible']=irreducible_checks()
    out['validation']=validation_checks()
    out['elapsed_seconds']=round(time.time()-started,3)
    out['all_checks_passed']=True
    path=Path(__file__).resolve().parents[1]/'data'/'verification.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    print('ALL CHECKS PASSED; wrote',path,flush=True)

if __name__=='__main__':
    main()
