"""Exact checks of sharp quarter-defect affine recovery and its boundary.
All maps tested here are normalized by f(0)=0; this quotient by constant
target translations leaves graph energy, affine distance, and decoder unchanged.
No finite computation substitutes for the accompanying proofs.
"""
from collections import Counter
from fractions import Fraction
from itertools import product, combinations
import json
from pathlib import Path


def group_table(mods):
    elts = list(product(*(range(m) for m in mods)))
    index = {x: i for i, x in enumerate(elts)}
    add = [[index[tuple((a + b) % m for a, b, m in zip(x, y, mods))]
            for y in elts] for x in elts]
    return elts, add


def suite(mods, q):
    points, add = group_table(mods)
    n = len(points)
    homs = []
    for slopes in product(range(q), repeat=len(mods)):
        if all((a * m) % q == 0 for a, m in zip(slopes, mods)):
            homs.append(tuple(sum(a*x for a, x in zip(slopes, p)) % q
                              for p in points))
    affine = [tuple((x+b) % q for x in h) for h in homs for b in range(q)]
    tally = Counter()
    for tail in product(range(q), repeat=n-1):
        f = (0,) + tail
        rows = [Counter((f[add[h][x]] - f[x]) % q for x in range(n))
                for h in range(n)]
        energy = sum(sum(c*c for c in r.values()) for r in rows)
        defect = n**3-energy
        tally['normalized_maps'] += 1
        if 4*defect > n**3:
            continue
        tally['quarter_eligible'] += 1
        major = {h: w for h in range(n) for w, c in rows[h].items()
                 if 2*c > n}
        assert major[0] == 0
        for h, w in major.items():
            for k, v in major.items():
                assert add[h][k] in major
                assert major[add[h][k]] == (w+v) % q
        distances = [sum(a != b for a,b in zip(f,g)) for g in affine]
        dist = min(distances)
        nearest = distances.count(dist)
        if len(major) == n:
            tally['global_majority'] += 1
            constants = Counter((f[x]-major[x]) % q for x in range(n))
            c, count = constants.most_common(1)[0]
            errors = n-count
            assert errors == dist and nearest == 1
            assert 7*errors < n
            kappa = int(q % 2 == 0)
            assert defect >= (4*errors*n*n-(10+2*kappa)*errors**2*n
                              +(6+2*kappa)*errors**3)
        else:
            tally['boundary_obstruction'] += 1
            assert 4*defect == n**3
            assert len(major)*2 == n
            assert 2*dist >= n
            # Each graph is the union of two cosets of the majority subgroup.
            equivalence = Counter()
            unseen = set(range(n))
            sizes = []
            while unseen:
                x = min(unseen)
                cell = {add[x][h] for h in major
                        if f[add[x][h]] == (f[x]+major[h]) % q}
                assert len(cell) == n//2
                sizes.append(len(cell))
                unseen.difference_update(cell)
            assert sizes == [n//2,n//2]
            if q % 2:
                assert 2*dist == n and nearest == 2
        if 4*defect < n**3:
            tally['strict_eligible'] += 1
            assert len(major) == n and nearest == 1
    return dict(tally)


def cutoff_certificates():
    n = 13
    # All two-node multiplicity obstructions to majority-subgroup closure.
    found = []
    for c in range(1,7):
        for b in range(7,14):
            if 2*b <= n+c:
                bound = Fraction(n**3-c**3-(b-c)**3-(n-b)**3,3)
                found.append((c,b,bound))
    assert min(v for _,_,v in found) == 588
    assert 13**3-(13**3-4*13**2+10*13-6) == 552
    # Stronger fiber constraint: largest color at most eight is impossible.
    assert 7*(8**2+5**2) + 6*169 == 1637 < 1645
    # Cubic gap eliminates support cardinalities 2,3,4 (and also 5).
    values = {s: 4*s*13**2-10*s*s*13+6*s**3 for s in range(1,6)}
    assert values[1] == 552 and all(values[s] > 552 for s in range(2,6))
    # The two order-twelve endpoint obstructions.
    examples=[]
    for q,f in [(3,tuple(x%2 for x in range(12))),
                (2,tuple((x%4)//2 for x in range(12)))]:
        e=sum(sum(c*c for c in Counter((f[(x+h)%12]-f[x])%q
                                      for x in range(12)).values())
              for h in range(12))
        k=int(q%2==0)
        proposed=12**3-4*12**2+(10+2*k)*12-(6+2*k)
        assert e==1296 and e>proposed
        examples.append({'target_order':q,'energy':e,'one_point_energy':proposed})
    return {'majority_two_node_cases':len(found),
            'smallest_forced_defect':588,
            'one_point_defect':552,
            'cubic_values_at_error_cardinalities':values,
            'order_twelve_counterexamples':examples}


def sparse_examples():
    tally=Counter()
    for n in (13,14,16,23,31,53):
        for q in (2,3,4,5,7,9):
            kappa=int(q%2==0)
            maximum=n**3-4*n*n+(10+2*kappa)*n-(6+2*kappa)
            maps=[]
            for b in range(1,q):
                maps.append((b,)+(0,)*(n-1))
            for j in sorted({1,n//2,n-1}):
                for b,c in product(range(1,q),repeat=2):
                    f=[0]*n
                    f[0],f[j]=b,c
                    maps.append(tuple(f))
            for f in maps:
                tally['specified_maps']+=1
                rows=[Counter((f[(x+h)%n]-f[x])%q for x in range(n))
                      for h in range(n)]
                energy=sum(sum(c*c for c in row.values()) for row in rows)
                defect=n**3-energy
                error=sum(x!=0 for x in f)
                assert energy<=maximum
                equal=(error==1 and (not kappa or (2*f[0])%q==0))
                assert (energy==maximum)==equal
                if equal: tally['sharp_maximum_examples']+=1
                if 4*defect<n**3:
                    tally['strict_nonaffine_examples']+=1
                    assert all(row.get(0,0)*2>n for row in rows)
                    assert 7*error<n
                    assert defect>=4*error*n*n-(10+2*kappa)*error**2*n+(6+2*kappa)*error**3
    return dict(tally)


if __name__ == '__main__':
    params = [((n,),q) for n in range(2,9) for q in (2,3)
              if q**(n-1)<=10000]
    params += [((n,),q) for n in range(2,7) for q in (4,5)
               if q**(n-1)<=4000]
    params += [((2,2),q) for q in (2,3,4,5)]
    params += [((2,2,2),q) for q in (2,3)]
    params += [((2,4),q) for q in (2,3)]
    results = {str(mods)+' -> C'+str(q):suite(mods,q) for mods,q in params}
    output={'status':'PASS','suites':results,'cutoff':cutoff_certificates(),
            'sparse_examples':sparse_examples()}
    path=Path(__file__).with_name('rigidity_checks.json')
    path.write_text(json.dumps(output,indent=2)+'\n')
    totals=Counter()
    for counts in results.values(): totals.update(counts)
    print(json.dumps({'status':'PASS','totals':dict(totals),
                      'suites':len(results),'output':str(path)},indent=2))
