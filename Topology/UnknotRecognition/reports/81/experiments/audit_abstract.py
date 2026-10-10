"""Independent exact randomized audit; no production files are modified."""
from fractions import Fraction as F
from itertools import combinations
from types import SimpleNamespace
from pathlib import Path
from math import gcd, lcm
from collections import Counter
import argparse
import hashlib
import json
import random
import sys
import time

PACKAGE = Path(__file__).resolve().parents[1]


def arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast', type=Path, default=PACKAGE / 'code',
                        help='Directory containing the fastunknot package (default: bundled code)')
    parser.add_argument('--output', type=Path,
                        default=PACKAGE / 'results' / 'abstract_geometry_audit.json',
                        help='Destination for the complete JSON audit record')
    return parser.parse_args()


def elimination(rows, width):
    a = [[F(x) for x in row] for row in rows]
    pivots = []
    for c in range(width):
        r = len(pivots)
        hit = next((i for i in range(r, len(a)) if a[i][c]), None)
        if hit is None:
            continue
        a[r], a[hit] = a[hit], a[r]
        z = a[r][c]
        a[r] = [x/z for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c]:
                z = a[i][c]
                a[i] = [x-z*y for x, y in zip(a[i], a[r])]
        pivots.append(c)
    return a, pivots


def rank(rows, width):
    return len(elimination(rows, width)[1])


def null_one(rows, width):
    reduced, pivots = elimination(rows, width)
    free = [i for i in range(width) if i not in pivots]
    if len(free) != 1:
        return None
    vector = [F(0)]*width
    vector[free[0]] = F(1)
    for row, p in zip(reduced, pivots):
        vector[p] = -row[free[0]]
    return vector


def primitive(values, orient=True):
    values = [F(x) for x in values]
    den = lcm(*(v.denominator for v in values))
    integers = [int(v*den) for v in values]
    div = 0
    for x in integers:
        div = gcd(div, abs(x))
    if not div:
        return tuple(integers)
    if orient and next(x for x in integers if x) < 0:
        div = -div
    return tuple(x//div for x in integers)


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), F(0))


def independent_rank_oracle(basis, groups, potentials):
    """All equality-arrangement candidates, filtered by lifted cone rank.

    The lifted cone has variables (basis coordinates, one height per group),
    inequalities q_i >= 0 and P_c q + h_group >= 0.  A canonical lift is
    extreme exactly when active inequalities have corank one.
    """
    d = len(basis)
    if not d:
        return set(), 0
    k = len(basis[0])
    coordinate_forms = [tuple(b[i] for b in basis) for i in range(k)]
    projected = {c: tuple(dot(potentials[c], b) for b in basis)
                 for group in groups for c in group}
    normals = set()
    for form in coordinate_forms:
        if any(form):
            normals.add(primitive(form))
    for group in groups:
        for a, b in combinations(group, 2):
            form = tuple(x-y for x, y in zip(projected[a], projected[b]))
            if any(form):
                normals.add(primitive(form))
    rays = set()
    checked = 0
    for chosen in combinations(sorted(normals), d-1):
        u = null_one(chosen, d)
        if u is None:
            continue
        q = tuple(dot(form, u) for form in coordinate_forms)
        if all(x <= 0 for x in q):
            u = [-x for x in u]
            q = tuple(-x for x in q)
        if not any(q) or any(x < 0 for x in q):
            continue
        q = primitive(q)
        checked += 1
        active = [tuple(form)+(0,)*len(groups)
                  for form, x in zip(coordinate_forms,
                                     [dot(form, u) for form in coordinate_forms])
                  if not x]
        for j, group in enumerate(groups):
            minimum = min(dot(projected[c], u) for c in group)
            for c in group:
                if dot(projected[c], u) == minimum:
                    heights = tuple(int(i == j) for i in range(len(groups)))
                    active.append(projected[c]+heights)
        if rank(active, d+len(groups)) == d+len(groups)-1:
            rays.add(q)
    return rays, checked


def producer_directions(kernel):
    stats = {}
    plan = sector_planar_plan(kernel, stats=stats)
    rays = set()
    for point in plan['points']:
        values = list(plan['q_origin'])
        for z, direction in zip(point, plan['q_directions']):
            values = [a+z*b for a, b in zip(values, direction)]
        rays.add(primitive(values))
    return rays, plan, stats


def trial(basis, group_sizes, coefficients, label):
    basis = tuple(tuple(F(x) for x in row) for row in basis)
    groups = []
    index = 0
    for size in group_sizes:
        groups.append(tuple(range(index, index+size)))
        index += size
    potentials = {c: tuple(F(x) for x in row)
                  for c, row in enumerate(coefficients)}
    groups = tuple(groups)
    kernel = SimpleNamespace(basis=basis, groups=groups,
                             classes=tuple(range(index)), potentials=potentials)
    produced, plan, stats = producer_directions(kernel)
    expected, candidate_count = independent_rank_oracle(basis, groups, potentials)
    model = dict(basis=basis, groups={i: list(g) for i, g in enumerate(groups)},
                 potentials=potentials)
    verifier_stats = {}
    verified = set(independent_planar_directions(model, stats=verifier_stats))
    if produced != expected or verified != expected:
        raise AssertionError(dict(label=label, basis=basis, groups=groups,
                                  potentials=potentials, produced=produced,
                                  expected=expected, verified=verified))
    if len(plan['points']) != len(produced):
        raise AssertionError(('duplicate projective points', label))
    if len(produced) > stats['output_bound']:
        raise AssertionError(('output_bound violation', label, stats))
    return dict(label=label, section_dimension=stats['section_dimension'],
                rays=len(expected), arrangement_candidates=candidate_count,
                producer_work=stats['work_units'],
                checker_work=verifier_stats['verification_work'])


def main(args):
    global sector_planar_plan, independent_planar_directions
    fast = args.fast.resolve()
    sys.path.insert(0, str(fast))
    from fastunknot.sector_planar import sector_planar_plan
    from fastunknot.sector_planar_verify import independent_planar_directions
    started = time.time()
    rng = random.Random(202610095071)
    hashes = {name: hashlib.sha256((fast/'fastunknot'/name).read_bytes()).hexdigest()
              for name in ['sector_planar.py', 'sector_planar_verify.py',
                           'sector_planar_certificate.py']}
    templates = [
        ('simplex', ((1,0,0),(0,1,0),(0,0,1))),
        ('square', ((1,-1,0,0),(0,0,1,-1),(0,1,0,1))),
        ('raw3_segment', ((1,-1,0,0),(0,0,1,0),(0,0,0,1))),
        ('raw3_point', ((1,-1,0,0,0),(0,0,1,-1,0),(0,0,0,0,1))),
        ('raw3_empty', ((1,-1,0,0,0,0),(0,0,1,-1,0,0),(0,0,0,0,1,-2))),
        ('raw2_segment', ((1,0),(0,1))),
        ('raw2_point', ((1,-1,0),(0,0,1))),
        ('raw2_empty', ((1,-1,0,0),(0,0,1,-2))),
        ('raw1_point', ((1,2,3),)),
        ('raw1_empty', ((1,-1,1),)),
    ]
    results = []
    # Deterministic coincident, inactive, lower-dimensional and rational ties.
    adversarial = [
        (((1,0,0),(0,1,0),(0,0,1)), [5],
         [(1,0,0),(-1,0,0),(0,0,0),(0,1,0),(0,0,1)], 'boundary_zero_area'),
        (((1,-1,0,0),(0,0,1,-1),(0,1,0,1)), [5,5],
         [(0,0,0,0),(1,0,0,0),(2,0,0,0),(-1,1,0,0),(-2,2,0,0)]*2,
         'coincident_overlays'),
        (((1,-1,0,0),(0,0,1,-1),(0,1,0,1)), [5,5],
         [(0,0,0,0),(1,0,0,0),(2,0,0,0),(-1,1,0,0),(-2,2,0,0)] +
         [(0,0,0,0),(0,0,1,0),(0,0,2,0),(0,0,-1,1),(0,0,-2,2)],
         'transverse_slabs'),
        (((1,0,0),(0,1,0),(0,0,1)), [4,3],
         [(1,0,0),(0,1,0),(0,0,1),(1,1,1),
          (1,0,0),(0,1,0),(0,0,1)], 'triple_tie'),
    ]
    for basis, sizes, coefficients, label in adversarial:
        results.append(trial(basis, sizes, coefficients, label))
    for i in range(200):
        label, basis = templates[i % len(templates)]
        k = len(basis[0])
        sizes = [rng.randint(1,5) for _ in range(rng.randint(0,3))]
        coefficients = [tuple(rng.randint(-3,3) for _ in range(k))
                        for _ in range(sum(sizes))]
        # Duplicate affine functions and dependent ties occur deliberately.
        if len(coefficients) > 2 and i % 3 == 0:
            coefficients[1] = coefficients[0]
        results.append(trial(basis, sizes, coefficients, f'{label}_{i}'))
    for i in range(100):
        d = rng.randint(1,3)
        k = rng.randint(d, d+3)
        while True:
            basis = tuple(tuple(rng.randint(-2,3) for _ in range(k)) for _ in range(d))
            if rank(basis,k) == d:
                break
        sizes = [rng.randint(1,4) for _ in range(rng.randint(0,3))]
        coefficients = [tuple(rng.randint(-3,3) for _ in range(k))
                        for _ in range(sum(sizes))]
        results.append(trial(basis, sizes, coefficients, f'random_basis_{i}'))
    summary = dict(status='PASS', trials=len(results), seed=202610095071,
                   section_dimensions=dict(Counter(r['section_dimension'] for r in results)),
                   rays_compared=sum(r['rays'] for r in results),
                   arrangement_candidates=sum(r['arrangement_candidates'] for r in results),
                   max_rays=max(r['rays'] for r in results),
                   source_sha256=hashes, seconds=time.time()-started, results=results)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k!='results'}, indent=2))


if __name__ == '__main__':
    main(arguments())
