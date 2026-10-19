#!/usr/bin/env python3
"""Independently check rational affine invariants by dual linear equations.

The discovery program propagates spans of homogenized points. This checker
instead computes annihilating equations and pulls every target equation back
through each CFG edge. It imports neither discovery's CFG builder nor its
transfer/intersection routines. Coordinates are (1,R0,...,R8).

With --product, the supplied threshold/parity invariant is checked first.
Its singleton equations at the successor can then be used in the pullback.
This is a conjunction of two already inductive overapproximations, not an
assumption that the source execution is bounded.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import hashlib
import json

from check_source_product_invariant import build_cfg, verify as verify_product

N = 10
SEED = tuple(map(F, (1, 3, 0, 0, 0, 3, 0, 0, 0, 0)))


def require(test, why):
    if not test:
        raise ValueError(why)


def rref(matrix):
    """Ordinary column-pivot elimination, separate from primal discovery."""
    a = [list(map(F, row)) for row in matrix]
    row, pivots = 0, []
    for col in range(N):
        pivot = next((i for i in range(row, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        scale = a[row][col]
        a[row] = [x / scale for x in a[row]]
        for i in range(len(a)):
            if i != row and a[i][col]:
                scale = a[i][col]
                a[i] = [x - scale*y for x, y in zip(a[i], a[row])]
        pivots.append(col)
        row += 1
        if row == len(a):
            break
    return tuple(tuple(x) for x in a[:row]), tuple(pivots)


def reduce_vector(vector, echelon, pivots):
    v = list(vector)
    for row, pivot in zip(echelon, pivots):
        scale = v[pivot]
        if scale:
            v = [x-scale*y for x, y in zip(v, row)]
    return tuple(v)


def annihilator(points):
    a, pivots = rref(points)
    result = []
    for col in range(N):
        if col not in pivots:
            v = [F(0)]*N
            v[col] = F(1)
            for row, pivot in zip(a, pivots):
                v[pivot] = -row[col]
            result.append(tuple(v))
    return result


def equation(coordinate, constant=0):
    v = [F(0)]*N
    v[coordinate] = F(1)
    v[0] -= F(constant)
    return tuple(v)


def pullback(normal, register, delta):
    v = list(normal)
    if register is not None:
        v[0] += delta*v[register+1]
    return tuple(v)


def fixed(points, coordinate):
    anchor = next(v for v in points if v[0])
    value = anchor[coordinate]/anchor[0]
    if all(v[coordinate] == value*v[0] for v in points):
        return value
    return None


def check(sites, raw_facts, product=None):
    ordered, cfg, start, depth = build_cfg(sites)
    require(len(raw_facts) == len(cfg), 'Wrong affine fact count')
    if product is not None:
        product_result = verify_product(ordered, cfg, start, product, 16)
    else:
        product_result = None
    points, equations = [], []
    for i, raw in enumerate(raw_facts):
        if raw is None:
            points.append(None)
            equations.append(None)
            continue
        require(isinstance(raw, list) and raw, f'Malformed basis {i}')
        require(all(isinstance(v, list) and len(v) == N for v in raw),
                f'Malformed coordinate row {i}')
        basis = tuple(tuple(map(F, v)) for v in raw)
        require(any(v[0] for v in basis), f'No affine anchor at {i}')
        points.append(basis)
        equations.append(annihilator(basis))
    require(points[start] is not None, 'Seed marked unreachable')
    require(all(sum(x*y for x, y in zip(SEED, a)) == 0
                for a in equations[start]), 'Seed excluded by affine equations')

    counts = Counter()
    equation_count = 0
    for i, descriptor in enumerate(cfg):
        if points[i] is None:
            continue
        op = descriptor[0]
        edges = []
        if op == 'INC':
            edges.append((descriptor[2], descriptor[1], 1, False))
        elif op == 'DEC':
            r = descriptor[1]
            constant = fixed(points[i], r+1)
            if constant is None or constant > 0:
                edges.append((descriptor[2], r, -1, False))
            else:
                # Under natural-register semantics, R_r <= 0 excludes R_r > 0.
                counts['positive_edges_excluded_by_nonpositive_constant'] += 1
            edges.append((descriptor[3], r, 0, True))
        elif op == 'JUMP':
            edges.append((descriptor[1], None, 0, False))
        else:
            require(descriptor == ('HALT',), 'Unknown instruction')
            counts['halt_leaves'] += 1
        for j, r, delta, zero_guard in edges:
            if product is not None and product[j] is None:
                counts['edges_excluded_by_independent_product'] += 1
                continue
            hypotheses = list(equations[i])
            if zero_guard:
                hypotheses.append(equation(r+1))
            if product is not None:
                for reg, mask in enumerate(product[j]):
                    if mask & (mask-1) == 0 and mask.bit_length()-1 < 16:
                        singleton = equation(reg+1, mask.bit_length()-1)
                        hypotheses.append(pullback(singleton, r, delta))
            echelon, pivots = rref(hypotheses)
            # The equation x_0=0 contradicts the homogenization x_0=1.
            impossible = not any(reduce_vector(equation(0), echelon, pivots))
            if impossible:
                counts['edges_excluded_by_inconsistent_equations'] += 1
                continue
            require(equations[j] is not None, f'Enabled edge {i}->{j} enters bottom')
            for normal in equations[j]:
                obligation = pullback(normal, r, delta)
                require(not any(reduce_vector(obligation, echelon, pivots)),
                        f'Affine pullback not implied on edge {i}->{j}')
                equation_count += 1
            counts['checked_edges'] += 1

    pairwise, constants = [], 0
    for i, basis in enumerate(points):
        if basis is None:
            continue
        values = [fixed(basis, r+1) for r in range(9)]
        constants += sum(v is not None for v in values)
        anchor = next(v for v in basis if v[0])
        for r in range(9):
            for s in range(r+1, 9):
                if values[r] is not None or values[s] is not None:
                    continue
                offset = (anchor[r+1]-anchor[s+1])/anchor[0]
                if all(v[r+1]-v[s+1] == offset*v[0] for v in basis):
                    pairwise.append({'index': i, 'path': ordered[i][0],
                                     'left_register': r, 'right_register': s,
                                     'left_minus_right': str(offset)})
    return {
        'status': 'PASS_INDEPENDENT_DUAL_AFFINE_INVARIANT',
        'instructions': len(cfg), 'start': start, 'source_depth': depth,
        'uses_independently_checked_product': product is not None,
        'checked_equation_pullbacks': equation_count, 'edge_counts': dict(counts),
        'unreachable': [i for i, b in enumerate(points) if b is None],
        'constant_register_facts': constants,
        'nonconstant_pairwise_offset_facts': len(pairwise),
        'pairwise_offset_facts': pairwise,
        'product_status': 'PASS' if product_result is not None else 'NOT_USED',
        'scope': 'All finite prefixes of the unbounded natural-register run from the calibrated seed; no binary state saving asserted.'
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source', type=Path, required=True)
    ap.add_argument('--facts', type=Path, required=True)
    ap.add_argument('--product', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    sites = json.loads(args.source.read_text())
    facts = json.loads(args.facts.read_text())
    product = json.loads(args.product.read_text()) if args.product else None
    result = check(sites, facts, product)
    # Targeted negative control: replace the seed subspace by the false equation R0=4.
    _, _, start, _ = build_cfg(sites)
    mutated = list(facts)
    mutated[start] = [['1','4','0','0','0','3','0','0','0','0']]
    rejected, why = False, None
    try:
        check(sites, mutated, product)
    except ValueError as error:
        rejected, why = True, str(error)
    require(rejected, 'The deliberately false seed fact was accepted')
    result['negative_control'] = {'rejected': rejected, 'reason': why}
    for key, path in [('source', args.source), ('facts', args.facts),
                      ('checker', Path(__file__))]:
        result[key+'_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'pairwise_offset_facts'}, indent=2))


if __name__ == '__main__':
    main()
