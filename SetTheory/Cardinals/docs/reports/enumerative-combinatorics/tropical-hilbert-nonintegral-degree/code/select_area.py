#!/usr/bin/env python3
"""Audit the retained area selection, or explicitly draw a new separate record.

The original single OS-random draw selected entry 50 of 96: Tropical geometry.
The default audit mode was added during packaging; it makes no random call.
"""
import json, secrets, hashlib
from pathlib import Path
AREAS = [
'Additive combinatorics', 'Algebraic combinatorics', 'Analytic number theory',
'Arithmetic geometry', 'Automata and formal languages', 'Banach space geometry',
'Combinatorial commutative algebra', 'Combinatorial design theory',
'Combinatorial game theory', 'Computable analysis', 'Computational geometry',
'Convex geometry', 'Discrete geometry', 'Dynamical systems', 'Enumerative geometry',
'Ergodic theory', 'Extremal graph theory', 'Finite fields', 'Finite group theory',
'Functional equations', 'General topology', 'Geometric group theory',
'Graph polynomials', 'Hypergraph theory', 'Integer partitions',
'Integral inequalities', 'Knot invariants', 'Lattice theory', 'Linear preserver problems',
'Matroid theory', 'Metric geometry', 'Noncommutative algebra', 'Numerical semigroups',
'Operator inequalities', 'Ordered algebraic structures', 'Permutation patterns',
'Polynomial dynamics', 'Probabilistic combinatorics', 'Quasigroups and loops',
'Ramsey theory', 'Real algebraic geometry', 'Recurrence sequences',
'Riordan arrays', 'Semigroup theory', 'Spectral graph theory',
'Symbolic dynamics', 'Tiling theory', 'Topological graph theory',
'Transcendental number theory', 'Tropical geometry', 'Word combinatorics',
'Zero-sum theory', 'Association schemes', 'Coding theory', 'Discrete optimization',
'Extremal set theory', 'Frame theory', 'Graph colorings', 'Incidence geometry',
'Infinite-dimensional holomorphy', 'Matrix inequalities', 'Moment problems',
'Orthogonal polynomials', 'Positive definite functions', 'Rational approximation',
'Riemannian geometry', 'Simplicial complexes', 'Tensor rank', 'Topological dynamics',
'Universal algebra', 'Ultrametric analysis', 'Valuation theory',
'Boolean function theory', 'Chip-firing and sandpiles', 'Discrete probability',
'Fractional calculus', 'Group actions on trees', 'Hyperplane arrangements',
'Information inequalities', 'Modular forms', 'Monomial ideals', 'Optimal transport',
'Partial orders', 'Real-rooted polynomials', 'Rewriting systems',
'Schubert calculus', 'Set-theoretic topology', 'Special functions',
'String-rewriting and monoids', 'Sum-product phenomena', 'Topological semigroups',
'Visibility in graphs', 'Weighted lattice paths', 'Well-quasi-orders',
'Zeta functions of graphs', 'Numerical linear algebra'
]
def main():
    import argparse
    parser = argparse.ArgumentParser(description=(
        "Audit the saved original draw by default. A new random draw requires "
        "--new-draw and a separate, nonexistent output path."))
    parser.add_argument('--new-draw', action='store_true')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--manifest', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    original = root / 'data' / 'area_selection.json'
    if not args.new_draw:
        if args.output:
            parser.error('--output is only used with --new-draw')
        record = json.loads(original.read_text())
        assert record['area_list'] == AREAS
        assert record['number_of_areas'] == len(AREAS) == 96
        index = record['index_zero_based']
        assert 0 <= index < len(AREAS)
        assert record['index_one_based'] == index + 1
        assert record['selected_area'] == AREAS[index]
        assert record['redraws'] == 0
        if args.manifest:
            digest = hashlib.sha256(args.manifest.read_bytes()).hexdigest()
            assert digest == record['manifest_sha256'], 'Manifest digest mismatch'
        print(json.dumps({'status': 'PASS', 'mode': 'audit; no new randomness',
                          'selected_area': record['selected_area'],
                          'index_one_based': index + 1, 'number_of_areas': len(AREAS)},
                         indent=2))
        return
    if args.output is None:
        parser.error('--new-draw requires --output for a separate record')
    if args.output.resolve() == original.resolve() or args.output.exists():
        parser.error('Refusing to overwrite an existing record')
    index = secrets.randbelow(len(AREAS))
    record = {'method': 'secrets.randbelow (operating-system random source)',
              'number_of_areas': len(AREAS), 'index_zero_based': index,
              'index_one_based': index + 1, 'selected_area': AREAS[index],
              'area_list': AREAS, 'redraws': 0}
    if args.manifest:
        record['manifest_sha256'] = hashlib.sha256(args.manifest.read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x') as out:
        out.write(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O: this audit uses assertions.')
    main()
