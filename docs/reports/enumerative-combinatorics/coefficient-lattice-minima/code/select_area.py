#!/usr/bin/env python3
"""Draw once from a fixed ordered catalogue using operating-system randomness."""
import secrets, json
from pathlib import Path
AREAS = [
 'Additive combinatorics', 'Algebraic combinatorics', 'Analytic combinatorics',
 'Extremal graph theory', 'Structural graph theory', 'Graph coloring',
 'Spectral graph theory', 'Hypergraph theory', 'Ramsey theory',
 'Design theory', 'Finite geometry', 'Matroid theory',
 'Discrete geometry', 'Convex geometry', 'Geometry of numbers',
 'Lattice polytopes and Ehrhart theory', 'Tiling theory', 'Combinatorial game theory',
 'Permutation patterns', 'Combinatorics on words', 'Automata and formal languages',
 'Symbolic dynamics', 'Substitution dynamical systems', 'Ergodic theory',
 'Topological dynamics', 'Arithmetic dynamics', 'Complex dynamics',
 'Real dynamical systems', 'Numerical semigroups', 'Commutative algebra',
 'Monomial ideals', 'Combinatorial commutative algebra', 'Invariant theory',
 'Finite group theory', 'Combinatorial group theory', 'Semigroup theory',
 'Nonassociative algebra', 'Lie algebras', 'Representation theory',
 'Category theory', 'Type theory', 'Universal algebra',
 'Order theory', 'Lattice theory', 'Computability theory',
 'Proof theory', 'Model theory', 'Set-theoretic topology',
 'General topology', 'Knot theory', 'Low-dimensional topology',
 'Algebraic topology', 'Persistent homology', 'Metric geometry',
 'Graph limits', 'Probabilistic combinatorics', 'Discrete probability',
 'Markov chains', 'Random walks', 'Information theory',
 'Coding theory', 'Finite fields', 'Elementary number theory',
 'Diophantine approximation', 'Diophantine equations', 'Multiplicative number theory',
 'Partition theory', 'q-series', 'Special functions',
 'Orthogonal polynomials', 'Approximation theory', 'Potential theory',
 'Harmonic analysis', 'Fourier analysis on finite groups', 'Functional equations',
 'Matrix theory', 'Nonnegative matrices', 'Tensor algebra',
 'Polynomial inequalities', 'Moment problems', 'Optimization',
 'Discrete optimization', 'Numerical analysis', 'Difference equations',
 'Differential algebra', 'Differential equations', 'D-finite functions',
 'Integer sequences', 'Enumerative topology', 'Geometric group theory',
 'Computational geometry', 'Boolean functions', 'Algebraic statistics',
 'Tropical geometry', 'Real algebraic geometry', 'Incidence geometry'
]
if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--draw', type=Path, metavar='NEW_PATH',
                        help='Make a new independent draw into a new file; never overwrite.')
    args = parser.parse_args()
    path = Path(__file__).resolve().parents[1] / 'data' / 'area_selection.json'
    if args.draw is None:
        result = json.loads(path.read_text())
        assert result['areas'] == AREAS
        assert result['selected_area'] == AREAS[result['index_zero_based']]
        print('Recorded original draw (no new random number generated):')
    else:
        # The original research used one secrets.randbelow(len(AREAS)) call.
        # This explicit option is for a different future draw, never replay.
        if args.draw.exists():
            parser.error('Refusing to overwrite an existing selection record.')
        index = secrets.randbelow(len(AREAS))
        result = {'method': 'secrets.randbelow (OS random source)',
                  'number_of_areas': len(AREAS), 'index_zero_based': index,
                  'index_one_based': index+1, 'selected_area': AREAS[index],
                  'draw_count': 1, 'areas': AREAS}
        with args.draw.open('x') as stream:
            stream.write(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='areas'}, indent=2))
