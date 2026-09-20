#!/usr/bin/env python3
"""One unbiased OS-random draw from a fixed list, made before problem searching."""
import secrets, json
from datetime import datetime, timezone
from pathlib import Path
AREAS = [
'Additive combinatorics', 'Algebraic combinatorics', 'Analytic combinatorics',
'Extremal graph theory', 'Structural graph theory', 'Spectral graph theory',
'Graph colorings', 'Combinatorial design theory', 'Matroid theory',
'Permutation patterns', 'Combinatorics on words', 'Enumerative geometry',
'Discrete geometry', 'Convex geometry', 'Geometry of numbers',
'Polyhedral combinatorics', 'Topological combinatorics', 'Ramsey theory',
'Extremal set theory', 'Finite probability', 'Random graphs',
'Markov chains', 'Ergodic theory', 'Symbolic dynamics',
'Topological dynamics', 'Arithmetic dynamics', 'Complex dynamics',
'Functional equations', 'Inequalities', 'Special functions',
'Orthogonal polynomials', 'Approximation theory', 'Harmonic analysis',
'Fourier analysis on finite groups', 'Operator theory', 'Matrix analysis',
'Linear preserver problems', 'Tensor algebra', 'Multilinear algebra',
'Commutative algebra', 'Homological algebra', 'Associative algebras',
'Nonassociative algebras', 'Semigroup theory', 'Finite group theory',
'Combinatorial group theory', 'Representation theory', 'Invariant theory',
'Ring theory', 'Number theory of recurrences', 'Diophantine equations',
'Elementary number theory', 'Analytic number theory', 'p-adic analysis',
'Finite fields', 'Coding theory', 'Cryptographic combinatorics',
'Numerical semigroups', 'Integer partitions', 'Integer-valued polynomials',
'Differential algebra', 'Difference algebra', 'Real algebraic geometry',
'Tropical mathematics', 'Algebraic geometry', 'Knot theory',
'Low-dimensional topology', 'Algebraic topology', 'General topology',
'Order theory', 'Lattice theory', 'Set theory',
'Model theory', 'Computability theory', 'Proof theory',
'Type theory', 'Automata theory', 'Formal language theory',
'Combinatorial game theory', 'Optimal transport', 'Discrete optimization',
'Polynomial optimization', 'Metric geometry', 'Geometric measure theory',
'Numerical analysis', 'Dynamical systems', 'Category theory',
'Information theory', 'Tiling theory', 'Fractal geometry',
'Symmetric functions', 'Cluster algebras', 'Total positivity',
'Statistical mechanics combinatorics', 'Random walks', 'Positional games'
]
if __name__ == '__main__':
    target = Path(__file__).with_name('area_selection.json')
    if target.exists():
        raise SystemExit('Recorded draw already exists; refusing to redraw.')
    k = secrets.randbelow(len(AREAS))
    result = dict(method='secrets.randbelow (operating-system randomness)',
                  timestamp_utc=datetime.now(timezone.utc).isoformat(),
                  area_count=len(AREAS), zero_based_index=k,
                  one_based_index=k+1, selected_area=AREAS[k], areas=AREAS)
    target.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: val for key,val in result.items() if key != 'areas'},indent=2))
