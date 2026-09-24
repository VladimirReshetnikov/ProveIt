#!/usr/bin/env python3
"""One uniform area draw using the operating system's random source."""
import secrets, json
from pathlib import Path
areas = [
'Additive combinatorics','Analytic number theory','Algebraic number theory','Diophantine approximation',
'Finite fields','Arithmetic dynamics','Combinatorial number theory','Integer partitions',
'Permutation patterns','Algebraic combinatorics','Enumerative combinatorics','Extremal set theory',
'Ramsey theory','Spectral graph theory','Structural graph theory','Graph polynomials',
'Graph labeling','Design theory','Coding theory','Matroid theory',
'Combinatorial geometry','Discrete geometry','Convex geometry','Lattice polytopes',
'Tiling theory','Combinatorics on words','Automata theory','Formal language theory',
'Semigroup theory','Finite group theory','Infinite group theory','Combinatorial group theory',
'Ring theory','Commutative algebra','Noncommutative algebra','Representation theory',
'Lie algebras','Universal algebra','Lattice theory','Order theory',
'Category theory','Type theory','Proof theory','Computability theory',
'Model theory','Set-theoretic topology','General topology','Algebraic topology',
'Knot theory','Low-dimensional topology','Differential geometry','Metric geometry',
'Geometric group theory','Dynamical systems','Symbolic dynamics','Ergodic theory',
'Probability inequalities','Discrete probability','Random walks','Stochastic processes',
'Special functions','Orthogonal polynomials','Continued fractions','Asymptotic analysis',
'Complex analysis','Geometric function theory','Harmonic analysis','Functional analysis',
'Banach space geometry','Operator theory','Matrix inequalities','Tensor algebra',
'Optimization theory','Discrete optimization','Numerical analysis','Approximation theory',
'Combinatorial game theory','Mathematical logic of games','Information theory','Boolean functions',
'Hypergraph theory','Incidence geometry','Finite geometry','Topological combinatorics',
'Cluster algebras','Tropical geometry','Algebraic statistics','Combinatorial commutative algebra',
'Symmetric functions','q-series','Difference equations','Functional equations',
'Fractional calculus','Integral inequalities','Potential theory','Fractal geometry']
index = secrets.randbelow(len(areas))
record = {'method':'secrets.randbelow; OS-backed uniform random draw, no redraw',
          'area_count': len(areas), 'zero_based_index':index,
          'one_based_index':index+1,'selected_area':areas[index], 'areas':areas}
Path(__file__).with_name('selection.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='areas'}, indent=2))
