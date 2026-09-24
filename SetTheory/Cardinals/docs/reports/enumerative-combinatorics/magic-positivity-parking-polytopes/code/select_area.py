#!/usr/bin/env python3
"""Draw one subject uniformly before looking for a specific problem."""
import argparse
import json
import random
import secrets
from pathlib import Path

AREAS = """Additive combinatorics
Algebraic combinatorics
Algebraic geometry
Algebraic graph theory
Algebraic number theory
Algebraic topology
Analytic combinatorics
Analytic number theory
Approximation theory
Automata theory
Banach space theory
Braid groups
Calculus of variations
Cellular automata
Coding theory
Combinatorial commutative algebra
Combinatorial designs
Combinatorial game theory
Combinatorial geometry
Combinatorics on words
Commutative algebra
Complex dynamics
Computability theory
Computational geometry
Convex geometry
Cryptographic Boolean functions
Descriptive set theory
Diophantine approximation
Difference equations
Differential algebra
Differential geometry
Discrete dynamical systems
Discrete geometry
Discrepancy theory
Distance geometry
Enumerative combinatorics
Ergodic theory
Extremal graph theory
Finite fields
Finite group theory
Formal languages and grammars
Fourier analysis
Functional equations
General topology
Geometric group theory
Geometry of numbers
Graph colorings
Graph polynomials
Harmonic analysis
Hypergraph theory
Incidence geometry
Information theory
Integer partitions
Integral transforms
Invariant theory
Knot theory
Lattice theory
Lie algebras
Linear algebra and matrix inequalities
Logic and proof theory
Low-dimensional topology
Mathematical billiards
Mathematical probability
Matroid theory
Metric geometry
Model theory
Modular forms
Moment problems
Nonassociative algebra
Noncommutative algebra
Numerical analysis
Operator theory
Optimization
Ordered algebraic structures
Order theory
Orthogonal polynomials
Packing and covering
Partial differential equations
Permutation patterns
Polynomial inequalities
Polyhedral combinatorics
Potential theory
q-Series and basic hypergeometric functions
Quiver representations
Ramsey theory
Random graphs
Real algebraic geometry
Recurrence sequences
Representation theory
Riordan arrays
Semigroup theory
Set theory
Spectral graph theory
Special functions
Substitution dynamical systems
Symbolic dynamics
Symmetric functions
Tensor decomposition
Topological dynamics
Tropical geometry
Type theory
Ultrametric analysis
Uniform distribution
Universal algebra
Variational inequalities
Vertex algebras
Well-quasi-orders
Zero-sum theory
Discrete differential geometry
Algebraic statistics
Numerical semigroups
Positivity and total positivity
Rewriting systems
Computational number theory
Fractional calculus
Nonstandard analysis
Geometric measure theory
Boolean lattices and set systems
Random walks
Higher category theory""".splitlines()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seed', type=int)
    parser.add_argument('--output', type=Path, default=Path('selection.json'))
    args = parser.parse_args()
    seed = secrets.randbits(128) if args.seed is None else args.seed
    rng = random.Random(seed)
    index = rng.randrange(len(AREAS))
    result = {'method': 'Python random.Random, seeded by secrets.randbits(128)',
              'seed': seed, 'number_of_areas': len(AREAS),
              'zero_based_index': index, 'one_based_index': index + 1,
              'selected_area': AREAS[index], 'areas': AREAS,
              'selection_policy': 'First draw, no redraw after seeing the result.'}
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k != 'areas'}, indent=2))

if __name__ == '__main__':
    main()
