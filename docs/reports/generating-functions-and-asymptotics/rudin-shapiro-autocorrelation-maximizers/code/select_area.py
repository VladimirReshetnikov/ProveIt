#!/usr/bin/env python3
"""Select uniformly from 100 mathematical areas; persist the single draw."""
import secrets, random, json, hashlib, argparse
from pathlib import Path
AREAS = '''Additive combinatorics
Algebraic combinatorics
Analytic combinatorics
Enumerative combinatorics
Extremal set theory
Design theory
Finite geometry
Ramsey theory
Graph coloring
Structural graph theory
Spectral graph theory
Graph polynomials
Hypergraph theory
Matroid theory
Combinatorial game theory
Discrete geometry
Convex geometry
Polytope theory
Lattice-point enumeration
Tiling theory
Coding theory
Finite fields
Finite groups
Combinatorial group theory
Semigroup theory
Ring theory
Commutative algebra
Polynomial identities
Representation theory
Invariant theory
Linear algebra and matrix inequalities
Nonnegative matrices
Tensor rank and decomposition
Spectral theory
Operator inequalities
Functional analysis
Banach-space geometry
Approximation theory
Orthogonal polynomials
Special functions
Real inequalities
Complex analysis
Univalent functions
Potential theory
Harmonic analysis
Fourier analysis on finite groups
Probability inequalities
Random walks
Markov chains
Branching processes
Percolation theory
Random combinatorial structures
Ergodic theory
Symbolic dynamics
Substitution sequences
Automata theory
Combinatorics on words
Formal languages
Type theory
Proof theory
Computability theory
Finite model theory
Universal algebra
Lattice theory
Order theory
General topology
Topological dynamics
Algebraic topology
Knot theory
Geometric topology
Metric geometry
Discrete differential geometry
Dynamical systems
Difference equations
Functional equations
Iteration theory
Asymptotic analysis
Diophantine equations
Diophantine approximation
Arithmetic functions
Prime-number theory
Modular arithmetic
p-adic analysis
Transcendental number theory
Continued fractions
Integer partitions
q-series
Modular forms
Elliptic curves
Algebraic number theory
Numerical semigroups
Combinatorial optimization
Integer programming
Polyhedral combinatorics
Discrete convex analysis
Optimization inequalities
Information theory
Quantum information mathematics
Boolean functions
Computational geometry'''.splitlines()
assert len(AREAS) == 100
if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    dest=args.output
    if dest.exists():
        raise SystemExit('Refusing to replace an existing selection record.')
    seed = secrets.randbits(128)
    index = random.Random(seed).randrange(len(AREAS))
    manifest = args.manifest
    dest.parent.mkdir(parents=True,exist_ok=True)
    result = dict(method='secrets.randbits(128) seed; random.Random(seed).randrange(100)',
                  seed=str(seed), index_zero_based=index, index_one_based=index+1,
                  area=AREAS[index], areas=AREAS, redraws=0,
                  manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest())
    dest.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'areas'}, indent=2))
