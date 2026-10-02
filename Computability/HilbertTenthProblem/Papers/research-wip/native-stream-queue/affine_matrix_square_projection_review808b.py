"""Independent affine-lattice checks and square-block projection.

The caller supplies an extracted archive root. Only the pinned verifier is
loaded. This is a review experiment, not a public matrix compiler.
"""
from collections import Counter
from contextlib import contextmanager
from fractions import Fraction
import hashlib
from itertools import combinations, product
import json
from math import comb, factorial
from pathlib import Path
import random
import sys
import types

SOURCE_SHA256 = '538a31307eb7a147b87104fdda687bc5d3683c1d248c1a67b736dbbbaf72faa7'


@contextmanager
def source(root):
    path = Path(root)/'verify.py'
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SOURCE_SHA256
    name = '_review_affine_808b'
    old = sys.modules.get(name)
    mod = types.ModuleType(name); mod.__file__ = str(path)
    sys.modules[name] = mod
    try:
        exec(compile(raw, str(path), 'exec'), mod.__dict__)
        yield mod
    finally:
        if old is None: sys.modules.pop(name, None)
        else: sys.modules[name] = old


def binomial(n, j):
    return comb(n, j) if n >= 0 else (-1)**j*comb(j-n-1, j)


def canonical(form):
    terms = Counter()
    for name, coefficient in form.terms: terms[name] += coefficient
    return form.constant, tuple(sorted((n, c) for n, c in terms.items() if c))


def projected(circuit, inputs, registers, remaining_aux):
    """Return reduced blocks and the uniquely restored original auxiliary list."""
    circuit.validate()
    assert len(registers) == len(circuit.gates)
    values = dict(inputs)
    values.update((g.name, z) for g, z in zip(circuit.gates, registers))
    reduced = []; restored = []; cursor = 0
    for g, z in zip(circuit.gates, registers):
        x, y = g.left.evaluate(values), g.right.evaluate(values)
        if canonical(g.left) == canonical(g.right):
            assert x == y
            u = 2*z-x
            reduced.append((2*x, u))
        else:
            u = remaining_aux[cursor]; cursor += 1
            reduced.extend(((x+y, u), (x-y, u-2*z+y)))
        restored.append(u)
    assert cursor == len(remaining_aux)
    return reduced, circuit.output.evaluate(values), tuple(restored)


def run(root):
    import sympy as sp
    counts = Counter(); rng = random.Random(808)
    with source(root) as m:
        # Independent factorial/generalized-binomial evaluation and a matrix
        # determinant, rather than the author's truncated-ring multiplication.
        for k in range(1, 9):
            nodes = rng.sample(range(-30, 31), k+1)
            points = [m.coordinates(k, n) for n in nodes]
            assert sp.Matrix([[1, *v] for v in points]).det() != 0
            counts['affine_independence_determinants'] += 1
            for n in [-10**40-3, -101, -1, 0, 1, 137, 10**35+7]:
                lam = m.coordinates(k, n)
                assert lam == tuple(binomial(n,i)*binomial(k-n,k-i) for i in range(1,k+1))
                for power in range(1, k+1):
                    assert sum(lam[i-1]*i**power for i in range(1,k+1)) == n**power
                counts['large_integer_interpolation_cases'] += 1
        for k, e in product(range(1, 13), range(1, 39)):
            P = m.period(k, e)
            for n in [0, P, -P, 3*P, 10**32+7, -10**33-11]:
                assert all(binomial(n,j)%e == 0 for j in range(1,k+1)) == (n%P == 0)
                assert all((a-b)%e == 0 for a,b in zip(m.coordinates(k,n+P),m.coordinates(k,n)))
                counts['independent_period_checks'] += 1
            for p in sp.factorint(P):
                assert any(binomial(P//p,j)%e for j in range(1,k+1))
                counts['proper_period_divisors_excluded'] += 1
        # Every small allowed finite set, including arbitrary negative shifts.
        for k in range(1, 5):
            for size in range(1, k+1):
                for F in combinations((-9, -2, 1, 7, 13), size):
                    c0 = sp.Matrix(m.coordinates(k,F[0]))
                    cols = [sp.Matrix(m.coordinates(k,n))-c0 for n in F[1:]]
                    B = sp.Matrix.hstack(*cols) if cols else sp.zeros(k,0)
                    for n in range(-12, 17):
                        v = sp.Matrix(m.coordinates(k,n))-c0
                        if not cols: accepted = v == sp.zeros(k,1)
                        else:
                            try: sol, free = B.gauss_jordan_solve(v)
                            except ValueError: accepted = False
                            else:
                                assert not free
                                accepted = all(x.q == 1 for x in sol)
                        assert accepted == (n in F)
                        counts['finite_hit_set_membership'] += 1
        # Literal symbolic matrix and square projection identity.
        x,y,z,u = sp.symbols('x y z u', integer=True)
        r1 = 2*u-(x+y)*(x+y-1)
        r2 = 2*(u-2*z+y)-(x-y)*(x-y-1)
        assert sp.expand(r1-r2-4*(z-x*y)) == 0
        assert sp.expand(r1.subs({y:x,u:2*z-x}, simultaneous=True)-4*(z-x*x)) == 0
        assert sp.expand(r2.subs({y:x,u:2*z-x}, simultaneous=True)) == 0
        t,s = sp.symbols('t s', integer=True)
        assert sp.Matrix([[1,t,s],[0,1,t],[0,0,1]]).det() == 1
        counts['symbolic_matrix_projection_identities'] = 4
        A, G, C = m.Affine, m.Gate, m.Circuit
        # Two source forms test syntactically distinct but equal square operands.
        circuits = [C(('a','b','c'), (
            G('r0', A(0,(('a',1),)), A(0,(('b',1),))),
            G('r1', A(0,(('r0',1),('c',1))), A(0,(('r0',1),('c',1)))),
            G('r2', A(0,(('a',1),('c',1))), A(0,(('b',1),)))),
            A(-7,(('r1',1),('r2',-1)))),
            C(('a','b'), (G('r0', A(1,(('a',2),('b',-1))),
                                      A(1,(('b',-1),('a',1),('a',1)))),),
              A(0,(('r0',1),)))]
        examples = []
        for circuit in circuits:
            square = [canonical(g.left) == canonical(g.right) for g in circuit.gates]
            g, s = len(square), sum(square)
            for values in product(range(-3,4), repeat=len(circuit.variables)):
                inputs = dict(zip(circuit.variables, values))
                registers, aux = circuit.witness(inputs)
                remaining = tuple(u for u, is_square in zip(aux,square) if not is_square)
                blocks, final, restored = projected(circuit,inputs,registers,remaining)
                assert restored == aux
                assert all(m.cyclic_member(t,b) for t,b in blocks)
                assert circuit.quartic_value(inputs,registers,restored) == final**2
                counts['canonical_square_projection_pairs'] += 1
                for _ in range(5):
                    rawreg = tuple(rng.randrange(-8,9) for _ in registers)
                    rawaux = tuple(rng.randrange(-8,9) for _ in remaining)
                    blocks, final, lifted = projected(circuit,inputs,rawreg,rawaux)
                    new = final**2+sum((2*b-t*(t-1))**2 for t,b in blocks)
                    old = circuit.quartic_value(inputs,rawreg,lifted)
                    assert old == new
                    assert (new == 0) == (rawreg == registers and rawaux == remaining and circuit.output.evaluate(dict(inputs,**dict(zip((q.name for q in circuit.gates),registers)))) == 0)
                    counts['signed_full_polynomial_graph_identities'] += 1
            examples.append(dict(gates=g, square_gates=s, old_dimension=6*g+2,
                new_dimension=6*g-3*s+2, old_added_coordinates=2*g,
                new_added_coordinates=2*g-s, old_residuals=2*g+1,
                new_residuals=2*g-s+1, polynomial_degree_bound=4))
        # Public methods revalidate causality and exact coordinate types.
        valid = circuits[0]
        def reject(fn):
            try: fn()
            except (ValueError,TypeError): counts['malformed_calls_rejected'] += 1
            else: raise AssertionError('invalid circuit call accepted')
        for bad in (True,False,1.0,Fraction(1),'1'):
            reject(lambda: valid.witness({'a':bad,'b':0,'c':0}))
            reject(lambda: valid.quartic_value({'a':0,'b':0,'c':0},(bad,0,0),(0,0,0)))
            reject(lambda: valid.accepts({'a':0,'b':0,'c':0},(0,0,0),(bad,0,0)))
            reject(lambda: m.multiplication_member(1,2,2,bad))
        for bad in (C(('a','a'),(),A()), C(('a',),(G('r',A(0,(('r',1),)),A()),),A()),
                    C(('a',),(),A(0,(('missing',1),))),
                    C(('a',),(G('a',A(),A()),),A())):
            reject(bad.validate)
        gates = [G('r',A(0,(('a',1),)),A(1))]
        mutable = C(('a',), gates, A(0,(('r',1),)))
        assert mutable.witness({'a':0}) == ((0,), (0,))
        gates[0] = G('r',A(0,(('r',1),)),A(1))
        reject(lambda: mutable.witness({'a':0}))
    return dict(status='PASS', source_sha256=SOURCE_SHA256, counts=dict(counts),
        square_projection_examples=examples,
        scope='Exact integer checks and supplied proofs; no numerical universal subgroup, priority claim, or arithmetic-operation record.')


if __name__ == '__main__':
    if not __debug__: raise RuntimeError('Assertions must be enabled')
    print(json.dumps(run(Path(sys.argv[1])),indent=2))
