"""Deterministic exact checks plus optional numerical Hessian smoke tests."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from collections import Counter
from pathlib import Path
import json
import random
from quartic_compiler import (Circuit, Gate, Constraint, compile_circuit,
                              or_circuit, evaluate_poly)

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / 'results'
RESULTS.mkdir(exist_ok=True)
RNG = random.Random(20260930)
counts = Counter()
maxima = Counter()


def audit(comp):
    stats = comp.structural_statistics()
    assert stats['degree'] == 4
    assert stats['coefficient_height'] <= 4
    assert stats['constant_coefficient'] == 1
    assert stats['max_incidence'] <= 3
    assert stats['max_interaction_degree'] <= 3
    assert stats['nonboolean_constraints'] == comp.variables - comp.circuit.inputs + 1
    assert stats['variables'] <= comp.circuit.inputs + 5 * len(comp.circuit.gates) + 5
    for key, value in stats.items():
        maxima[key] = max(maxima[key], value)
    pairs = Counter()
    for constraint in comp.constraints:
        support = sorted(constraint.support())
        for j, a in enumerate(support):
            for b in support[j + 1:]:
                pairs[(a, b)] += 1
    assert max(pairs.values(), default=0) <= 1
    counts['circuits_structurally_audited'] += 1
    return stats


circuits = [Circuit(1, (), 0), Circuit(0, (Gate('ZERO'),), 0),
            Circuit(0, (Gate('ONE'),), 0),
            Circuit(1, (Gate('NOT', (0,)),), 1),
            Circuit(2, (Gate('AND', (0, 1)),), 2),
            Circuit(1, (Gate('AND', (0, 0)),), 1)]
for _ in range(160):
    k = RNG.randrange(1, 5)
    gates = []
    for j in range(RNG.randrange(1, 13)):
        kind = RNG.choice(['AND', 'NOT', 'COPY', 'ZERO', 'ONE'])
        arity = {'AND': 2, 'NOT': 1, 'COPY': 1, 'ZERO': 0, 'ONE': 0}[kind]
        args = tuple(RNG.randrange(k + j) for _ in range(arity))
        gates.append(Gate(kind, args))
    circuits.append(Circuit(k, tuple(gates), RNG.randrange(k + len(gates))))

root_samples = []
for index, circ in enumerate(circuits):
    comp = compile_circuit(circ)
    audit(comp)
    p = comp.polynomial()
    for bits in product((0, 1), repeat=circ.inputs):
        root = comp.extend(bits)
        assert all(v in (0, 1) for v in root)
        energy = comp.energy(root)
        assert energy == evaluate_poly(p, root)
        assert energy == 1 - circ.run(bits)
        assert (energy == 0) == bool(circ.run(bits))
        counts['input_extensions_checked'] += 1
        if not energy and len(root_samples) < 100:
            root_samples.append((comp, root))
        for _ in range(2):
            mutant = list(root)
            at = RNG.randrange(comp.variables)
            mutant[at] = 1 - mutant[at]
            is_canonical = (tuple(mutant) == comp.extend(mutant[:circ.inputs])
                            and circ.run(mutant[:circ.inputs]) == 1)
            assert (comp.energy(mutant) == 0) == is_canonical
            counts['boolean_mutations_checked'] += 1
    if index < 6:
        accepted = 0
        for assignment in product((0, 1), repeat=comp.variables):
            good = (tuple(assignment) == comp.extend(assignment[:circ.inputs])
                    and circ.run(assignment[:circ.inputs]) == 1)
            assert (comp.energy(assignment) == 0) == good
            accepted += good
            counts['full_boolean_assignments_exhausted'] += 1
        assert accepted == sum(circ.run(bits)
                               for bits in product((0, 1), repeat=circ.inputs))

# Scalar rounding inequality on an exact rational grid.
for numerator in range(-128, 193):
    x = F(numerator, 64)
    d = min(abs(x), abs(x - 1))
    assert d <= 2 * abs(x * (x - 1))
    counts['scalar_rounding_checks'] += 1

# Gate Lipschitz bound used by the 1/64 rounding theorem.
for kind, args in [('AND', (1, 2)), ('NOT', (1, 2)), ('COPY', (1,))]:
    c = Constraint(kind, 0, args)
    dim = 1 + len(args)
    for bits in product((0, 1), repeat=dim):
        for delta in product((F(-1, 4), F(0), F(1, 4)), repeat=dim):
            x = tuple(F(a) + b for a, b in zip(bits, delta))
            rho = max(map(abs, delta), default=F(0))
            assert abs(c.value(x) - c.value(bits)) <= (3 + rho) * rho
            counts['gate_rounding_checks'] += 1

for comp, root in root_samples:
    n = comp.variables
    for _ in range(3):
        # Keep the total energy small despite the number of coordinates.
        x = [F(b) + F(RNG.choice((-1, 0, 1)), 1024 * n) for b in root]
        energy = comp.energy(x)
        assert energy <= F(1, 4096)
        rounded = tuple(int(v >= F(1, 2)) for v in x)
        assert rounded == root
        assert sum((a - b) ** 2 for a, b in zip(x, rounded)) <= 4 * energy
        counts['exact_low_energy_rounding_checks'] += 1

# Explicit dimension-free constants from the Hessian proof.
rho = F(1, 32)
lower = 2 - 30 * rho - 2 * rho**2
upper = (2 * (1 + 2*rho)**2 + 6*(1+rho)*(3+2*rho)
         + 4*rho*(1+rho) + 6*(3+rho)*rho)
assert lower > 1 and upper < 24
assert F(1, 8) + (3 + F(1, 4))*F(1, 4) == F(15, 16)
counts['exact_constant_checks'] = 3

# Optional floating-point checks. These are explicitly not exact proofs.
hessian = {'available': False}
try:
    import numpy as np
    mins_zero, maxs_zero, mins_box, maxs_box = [], [], [], []
    for comp, root in root_samples[:30]:
        n = comp.variables
        for is_zero in (True, False):
            x = np.array(root, dtype=float)
            if not is_zero:
                x += np.array([RNG.uniform(-1/32, 1/32) for _ in root])
            H = np.diag(12*x*x - 12*x + 2)
            for c in comp.constraints:
                grad = np.zeros(n)
                for i, value in c.gradient(x).items():
                    grad[i] = value
                H += 2*np.outer(grad, grad)
                if c.kind == 'AND':
                    a, b = c.args
                    H[a, b] -= 2*c.value(x)
                    H[b, a] -= 2*c.value(x)
            eig = np.linalg.eigvalsh(H)
            if is_zero:
                assert eig[0] >= 2 - 1e-9 and eig[-1] <= 20 + 1e-9
                mins_zero.append(float(eig[0])); maxs_zero.append(float(eig[-1]))
            else:
                assert eig[0] >= 1 - 1e-9 and eig[-1] <= 24 + 1e-9
                mins_box.append(float(eig[0])); maxs_box.append(float(eig[-1]))
            counts['numerical_hessian_checks'] += 1
    hessian = {'available': True, 'zeros_tested': len(mins_zero),
               'box_points_tested': len(mins_box),
               'min_eigenvalue_at_zeros': min(mins_zero),
               'max_eigenvalue_at_zeros': max(maxs_zero),
               'min_eigenvalue_in_boxes': min(mins_box),
               'max_eigenvalue_in_boxes': max(maxs_box)}
except ImportError:
    pass

examples = []
for t in range(9):
    circ = or_circuit(t)
    comp = compile_circuit(circ)
    stats = audit(comp)
    accepted = sum(circ.run(b) for b in product((0, 1), repeat=t))
    assert accepted == 2**t - 1
    probability = F(accepted, 2**t)
    examples.append({'horizon': t, 'roots': accepted,
                     'probability': str(probability), **stats})
    counts['geometric_example_horizons_checked'] += 1
    if t in (0, 1, 2, 3):
        comp.write_json(str(RESULTS / f'geometric_horizon_{t}.json'))

# Sharp interaction frontier: exact path/cycle/triangle dynamic programming.
from degree_two import count_degree_two
from quartic_compiler import multiply
for _ in range(120):
    n = RNG.randrange(1, 10)
    edges = [(j, j+1) for j in range(n-1)]
    if n >= 3 and RNG.choice((False, True)):
        edges.append((0, n-1))
    residuals = []
    for u, v in edges:
        # Forbid a randomly chosen local assignment using its indicator.
        a, b = RNG.randrange(2), RNG.randrange(2)
        pu = {(u,): 1} if a else {(): 1, (u,): -1}
        pv = {(v,): 1} if b else {(): 1, (v,): -1}
        residuals.append(multiply(pu, pv))
    if RNG.choice((False, True)):
        at = RNG.randrange(n)
        residuals.append({(at,): 1, (): -RNG.randrange(2)})
    expected = sum(all(evaluate_poly(p, bits) == 0 for p in residuals)
                   for bits in product((0, 1), repeat=n))
    assert count_degree_two(n, residuals) == expected
    counts['degree_two_dp_instances_checked'] += 1
for p in [{(0,): 1, (1,2): -1}, {(0,): 1, (1,): 1, (2,): -1}]:
    expected = sum(evaluate_poly(p, b) == 0 for b in product((0,1), repeat=3))
    assert count_degree_two(3, [p]) == expected
    counts['degree_two_dp_instances_checked'] += 1

# PAST slowdown example: geometric continuation probability 1/4.
first_moment = sum(F(3, 4**(n+1)) * 2**n for n in range(20))
second_partial = sum(F(3, 4**(n+1)) * 4**n for n in range(20))
assert first_moment < F(3, 2) and second_partial == 15
counts['slowdown_moment_checks'] = 2

report = {'status': 'PASS', 'seed': 20260930,
          'exact_checks': {k: v for k, v in counts.items()
                           if not k.startswith('numerical')},
          'exact_check_total': sum(v for k, v in counts.items()
                                   if not k.startswith('numerical')),
          'observed_structural_maxima': dict(maxima),
          'hessian_exact_lower_bound_at_radius_1_over_32': str(lower),
          'hessian_exact_upper_bound_at_radius_1_over_32': str(upper),
          'numerical_hessian_smoke_tests': hessian,
          'geometric_examples': examples,
          'scope': 'Finite exact checks and optional floating-point smoke tests; '
                   'not a machine-checked proof of the general theorems.'}
with open(RESULTS / 'verification_report.json', 'w') as f:
    json.dump(report, f, indent=2); f.write('\n')
print(json.dumps(report, indent=2))
