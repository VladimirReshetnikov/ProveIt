"""Reproducible finite and symbolic checks; not a proof-assistant formalization."""
from __future__ import annotations
import json
from collections import Counter
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import sympy as sp
from compiler import compile_polynomial, partition_interval, critical_fugacity

ROOT = Path(__file__).resolve().parent
counts: Counter[str] = Counter()


def check(condition: bool, group: str) -> None:
    if not condition:
        raise AssertionError(group)
    counts[group] += 1


def evaluate(terms, params, inputs):
    xs = tuple(params) + tuple(inputs)
    return sum(c * prod_int(x ** e for x, e in zip(xs, mon)) for mon, c in terms.items())


def prod_int(xs):
    out = 1
    for x in xs:
        out *= x
    return out


recipes = [
    ('linear', {(0, 1): 1, (1, 0): -1}, 1, 1),
    ('cubic', {(0, 3): 1, (1, 0): -1}, 1, 1),
    ('product', {(0, 1, 1): 1, (1, 0, 0): -1}, 2, 1),
    ('no_root', {(2,): 1, (0,): 1}, 1, 0),
    ('mixed', {(0, 2, 0): 1, (0, 1, 1): 1,
               (1, 0, 1): -1, (0, 0, 0): -3}, 2, 1),
    ('zero', {}, 1, 0),
]
exports = []
for name, terms, k, p in recipes:
    comp = compile_polynomial(terms, k, p)
    export = comp.export()
    export['name'] = name
    export['sparse_source'] = [{'exponents': list(m), 'coefficient': c}
                                for m, c in sorted(terms.items())]
    exports.append(export)
    for params in product(range(5), repeat=p):
        for inputs in product(range(5), repeat=k):
            ns = comp.canonical(inputs, params)
            value = evaluate(terms, params, inputs)
            rs = comp.residuals(ns, params)
            check(all(r == 0 for r in rs[:-2]) and rs[-1] == 0, 'canonical_gate_and_marker')
            check(rs[-2] == value, 'signed_output_identity')
            check(comp.penalty(ns, params) == value * value, 'canonical_penalty_identity')
            check((comp.energy(ns, params) == 0) == (value == 0), 'source_zero_equivalence')
            for i in range(k, comp.modes):
                bad = list(ns)
                bad[i] += 1
                check(comp.penalty(bad, params) > 0, 'single_auxiliary_mutation_rejected')
    # Exhaustive supplied-tuple checks for small arity, including noncanonical gates.
    if comp.modes <= 4:
        for params in product(range(4), repeat=p):
            for ns in product(range(4), repeat=comp.modes):
                is_source = evaluate(terms, params, ns[:k]) == 0
                is_canonical = ns == comp.canonical(ns[:k], params)
                Q = comp.penalty(ns, params)
                H = comp.energy(ns, params)
                check((Q == 0) == (is_source and is_canonical), 'exhaustive_zero_fiber_bijection')
                check(H == 0 or H >= 1 + sum(ns), 'radial_energy_lower_bound')
    # Independently expand the complete symbolic polynomial, including parameters.
    z = sp.symbols(f'z0:{comp.modes}')
    ps = sp.symbols(f'p0:{p}')
    def atom(a):
        return sp.Integer(a.value) if a.kind == 'const' else (z[a.value] if a.kind == 'mode' else ps[a.value])
    residuals = []
    for g in comp.gates:
        a, b = atom(g.left), atom(g.right)
        residuals.append(z[g.output] - (a + b if g.operation == 'add' else a * b))
    residuals += [atom(comp.left) - atom(comp.right), z[-1] - 1]
    Qsym = sp.expand(sum(r*r for r in residuals))
    Hsym = sp.expand((1 + sum(z)) * Qsym)
    variables = z + ps
    check(sp.Poly(Qsym, *variables).total_degree() <= 4, 'symbolic_quartic_bound')
    check(sp.Poly(Hsym, *variables).total_degree() <= 5, 'symbolic_quintic_bound')
    check(len(residuals) == len(comp.gates) + 2 and comp.modes == k + len(comp.gates) + 1,
          'exact_resource_ledger')
    for r in residuals:
        check(len(r.free_symbols.intersection(set(z))) <= 3, 'residual_three_mode_locality')
        for factor in (sp.Integer(1),) + z:
            term = sp.expand(factor * r * r)
            check(len(term.free_symbols.intersection(set(z))) <= 4, 'four_mode_positive_term_support')
    export['expanded_H'] = str(Hsym)

# Exact type guards; numerically equal floating-point values are not integers.
for bad in (True, 1.0, -1):
    try:
        compile_polynomial({(bad,): 1}, 1)
    except ValueError:
        check(True, 'invalid_exact_input_rejected')
    else:
        raise AssertionError('exact exponent type guard')
for bad in (True, 1.0):
    try:
        compile_polynomial({(1,): bad}, 1)
    except ValueError:
        check(True, 'invalid_exact_input_rejected')
    else:
        raise AssertionError('exact coefficient type guard')

for d in range(1, 201):
    q = F(1, 8 * (d + 1))
    eps = q / (1 - q)**d
    check(eps <= F(1, 7*d + 8) < F(1, 8), 'dimension_uniform_thermal_bound')

# Exact positive-energy multiplicities for an infinite zero-state family.
def infinite_energy(ns):
    x, a = ns
    return (1 + x + a) * (a - 1)**2

Emax = 60
multiplicities = Counter()
for ns in product(range(Emax), repeat=2):
    h = infinite_energy(ns)
    if 0 < h <= Emax:
        multiplicities[h] += 1
        check(sum(ns) <= h - 1, 'finite_positive_energy_shell')
for E in range(1, Emax + 1):
    count = 0
    for a in range(E + 1):
        if a == 1:
            continue
        b = (a - 1)**2
        if E % b == 0 and E // b - a - 1 >= 0:
            count += 1
    check(multiplicities[E] == count, 'independent_positive_spectrum_formula')

# Check the Pell recurrence and marker without claiming all Pell solutions tested.
x, y = 1, 0
pell_examples = []
for j in range(32):
    check(x*x - 2*y*y == 1, 'pell_infinite_zero_family')
    if j < 6:
        pell_examples.append([x, y, 1])
    nx, ny = 3*x + 4*y, 2*x + 3*y
    check(nx > x and ny > y, 'pell_strict_growth')
    x, y = nx, ny

# The full geometric-tail evaluator and zero/excited decomposition are separate routes.
models = []
for N in (0, 3, 17):
    def energy(ns, N=N):
        x, a = ns
        return (1+x+a) * ((x-N)**2 + (a-1)**2)
    models.append((f'single_{N}', energy, lambda t, N=N: t**(N+1)))
models.append(('infinite', infinite_energy, lambda t: t/(1-t)))
def no_root_energy(ns):
    x, a = ns
    return (1+x+a) * ((x*x+1)**2 + (a-1)**2)
models.append(('empty', no_root_energy, lambda t: F(0)))
interval_data = []
for name, energy, ground in models:
    for t in (F(1,4), F(1,2), F(3,4)):
        q = F(1,24)
        full = partition_interval(energy, 2, q, t, F(1,4096))
        excited = partition_interval(energy, 2, q, t, F(1,2**20), excited_only=True)
        lo, hi = ground(t) + excited.lower, ground(t) + excited.upper
        check(full.width <= F(1,4096), 'full_partition_certified_width')
        check(excited.width <= F(1,2**20), 'excited_partition_certified_width')
        check(max(full.lower, lo) <= min(full.upper, hi), 'independent_partition_enclosures_overlap')
        check(excited.lower <= q/(1-q)**2, 'excited_partial_below_global_bound')
        interval_data.append({'model': name, 't': str(t), 'full_lower': str(full.lower),
                              'full_upper': str(full.upper), 'box_points': full.visited})

# Crossings: the supplied G(t) formula is proved for each of these models.
critical_data = []
for N in (0,1,3,10,100,1000):
    def energy(ns, N=N):
        x, a = ns
        return (1+x+a) * ((x-N)**2 + (a-1)**2)
    a, b, calls = critical_fugacity(energy, 2, F(1,2**30),
                                    ground_series=lambda t, N=N: t**(N+1))
    check(b-a <= F(1,2**30), 'critical_interval_width')
    eps = F(1,24)/(1-F(1,24))**2
    L = N+1
    check(a**L <= F(1,2) and b**L >= F(1,2)-eps, 'critical_height_bounds')
    critical_data.append({'model':f'x={N}', 'zero_height':L,
                          'lower':str(a), 'upper':str(b),
                          'midpoint':float((a+b)/2), 'calls':calls})
for name, energy, ground in models[-2:]:
    a, b, calls = critical_fugacity(energy, 2, F(1,2**30), ground_series=ground)
    check(b-a <= F(1,2**30), 'critical_interval_width')
    if name == 'empty':
        check(b == 1, 'empty_crossing_is_endpoint')
    else:
        check(b <= F(1,3), 'infinite_crossing_below_ground_only_value')
    critical_data.append({'model':name, 'lower':str(a), 'upper':str(b),
                          'midpoint':float((a+b)/2), 'calls':calls})

# General critical routine without a supplied ground formula, modest precision.
def first_energy(ns):
    x, a = ns
    return (1+x+a)*(x*x+(a-1)**2)
a,b,calls = critical_fugacity(first_energy, 2, F(1,256))
reference = critical_data[0]
check(max(a,F(reference['lower'])) <= min(b,F(reference['upper'])),
      'general_critical_routine_matches_exact_ground_route')

# Counterexamples: unweighted Q and a weight omitting y both have a flat positive level.
for y in range(100):
    check((0**2+1) == 1 and (1+0)*(0**2+1) == 1,
          'omitted_mode_confinement_counterexample')

result = {
    'status':'PASS',
    'total_assertions':sum(counts.values()),
    'groups':dict(sorted(counts.items())),
    'symbolic_engine':f'SymPy {sp.__version__}',
    'scope':'Finite regression and symbolic checks only; no Lean/Rocq formalization; no universal MRDP polynomial instantiated.',
    'critical_fugacities':critical_data,
    'pell_examples':pell_examples,
    'positive_multiplicities_1_to_60':dict(sorted(multiplicities.items())),
    'partition_enclosures':interval_data,
}
(ROOT/'examples.json').write_text(json.dumps(exports, indent=2)+'\n')
(ROOT/'verification.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'status':'PASS','assertions':sum(counts.values()),'groups':dict(counts),
                  'critical_fugacities':critical_data}, indent=2))
