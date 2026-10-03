"""Guarded simplification of the actual bounded FRACTRAN report compiler.

All semantic zero-set claims are over NONNEGATIVE INTEGER witnesses.  This
is a horizon-indexed family, not a fixed-arity universal Diophantine bound.
The frozen report compiler is loaded by path and its entire source hashed.
"""
import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random
import sys


ROOT = Path(__file__).resolve().parents[5]
IMPORTED = ROOT / ('SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/'
                  'canonical-diophantine-certificates/code/'
                  '04-witness-faithful-diophantine_compiler.py')
IMPORTED_SHA256 = '23c0c0ce8859a7a70eec4b8327607bf0ce18badd096a1afa8a3bed1c2981f767'
MODULE_NAME = '_fdrp_frozen_report_compiler'
STAGES = ('parent', 'delete', 'linearize')


def exact_equal(actual, expected):
    """Canonical packets require exact types, not Python's 1 == 1.0 == True."""
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return (all(type(key) is str for key in actual)
                and actual.keys() == expected.keys()
                and all(exact_equal(actual[key], value) for key, value in expected.items()))
    if isinstance(expected, (list, tuple)):
        return len(actual) == len(expected) and all(exact_equal(a, b) for a, b in zip(actual, expected))
    return actual == expected


def frozen_compiler():
    if hashlib.sha256(IMPORTED.read_bytes()).hexdigest() != IMPORTED_SHA256:
        raise ValueError('frozen report compiler changed; review before updating hash')
    if MODULE_NAME not in sys.modules:
        spec = importlib.util.spec_from_file_location(MODULE_NAME, IMPORTED)
        module = importlib.util.module_from_spec(spec)
        sys.modules[MODULE_NAME] = module
        spec.loader.exec_module(module)
    return sys.modules[MODULE_NAME]


def validate_spec(program, start, finish, horizon, terminal):
    if not isinstance(program, (list, tuple)) or not program:
        raise ValueError('a nonempty fixed FRACTRAN program is required')
    for fraction in program:
        if (not isinstance(fraction, (list, tuple)) or len(fraction) != 2
                or any(type(v) is not int or v <= 0 for v in fraction)):
            raise ValueError('fractions must contain two positive integers')
    if (type(start) is not int or start <= 0
            or type(finish) is not int or finish <= 0
            or type(horizon) is not int or horizon < 0
            or type(terminal) is not bool):
        raise ValueError('positive endpoints, natural horizon and Boolean terminal required')


def canonical_parent(program, start, finish, horizon, terminal=False):
    validate_spec(program, start, finish, horizon, terminal)
    compiler = frozen_compiler()
    normalized = compiler.normalize_fractions(program)
    system = compiler.compile_fractran(normalized, start, finish, horizon,
                                      terminal=terminal, witness=False)
    return {
        'format': 'bounded-fractran-natural-residuals-v1',
        'stage': 'parent',
        'domain': 'nonnegative integers',
        'spec': {'program': [list(f) for f in normalized], 'start': start,
                 'finish': finish, 'horizon': horizon, 'terminal': terminal},
        'variables': list(system.variables),
        'residuals': [[label, polynomial.as_json()]
                      for label, polynomial in system.residuals],
        'imported_source_file_sha256': IMPORTED_SHA256,
        'scope': 'fixed program and horizon; same-coordinate natural zero sets',
    }


def rewrite(old, *, linearize=False):
    if type(linearize) is not bool:
        raise ValueError('linearize must be Boolean')
    if not isinstance(old, dict) or 'spec' not in old:
        raise ValueError('complete canonical parent required')
    spec = old['spec']
    expected = canonical_parent(**spec)
    if not exact_equal(old, expected):
        raise ValueError('complete canonical parent required')
    compiler = frozen_compiler()
    by_label = {label: terms for label, terms in old['residuals']}
    if len(by_label) != len(old['residuals']):
        raise ValueError('duplicate residual label')
    removed = set()
    replacements = {}
    for t in range(spec['horizon']):
        for j in range(1, len(spec['program']) + 1):
            z, rem, u = [compiler.Poly.cast(0) + compiler.Poly({(f'{p}_{t}_{j}',): 1})
                         for p in ('z', 'rem', 'u')]
            required = {
                f'zero_bit_{t}_{j}': z * (z - 1),
                f'zero_test_{t}_{j}': z * rem,
                f'positive_test_{t}_{j}': rem - (1 - z) * (u + 1),
                f'inactive_zero_{t}_{j}': z * u,
            }
            for label, polynomial in required.items():
                if by_label.get(label) != polynomial.as_json():
                    raise ValueError('actual divisibility source differs from theorem')
            removed.update((f'zero_bit_{t}_{j}', f'zero_test_{t}_{j}'))
            if linearize:
                replacements[f'positive_test_{t}_{j}'] = (rem - u + z - 1).as_json()
    out = deepcopy(old)
    out['stage'] = 'linearize' if linearize else 'delete'
    out['residuals'] = [[label, replacements.get(label, deepcopy(terms))]
                        for label, terms in old['residuals'] if label not in removed]
    return out


def build(program, start, finish, horizon, terminal=False, stage='linearize'):
    if type(stage) is not str or stage not in STAGES:
        raise ValueError('unknown stage')
    old = canonical_parent(program, start, finish, horizon, terminal)
    return old if stage == 'parent' else rewrite(old, linearize=stage == 'linearize')


def checked_packet(packet):
    if not isinstance(packet, dict) or 'stage' not in packet or 'spec' not in packet:
        raise ValueError('complete canonical packet required')
    if not exact_equal(packet, build(**packet['spec'], stage=packet['stage'])):
        raise ValueError('complete canonical packet required')
    return packet


def polynomial_source(packet):
    """A literal, fully charged sparse-residual SLP; no cross-row CSE.

    Terms with positive coefficients precede negative terms.  Within each
    sign, monomials have the source's lexicographic order.  Magnitude-one
    coefficients need no multiplication; every other scalar multiplication
    is charged.  Each residual is squared and all squares are added.
    """
    checked_packet(packet)
    source = []

    def gate(op, a, b):
        name = f'fdrp_g{len(source):06d}'
        source.append([name, op, a, b])
        return name

    def magnitude(term):
        coefficient = abs(term['coefficient'])
        monomial = term['monomial']
        if not monomial:
            return coefficient
        value = monomial[0]
        for variable in monomial[1:]:
            value = gate('*', value, variable)
        return value if coefficient == 1 else gate('*', coefficient, value)

    squares = []
    for _, terms in packet['residuals']:
        ordered = [t for t in terms if t['coefficient'] > 0]
        ordered += [t for t in terms if t['coefficient'] < 0]
        if not ordered:
            value = 0
        else:
            first, *rest = ordered
            value = magnitude(first)
            if first['coefficient'] < 0:
                value = gate('-', 0, value)
            for term in rest:
                value = gate('+' if term['coefficient'] > 0 else '-',
                             value, magnitude(term))
        squares.append(gate('*', value, value))
    output = squares[0]
    for square in squares[1:]:
        output = gate('+', output, square)
    return source, output


def integer_values(packet, assignment):
    """Algebraic evaluator also used on signed assignments; no semantic claim."""
    checked_packet(packet)
    if (set(assignment) != set(packet['variables'])
            or any(type(value) is not int for value in assignment.values())):
        raise ValueError('an exact integer assignment to all variables is required')
    values = []
    for _, terms in packet['residuals']:
        value = 0
        for term in terms:
            monomial = term['coefficient']
            for name in term['monomial']:
                monomial *= assignment[name]
            value += monomial
        values.append(value)
    return values


def evaluate(packet, assignment):
    values = integer_values(packet, assignment)
    if any(value < 0 for value in assignment.values()):
        raise ValueError('semantic witnesses must be nonnegative integers')
    return sum(value * value for value in values)


def source_value(source, output, assignment):
    values = dict(assignment)
    for name, op, a, b in source:
        if name in values or op not in ('+', '-', '*'):
            raise ValueError('invalid literal SLP')
        a = values[a] if isinstance(a, str) else a
        b = values[b] if isinstance(b, str) else b
        values[name] = a + b if op == '+' else a - b if op == '-' else a * b
    return values[output]


def ledger(packet):
    source, output = polynomial_source(packet)
    variables = set(packet['variables'])
    by = {row[0]: row[2:] for row in source}
    need = set()
    todo = [output]
    inputs = set()
    while todo:
        name = todo.pop()
        if type(name) is int:
            continue
        if name in variables:
            inputs.add(name)
        elif name not in need:
            need.add(name)
            todo.extend(by[name])
    assert need == set(by) and inputs == variables
    count = Counter(row[1] for row in source)
    degrees = {v: 1 for v in variables}
    for name, op, a, b in source:
        da = degrees[a] if isinstance(a, str) else 0
        db = degrees[b] if isinstance(b, str) else 0
        degrees[name] = da + db if op == '*' else max(da, db)
    return {'variables': len(variables), 'residuals': len(packet['residuals']),
            'M': count['*'], 'A': count['+'] + count['-'],
            'operations': len(source), 'degree_upper_bound': degrees[output],
            'source': source, 'output': output,
            'source_sha256': hashlib.sha256(json.dumps(source, separators=(',', ':')).encode()).hexdigest()}


def algebra_checks():
    counts = Counter()
    # Complete bounded cubes of local natural candidates, without assuming bits.
    for rho, u, z in itertools.product(range(13), repeat=3):
        B, ZR, R, Z, L = z * (z - 1), z * rho, rho - (1 - z) * (u + 1), z * u, rho - u + z - 1
        assert (R == Z == 0) == (B == ZR == R == Z == 0)
        assert (R == Z == 0) == (L == Z == 0)
        assert R == L + Z
        counts['local_natural_candidates'] += 1
    for n in range(65):
        for b in range(1, 14):
            q, rho = divmod(n, b)
            z = int(rho == 0)
            u = max(rho - 1, 0)
            gap = b - 1 - rho
            assert n - b * q - rho == rho + gap - (b - 1) == 0
            assert rho - u + z - 1 == z * u == 0
            counts['canonical_divisions_including_zero_and_denominator_one'] += 1
    return counts


def audit():
    counts = algebra_checks()
    rng = random.Random(20261002)
    compiler = frozen_compiler()
    examples = []
    specs = [([(3, 2), (5, 3)], 8, 125, 6, False),
             ([(3, 2), (5, 3)], 8, 125, 6, True),
             ([(2, 2)], 1, 1, 0, False),
             ([(1, 1)], 1, 1, 0, True),
             ([(1, 2), (1, 1)], 1, 1, 1, False),
             ([(6, 4), (10, 6)], 8, 125, 6, True)]
    for program, start, finish, horizon, terminal in specs:
        forms = [build(program, start, finish, horizon, terminal, stage) for stage in STAGES]
        records = [ledger(packet) for packet in forms]
        r = len(forms[0]['spec']['program'])
        k = r * horizon
        assert all(forms[0]['variables'] == p['variables'] for p in forms)
        assert records[0]['residuals'] == horizon * (8 * r + 3) + 2 + terminal * 2 * r
        assert records[1]['residuals'] == records[2]['residuals'] == horizon * (6 * r + 3) + 2 + terminal * 2 * r
        assert records[0]['variables'] == horizon * (7 * r + 2) + 1 + terminal * 3 * r
        assert [records[0]['M'] - a['M'] for a in records[1:]] == [4 * k, 5 * k]
        assert [records[0]['A'] - a['A'] for a in records[1:]] == [3 * k, 4 * k]
        for i in range(40):
            assignment = {v: rng.randrange(-5, 9) if i % 2 else rng.randrange(9)
                          for v in forms[0]['variables']}
            energies = []
            for packet, record in zip(forms, records):
                energy = sum(v * v for v in integer_values(packet, assignment))
                assert energy == source_value(record['source'], record['output'], assignment)
                energies.append(energy)
                counts['independent_source_output_comparisons'] += 1
            deletion = linearization = 0
            for t in range(horizon):
                for j in range(1, r + 1):
                    z, rho, u = (assignment[f'{v}_{t}_{j}'] for v in ('z', 'rem', 'u'))
                    L, Z = rho - u + z - 1, z * u
                    deletion += (z * (z - 1)) ** 2 + (z * rho) ** 2
                    linearization += 2 * L * Z + Z * Z
            assert energies[0] - energies[1] == deletion
            assert energies[1] - energies[2] == linearization
            counts['off_zero_full_compiler_corrections'] += 1
            counts['signed_off_zero_full_compiler_corrections'] += i % 2
        examples.append({'spec': forms[0]['spec'], 'forms': [dict(stage=s, **v) for s, v in zip(STAGES, records)]})
    # Actual finite runs, including repeated denominators, unreduced input
    # fractions, positive/zero remainders, priority and first-halting extensions.
    programs = [[(a, b)] for a in range(1, 4) for b in range(1, 5)]
    programs += [[(a, b), (c, d)] for a, b, c, d in itertools.product(range(1, 3), range(1, 4), range(1, 3), range(1, 4))]
    for program in programs:
        for start in range(1, 9):
            for horizon in range(4):
                rows = compiler.fractran_run(program, start, horizon)
                if rows is None:
                    continue
                finish = rows[-1]
                terminal_options = [False]
                if compiler.fractran_run(program, finish, 1) is None:
                    terminal_options.append(True)
                for terminal in terminal_options:
                    old = compiler.compile_fractran(program, start, finish, horizon, terminal=terminal)
                    for stage in STAGES:
                        packet = build(program, start, finish, horizon, terminal, stage)
                        assert evaluate(packet, old.witness) == 0
                        counts['actual_compiler_natural_zero_checks'] += 1
    # Full actual compiler signed counterexample: the transformed systems
    # vanish, while the original is 8.  Natural-domain evaluators reject it.
    packets = [build([(1, 2), (1, 1)], 1, 1, 1, stage=s) for s in STAGES]
    signed = dict(compiler.compile_fractran([(1, 2), (1, 1)], 1, 1, 1).witness)
    signed.update(z_0_1=2, rem_0_1=-1, gap_0_1=2, q_0_1=1, u_0_1=0,
                  h_0_1=-1, x_0_1=2, x_0_2=-1)
    energies = [sum(v * v for v in integer_values(p, signed)) for p in packets]
    assert energies == [8, 0, 0]
    for p in packets:
        try:
            evaluate(p, signed)
        except ValueError:
            counts['signed_semantic_evaluations_rejected'] += 1
        else:
            raise AssertionError('signed witness accepted in natural domain')
    return examples, dict(counts), {'spec': packets[0]['spec'], 'assignment': signed,
                                  'energies_parent_delete_linearize': energies}


def guards():
    count = 0

    def reject(fn):
        nonlocal count
        try:
            fn()
        except (ValueError, TypeError, KeyError):
            count += 1
        else:
            raise AssertionError('invalid caller accepted')

    base = dict(program=[(3, 2), (5, 3)], start=8, finish=125, horizon=6, terminal=False)
    for name, bad in [('program', []), ('program', [(0, 1)]), ('program', [(True, 2)]),
                      ('program', [(1, 0)]), ('program', [(1, 2, 3)]), ('start', True),
                      ('start', 0), ('finish', 0), ('horizon', -1), ('horizon', 1.0),
                      ('terminal', 1)]:
        reject(lambda name=name, bad=bad: build(**dict(base, **{name: bad})))
    reject(lambda: build(**base, stage=True))
    for stage in STAGES:
        packet = build(**base, stage=stage)
        changes = [('variables', packet['variables'][::-1]), ('residuals', packet['residuals'][:-1]),
                   ('domain', 'integers'), ('scope', 'universal'), ('imported_source_file_sha256', 'bad')]
        for key, value in changes:
            for api in (polynomial_source, ledger, checked_packet):
                reject(lambda key=key, value=value, api=api: api(dict(packet, **{key: value})))
        changed = deepcopy(packet)
        changed['residuals'][0][1][0]['coefficient'] += 1
        reject(lambda: checked_packet(changed))
        reject(lambda: evaluate(packet, {v: False for v in packet['variables']}))
    parent = canonical_parent(**base)
    reject(lambda: rewrite(parent, linearize=1))
    reject(lambda: rewrite(build(**base)))
    reject(lambda: rewrite(dict(parent, variables=[])))
    # Equality alone would accept floating coefficients: at N=2**100,
    # rounded subtraction can falsely turn the exact endpoint error 1 into 0.
    for stage in STAGES:
        large = build([(1, 1)], 2**100, 2**100, 0, stage=stage)
        assert evaluate(large, {'n_0': 2**100 + 1}) == 2
        for mode in ('float_constant', 'float_unit', 'bool_unit'):
            altered = deepcopy(large)
            for _, terms in altered['residuals']:
                for term in terms:
                    if mode == 'float_constant' and not term['monomial']:
                        term['coefficient'] = float(term['coefficient'])
                    elif mode == 'float_unit' and term['coefficient'] == 1:
                        term['coefficient'] = 1.0
                    elif mode == 'bool_unit' and term['coefficient'] == 1:
                        term['coefficient'] = True
            for api in (checked_packet, polynomial_source, ledger):
                reject(lambda api=api, altered=altered: api(altered))
            reject(lambda altered=altered: evaluate(altered, {'n_0': 2**100 + 1}))
            if stage == 'parent':
                reject(lambda altered=altered: rewrite(altered))
    return count


def verify():
    examples, checks, signed = audit()
    return {'status': 'PASS_BOUNDED_FRACTRAN_DIVISIBILITY_RESIDUAL_PROJECTION',
            'imported_source_path': str(IMPORTED.relative_to(ROOT)),
            'imported_source_file_sha256': IMPORTED_SHA256,
            'author_source_file_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'domain': 'nonnegative integers, including zero',
            'claim': 'full same-coordinate natural zero-set equality; fixed horizon family',
            'cost_model': 'literal sparse residuals, positive terms first, no cross-row CSE, charged scalar products, literal SOS',
            'per_fraction_step_savings': {'delete': {'M': 4, 'A': 3, 'residuals': 2},
                                        'linearize': {'M': 5, 'A': 4, 'residuals': 2}},
            'examples': examples, 'checks': checks, 'rejected_callers': guards(),
            'full_compiler_signed_counterexample': signed,
            'limitations': 'No integer-domain equivalence, off-zero identity, optimality, or improved fixed-arity universal bound.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2) + '\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(json.dumps({'checks': result['checks'], 'rejected_callers': result['rejected_callers']}))
