#!/usr/bin/env python3
"""Static rational identities for Report 64. No next-event or trajectory engine.

The declared tables are proof data. We only subtract rational linear rows,
check affine coefficients, and inspect finite rule syntax. Standard library only.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent

def row(*a):
    return tuple(F(v) for v in a)

def add(a, b):
    return tuple(x + y for x, y in zip(a, b))

def neg(a):
    return tuple(-x for x in a)

def sub(a, b):
    return add(a, neg(b))

def mul(c, a):
    return tuple(F(c) * x for x in a)

def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), F(0))

def right(a, m):
    return tuple(sum((a[i] * m[i][j] for i in range(3)), F(0)) for j in range(3))

def mm(a, b):
    return tuple(right(r, b) for r in a)

def strs(a):
    return [str(v) for v in a]

O = row(0, 0, 0)
D, X, Y = row(1, 0, 0), row(0, 1, 0), row(0, 0, 1)
I = (D, X, Y)
FROW = row(0, '-8/9', '10/9')

# Fields: declared time, messenger position, target position, contact-gap rank.
COMMON = [
    (O, O, X, 0),
    (X, X, X, 1),
    (mul(F(5, 3), X), O, mul(F(2, 3), X), 0),
    (mul(F(19, 9), X), mul(F(4, 9), X), mul(F(4, 9), X), 1),
    (mul(F(35, 9), X), O, mul(4, X), 0),
]
TABLE_Z = COMMON + [
    (row(0, '17/9', '1/2'), row(0, -8, 2), Y, 2),
    (row(0, '11/3', '5/18'), FROW, FROW, 1),
    (row(0, '25/9', '25/18'), O, FROW, 0),
]
TABLE_N = COMMON + [
    (mul(F(53, 9), X), mul(8, X), mul(8, X), 1),
    (mul(F(125, 9), X), O, mul(8, X), 0),
]
VELOCITY_COMMON = [(F(1), F(0)), (F(-3, 2), F(-1, 2)),
                   (F(1), F(-1, 2)), (F(-1, 4), F(2)), (F(4), F(2))]
VELOCITY_Z = VELOCITY_COMMON + [(F(4), F(-1, 2)), (F(-1), F(0))]
VELOCITY_N = VELOCITY_COMMON + [(F(-1), F(0))]
# Positive cone parameters: Z=(y-4x,8x-y,D-y), N=(x,y-8x,D-y).
BASIS_Z = (row(2, 1, 1), row('1/4', '1/4', 0), row(2, 1, 0))
BASIS_N = (row(8, 1, 1), row(1, 0, 0), row(8, 1, 0))
MAP_Z = (D, FROW, Y)
INV_Z = (D, row(0, '-9/8', '5/4'), Y)
MAP_N = (D, mul(8, X), Y)
INV_N = (D, mul(F(1, 8), X), Y)


def certify_word(table, velocities, basis, branch_map, inverse_map):
    assert len(velocities) + 1 == len(table)
    assert mm(branch_map, inverse_map) == I == mm(inverse_map, branch_map)
    gaps_evidence, flight_evidence = [], []
    for n, (t, q, target, contact) in enumerate(table):
        gaps = [q, sub(target, q), sub(Y, target), sub(D, Y)]
        coeffs = [right(g, basis) for g in gaps]
        for j, c in enumerate(coeffs):
            if j == contact:
                assert c == O, (n, j, c)
            else:
                assert all(v >= 0 for v in c) and any(v > 0 for v in c), (n, j, c)
        gaps_evidence.append({'event': n, 'contact_gap': contact,
                              'coefficients': [strs(c) for c in coeffs]})
    for n, (vq, vx) in enumerate(velocities):
        t, q, target, source = table[n]
        tn, qn, xn, destination = table[n + 1]
        dt = sub(tn, t)
        assert sub(qn, q) == mul(vq, dt)
        assert sub(xn, target) == mul(vx, dt)
        coeff = right(dt, basis)
        assert all(v >= 0 for v in coeff) and any(v > 0 for v in coeff)
        gap_v = (vq, vx - vq, -vx, F(0))
        assert gap_v[source] > 0 and gap_v[destination] < 0
        flight_evidence.append({'flight': n + 1, 'duration_row': strs(dt),
                                'positive_cone_coefficients': strs(coeff),
                                'messenger_speed': str(vq), 'target_speed': str(vx)})
    # Exact time-reflected rows: no event prediction and no initial zero-time event.
    T = table[-1][0]
    reverse_table = [(sub(T, t), q, target, contact)
                     for t, q, target, contact in reversed(table)]
    assert reverse_table[0][0] == O and reverse_table[-1][0] == T
    for n in range(len(velocities)):
        vq, vx = velocities[len(velocities) - 1 - n]
        t, q, target, _ = reverse_table[n]
        tn, qn, xn, _ = reverse_table[n + 1]
        dt = sub(tn, t)
        assert sub(qn, q) == mul(-vq, dt)
        assert sub(xn, target) == mul(-vx, dt)
    assert reverse_table[-1][1] == O and reverse_table[-1][2] == X
    return {'events': len(velocities), 'duration': strs(T),
            'nondestructive_duration': strs(mul(2, T)),
            'return': [strs(r) for r in branch_map],
            'inverse': [strs(r) for r in inverse_map],
            'event_gap_certificates': gaps_evidence,
            'flight_certificates': flight_evidence,
            'time_reflection_checked': True}


def range_on_rectangle(linear_rows, xs, ys):
    out = {}
    vertices = [row(1, x, y) for x, y in product(xs, ys)]
    for name, r in linear_rows.items():
        values = [dot(r, p) for p in vertices]
        lo, hi = min(values), max(values)
        assert lo > 0, (name, lo)
        out[name] = {'min': str(lo), 'max': str(hi)}
    return out


result = {'kind': 'static exact rational row certificate',
          'no_simulation': True,
          'Z': certify_word(TABLE_Z, VELOCITY_Z, BASIS_Z, MAP_Z, INV_Z),
          'N': certify_word(TABLE_N, VELOCITY_N, BASIS_N, MAP_N, INV_N)}
assert mul(2, TABLE_Z[-1][0]) == row(0, '50/9', '25/9')
assert mul(2, TABLE_N[-1][0]) == row(0, '250/9', 0)

result['encoding_zero_A'] = range_on_rectangle({
    'x': X, 'y-4x': row(0, -4, 1), '8x-y': row(0, 8, -1),
    'D-y': sub(D, Y), 'post_output_y_gap': mul(F(1, 9), row(0, 8, -1)),
    'test_duration': mul(2, TABLE_Z[-1][0]),
    'test_duration_minus_D': sub(mul(2, TABLE_Z[-1][0]), D),
    '4D_minus_test_duration': sub(mul(4, D), mul(2, TABLE_Z[-1][0])),
}, [F(3, 20)], [F(17, 20), F(19, 20)])
result['encoding_positive_A'] = range_on_rectangle({
    'x': X, 'y-8x': row(0, -8, 1), 'D-y': sub(D, Y),
    'test_duration': mul(2, TABLE_N[-1][0]),
    'test_duration_minus_D': sub(mul(2, TABLE_N[-1][0]), D),
    '4D_minus_test_duration': sub(mul(4, D), mul(2, TABLE_N[-1][0])),
}, [F(1, 20), F(1, 10)], [F(17, 20), F(19, 20)])

# For updates the three coordinates are (D,t,s), using the same row operations.
updates = {}
for name, k, e, bounds, claimed_coefficient in [
    ('increment', F(1, 2), F(1, 40), [F(1, 20), F(3, 20)], F(196, 39)),
    ('positive_decrement', F(2), F(-1, 20), [F(1, 20), F(1, 10)], F(290, 21)),
]:
    first = mul(k, X)
    final = add(first, mul(e, D))
    hidden = mul(1 / (1 - e), first)
    total = add(mul(2 * (1 + k), X),
                add(mul(2, add(first, hidden)), mul(2, D)))
    assert total == add(mul(2, D), mul(claimed_coefficient, X))
    # Both maps fix the interior limit t=D/20.
    assert dot(final, row(1, F(1, 20), F(9, 10))) == F(1, 20)
    evidence = range_on_rectangle({
        'initial_t': X, 'initial_s_minus_t': sub(Y, X), 'D_minus_s': sub(D, Y),
        'scaled_t': first, 's_minus_scaled_t': sub(Y, first),
        'translated_t': final, 's_minus_translated_t': sub(Y, final),
        'hidden_t': hidden, 's_minus_hidden_t': sub(Y, hidden),
        'duration_minus_2D': sub(total, mul(2, D)),
        '4D_minus_duration': sub(mul(4, D), total),
    }, bounds, [F(17, 20), F(19, 20)])
    h = e / (2 - e)
    assert add(hidden, mul(h, sub(sub(mul(2, D), final), hidden))) == final
    evidence['parameters'] = {'k': str(k), 'e': str(e),
                              'scale_target_speed': str((k - 1) / (k + 1)),
                              'translation_target_speed': str(h),
                              'return_row': strs(final), 'duration_row': strs(total)}
    updates[name] = evidence
result['updates'] = updates

# Reflection in R turns (D,x,y) into distances (D,D-y,D-x).
REFLECTION = (D, sub(D, Y), sub(D, X))
assert mm(REFLECTION, REFLECTION) == I
result['right_anchor_reflection'] = [strs(r) for r in REFLECTION]

# Inspect every explicit binary test/reverse rule, including both anchor interfaces.
speeds = {'L': F(0), 'X0': F(0), 'Y': F(0), 'R': F(0),
          'Xpre': F(-1, 2), 'Xfast': F(2), 'Xpost': F(-1, 2),
          'Q0': F(1), 'Q1': F(-3, 2), 'Q2': F(1), 'Q3': F(-1, 4),
          'Q4': F(4), 'CZ': F(-1), 'CN': F(-1)}
rules = [
    (('Q0', 'X0'), ('Q1', 'Xpre')),
    (('Q1', 'L'), ('Q2', 'L')),
    (('Q2', 'Xpre'), ('Q3', 'Xfast')),
    (('Q3', 'L'), ('Q4', 'L')),
    (('Xfast', 'Y'), ('Xpost', 'Y')),
    (('Q4', 'Xpost'), ('CZ', 'X0')),
    (('Q4', 'Xfast'), ('CN', 'X0')),
]
for c in ('Z', 'N'):
    rev = lambda label: 'r' + label + '_' + c
    for label in ('Q0', 'Q1', 'Q2', 'Q3', 'Q4', 'Xpre', 'Xfast', 'Xpost'):
        speeds[rev(label)] = -speeds[label]
    entry = 'rC_' + c
    speeds[entry] = F(1)
    out = 'OUT_' + c
    speeds[out] = F(1)
    rules += [
        (('C' + c, 'L'), (entry, 'L')),
        ((entry, 'X0'), (rev('Q4'), rev('Xpost' if c == 'Z' else 'Xfast'))),
        ((rev('Q4'), 'L'), (rev('Q3'), 'L')),
        ((rev('Q3'), rev('Xfast')), (rev('Q2'), rev('Xpre'))),
        ((rev('Q2'), 'L'), (rev('Q1'), 'L')),
        ((rev('Q1'), rev('Xpre')), (rev('Q0'), 'X0')),
        ((rev('Q0'), 'L'), (out, 'L')),
    ]
    if c == 'Z':
        rules.append(((rev('Xpost'), 'Y'), (rev('Xfast'), 'Y')))
seen = set()
for incoming, outgoing in rules:
    assert len(incoming) == len(set(incoming)) == len(outgoing) == len(set(outgoing)) == 2
    assert len({speeds[label] for label in incoming}) == 2
    assert len({speeds[label] for label in outgoing}) == 2
    key = frozenset(incoming)
    assert key not in seen
    seen.add(key)
result['test_rule_syntax'] = {'explicit_rules': len(rules),
                              'all_binary_distinct_speed_and_unambiguous': True}

magnitudes = {F(1), F(1, 3), F(1, 79), F(1, 41), F(3, 2),
              F(1, 4), F(4), F(1, 2), F(2)}
full_speed_set = {F(0)} | magnitudes | {-v for v in magnitudes}
assert len(full_speed_set) == 19
assert set(speeds.values()) <= full_speed_set
result['common_speed_set'] = strs(sorted(full_speed_set))
result['instruction_event_counts'] = {
    'increment_A': 14, 'increment_B': 3 + 14 + 3,
    'conditional_A_zero': 14, 'conditional_A_positive': 12 + 14,
    'conditional_B_zero': 3 + 14 + 3,
    'conditional_B_positive': 3 + 12 + 14 + 3,
}
assert max(result['instruction_event_counts'].values()) == 32
result['checker_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
out = ROOT / 'evidence' / 'static_checks.json'
out.write_text(json.dumps(result, indent=2) + '\n')
print('PASS: exact word rows, strict chamber coefficients, time reversal, uniform guards, and rule syntax')
print(out)
