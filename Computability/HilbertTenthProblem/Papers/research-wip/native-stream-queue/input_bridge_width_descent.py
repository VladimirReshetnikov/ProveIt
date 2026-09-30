"""Exact width-descent invariance after deleting the initial-width bound."""
import argparse
from collections import Counter, deque
from itertools import product
import hashlib
import json
from pathlib import Path
import sympy as sp
import native_dualrail_fifo63 as prior

LABELS = tuple(product((0, 1), repeat=4))  # append0,append1,read0,read1


def deletion_source():
    old = prior.source_check()
    parameters = old['positive_parameters']
    auxiliaries = [name for name in old['positive_auxiliaries'] if name != 'beta']
    z = {name: sp.Symbol(name) for name in parameters + auxiliaries}
    schedule = [row for row in old['instructions'] if row[0] != 'width_bound']
    records = [record for record in old['sources'] if record['equality'] != ['width_bound', 'W']]
    env = prior.selector.execute(schedule, z)
    expressions = []
    for record in records:
        left, right = record['equality']
        source = sp.sympify(record['source'], locals=z)
        correction = sp.sympify(record['correction'], locals=z)
        assert sp.expand(env[left] - env[right] - source - correction) == 0
        expressions.append(source)
    counts = Counter(row[1] for row in schedule)
    assert len(schedule) == 62 and counts['*'] == 33 and counts['+'] + counts['-'] == 29
    assert len(records) == 14 and len(auxiliaries) == 19
    assert set().union(*(value.free_symbols for value in expressions)) == set(z.values())
    smaller = sp.Symbol('smaller_width', positive=True)
    append = z['F0'] + z['F1'] - z['q'] + 1
    substitution = {z['x']: z['x'] + (z['W']-smaller)*append/6,
                    z['W']: smaller, z['L']: z['W']*z['L']/smaller}
    for expression in expressions:
        assert sp.cancel(expression.subs(substitution, simultaneous=True) - expression) == 0
    return dict(operations=62, multiplications=33, additions_subtractions=29,
                equations=14, positive_parameters=parameters, positive_auxiliaries=auxiliaries,
                positive_existentials_excluding_x=25, instructions=schedule, sources=records,
                invariant_under_width_substitution=True,
                scope='Literal deletion source audited; no exact typing or standard FIFO projection is claimed')


def fixture(fields, x, W, q):
    r = prior.prior.base.prior.packed(fields, q)
    A = fields[0] + fields[1] - q + 1
    D = fields[2] + fields[3] - q + 1
    values = dict(x=x, W=W, q=q, r=r, alpha=q-A-D, L=q//W,
                  **{f'F{i}': value for i, value in enumerate(fields)})
    assert q % W == 0 and min(values.values()) > 0
    assert D == 6*x + W*A and r % 2 == 0
    t = 0
    power = 1
    while power < q:
        power *= 3
        t += 1
    assert power == q
    assert all(0 < F < q and prior.prior.base.prior.native(F, t) for F in fields)
    assert fields[0] % 3 == 2 and prior.carry_count(r) == 4*t
    return dict(positive_outer_values=values, append_sum=A, read_sum=D,
                initial=6*x, native_t=t,
                kernel_extension='Retained positive four-field converse; unchanged core coordinates under width descent')


def examples():
    original = fixture((14, 13, 25, 16), 1, 9, 27)
    descended = fixture((14, 13, 25, 16), 2, 3, 27)
    assert original['initial'] < 9 and descended['initial'] > 3
    unit = fixture((14, 13, 17, 16), 1, 1, 27)
    assert unit['read_sum'] % 3 != unit['initial'] % 3
    return dict(original_bounded=original, same_streams_overflow=descended,
                width_one_native=unit,
                scope='Full positive kernel extensions exist; no large auxiliary tuple is materialized')


def transition(state, label, I, W, coefficients, h, bound, age_limit):
    N, carry, addition, age = state
    if age == 0 and label[0] != 1:
        return None
    a, d = sum(label[:2]), sum(label[2:])
    numerator = N + W*a - d
    weighted = carry + h + sum(c*bit for c, bit in zip(coefficients, label))
    if numerator % 3 or weighted % 3:
        return None
    next_N, next_carry = numerator//3, weighted//3
    assert 0 <= next_N <= max(I, W)
    assert -bound <= next_carry <= bound
    return next_N, next_carry, (addition+a+d)//3, min(age+1, age_limit)


def fixed_width_setup(x, W, coefficients, h, cs):
    m, power = 0, 1
    while power < W:
        power *= 3
        m += 1
    assert power == W
    bound = max(abs(cs), (abs(h)+sum(map(abs, coefficients))+1)//2)
    return 6*x, bound, max(1, m)


def fixed_width_decide(x, W, coefficients, h, cs, cf):
    I, bound, age_limit = fixed_width_setup(x, W, coefficients, h, cs)
    start = (I, cs, 0, 0)
    distance = {start: 0}
    queue = deque([start])
    while queue:
        state = queue.popleft()
        if state == (0, cf, 0, age_limit):
            return dict(accepted=True, minimum_length=distance[state], visited=len(distance))
        for label in LABELS:
            next_state = transition(state, label, I, W, coefficients, h, bound, age_limit)
            if next_state is not None and next_state not in distance:
                distance[next_state] = distance[state]+1
                queue.append(next_state)
    return dict(accepted=False, minimum_length=None, visited=len(distance))


def fixed_width_checks():
    systems = [((0, 0, 0, 0), 0, 0, 0),
               ((1, -1, 1, -1), 0, 0, 0),
               ((2, 1, -1, -2), 1, 0, 1)]
    records = []
    word_cases = 0
    for coefficients, h, cs, cf in systems:
        for x, W in product(range(1, 4), (1, 3, 9)):
            I, bound, age_limit = fixed_width_setup(x, W, coefficients, h, cs)
            small_accepted = 0
            for length in range(1, 4):
                q = 3**length
                H = (q-1)//2
                for labels in product(LABELS, repeat=length):
                    words = [sum(label[i]*3**j for j, label in enumerate(labels)) for i in range(4)]
                    A, D = sum(words[:2]), sum(words[2:])
                    arithmetic = (labels[0][0] == 1 and q % W == 0 and
                                  D == I+W*A and A+D < q and
                                  cs+h*H+sum(c*word for c, word in zip(coefficients, words)) == q*cf)
                    state = (I, cs, 0, 0)
                    for label in labels:
                        state = transition(state, label, I, W, coefficients, h, bound, age_limit)
                        if state is None:
                            break
                    accepted = state == (0, cf, 0, age_limit)
                    assert arithmetic == accepted
                    small_accepted += accepted
                    word_cases += 1
            result = fixed_width_decide(x, W, coefficients, h, cs, cf)
            assert bool(small_accepted) == (result['accepted'] and result['minimum_length'] <= 3)
            records.append(dict(coefficients=list(coefficients), h=h, cs=cs, cf=cf,
                                x=x, W=W, accepted_words_through_length3=small_accepted,
                                decision=result))
    return dict(word_arithmetic_vs_state_checks=word_cases, fixed_width_decision_cases=len(records),
                includes_width_one=True, records=records,
                scope='Native branch only; absent typing and the variable-width language are not decided here')


def verify():
    return dict(status='PASS_WIDTH_DESCENT_AND_FIXED_WIDTH_NATIVE_DECISION',
                source62=deletion_source(), examples=examples(), fixed_width=fixed_width_checks(),
                dependency_sha256=hashlib.sha256(Path(prior.__file__).read_bytes().replace(b'\r\n', b'\n')).hexdigest(),
                scope='No label-only recovery of the deleted initial-width bound; native fixed-width decision only',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(json.dumps(dict(status=result['status'],
                         source_operations=result['source62']['operations'],
                         source_equations=result['source62']['equations'],
                         fixed_width_checks=result['fixed_width']['word_arithmetic_vs_state_checks'],
                         decision_cases=result['fixed_width']['fixed_width_decision_cases'],
                         scope=result['scope']), indent=2))
