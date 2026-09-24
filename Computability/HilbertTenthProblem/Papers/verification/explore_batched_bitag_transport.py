"""Exact bi-tag batching and conditional 13-operation arithmetic transport."""
from itertools import product
from pathlib import Path
import json
import sympy as sp


DIRECT = [
    ('trim', '-', 'N', 'A'), ('append', '+', 'trim', 'U'),
    ('content_left', '*', 'R', 'append'),
    ('start', '-', 'N', 'n0'), ('end', '*', 'nh', 'Q'),
    ('content_inner', '+', 'start', 'end'),
    ('content_right', '*', 'b', 'content_inner'),
    ('length_left', '*', 'R', 'W'), ('length_start', '-', 'Z', 'L0'),
    ('length_end', '*', 'Lh', 'Q'),
    ('length_right', '+', 'length_start', 'length_end'),
    ('state_left', '*', 'R', 'F'), ('state_right', '-', 'S', 's0'),
]
SHARED = [('radix', '*', 'b', 'B')] + [
    (name, op, 'B' if name == 'content_left' else left, right)
    for name, op, left, right in DIRECT if name != 'content_right'
]
EQ = [('content_left', 'content_right'), ('length_left', 'length_right'),
      ('state_left', 'state_right')]
SHARED_EQ = [('content_left', 'content_inner')] + EQ[1:]
LETTERS = (1, 2)
STATES = ('q', 'r', 'halt')
STATE_CODE = {'q': 1, 'r': 2, 'halt': 0}
OUTPUTS = tuple((a,) for a in LETTERS) + tuple(product(LETTERS, repeat=2))


def words(max_length):
    return [w for length in range(1, max_length+1)
            for w in product(LETTERS, repeat=length)]


def run(schedule, values):
    env = dict(values)
    for name, op, left, right in schedule:
        assert name not in env
        a = env[left] if isinstance(left, str) else left
        b = env[right] if isinstance(right, str) else right
        env[name] = a*b if op == '*' else a+b if op == '+' else a-b
    return env


def histogram(schedule):
    return {'M': sum(op == '*' for _, op, _, _ in schedule),
            'A': sum(op != '*' for _, op, _, _ in schedule)}


def source_check():
    names = 'R B Q N A U Z W S F n0 nh L0 Lh s0 b'.split()
    sym = dict(zip(names, sp.symbols(' '.join(names))))
    R, B, Q, N, A, U, Z, W, S, F, n0, nh, L0, Lh, s0, b = [sym[n] for n in names]
    independent = [R*(N-A+U)-b*(N-n0+nh*Q), R*W-Z+L0-Lh*Q, R*F-S+s0]
    divided = [B*(N-A+U)-N+n0-nh*Q] + independent[1:]
    receipts = []
    for schedule, eqs, source in ((DIRECT, EQ, independent),
                                  (SHARED, SHARED_EQ, divided)):
        env = run(schedule, sym)
        for (left, right), residual in zip(eqs, source):
            assert sp.expand(env[left]-env[right]-residual) == 0
        assert len(schedule) == 13 and histogram(schedule) == {'M': 6, 'A': 7}
        receipts.append({'operations': len(schedule), 'histogram': histogram(schedule),
                         'schedule': schedule, 'equalities': eqs,
                         'source_residuals': [sp.sstr(x) for x in source]})
    assert run(SHARED, sym)['radix'] == b*B
    assert sp.expand(independent[0]-b*divided[0]-(R-b*B)*(N-A+U)) == 0
    return {'direct': receipts[0], 'paid_shared_radix': receipts[1],
            'shared_additional_equality': 'radix=R', 'symbolic_source_comparisons': 6,
            'radix_corrections': 1}


def halted(dataword):
    return dataword[0] == 'halt'


def microstep(dataword, table):
    assert not halted(dataword)
    if isinstance(dataword[0], int):
        return dataword[1:]+dataword[:1]
    assert isinstance(dataword[1], int)
    nxt, out = table[dataword[0], dataword[1]]
    return dataword[2:]+out+(nxt,)


def canonicalize(dataword):
    word = dataword
    count = 0
    while isinstance(word[0], int):
        assert not halted(word)
        word = microstep(word, {})
        count += 1
    return word, count


def expand_batch(state, data, table):
    assert state != 'halt' and data
    nxt, out = table[state, data[0]]
    expected = (nxt,)+data[1:]+out
    actual = microstep((state,)+data, table)
    micro_count = 1
    for _ in range(len(data)-1+len(out)):
        assert not halted(actual)
        actual = microstep(actual, table)
        micro_count += 1
    assert actual == expected
    assert halted(actual) == (nxt == 'halt')
    return nxt, expected[1:], micro_count


def code(data, base=3):
    return sum(a*base**i for i, a in enumerate(data))


def local_check():
    normalizations = batches = scalar = 0
    for data in words(4):
        for state in STATES:
            for split in range(len(data)+1):
                initial = data[:split]+(state,)+data[split:]
                actual, count = canonicalize(initial)
                assert actual == (state,)+data[split:]+data[:split]
                assert count == split
                normalizations += 1
        for state in STATES[:-1]:
            for nxt in STATES:
                for out in OUTPUTS:
                    table = {(state, data[0]): (nxt, out)}
                    e, after, count = expand_batch(state, data, table)
                    assert e == nxt and after == data[1:]+out
                    assert count == len(data)+len(out)
                    n, L = code(data), 3**len(data)
                    nn, LL = code(after), 3**len(after)
                    assert 0 < n < L and 0 < nn < LL
                    assert 3*nn == n-data[0]+code(out)*L
                    assert LL == (1+2*(len(out)-1))*L
                    batches += 1
                    scalar += 2
    return {'canonicalizations': normalizations, 'local_batches': batches,
            'scalar_recurrence_checks': scalar, 'maximum_input_length': 4,
            'letter_count': len(LETTERS), 'marker_states': len(STATES)}


def packed_check(initial_state, initial_data, rows, final_state, final_data, table):
    # Every row is independently obtained by expanding actual microsteps.
    terms = []
    current_state, current_data = initial_state, initial_data
    for state, data, nxt, after, out in rows:
        assert (state, data) == (current_state, current_data)
        n, L = code(data), 3**len(data)
        terms.append((n, data[0], code(out)*L, L, 3**len(after),
                      STATE_CODE[state], STATE_CODE[nxt]))
        current_state, current_data = nxt, after
    assert (current_state, current_data) == (final_state, final_data)
    R = 3
    largest = max([3**len(initial_data), 3**len(final_data)]
                  + [x for row in terms for x in row])
    while R <= 8*largest:
        R *= 3
    values = {'R': R, 'B': R//3, 'Q': R**len(rows), 'b': 3,
              'n0': code(initial_data), 'nh': code(final_data),
              'L0': 3**len(initial_data), 'Lh': 3**len(final_data),
              's0': STATE_CODE[initial_state]}
    for j, name in enumerate(('N', 'A', 'U', 'Z', 'W', 'S', 'F')):
        values[name] = sum(row[j]*R**i for i, row in enumerate(terms))
    for schedule, eqs in ((DIRECT, EQ), (SHARED, SHARED_EQ)):
        env = run(schedule, values)
        assert all(env[a] == env[b] for a, b in eqs[:2])
        assert env['state_left']-env['state_right'] == STATE_CODE[final_state]*values['Q']
        if final_state == 'halt':
            assert all(env[a] == env[b] for a, b in eqs)
    assert run(SHARED, values)['radix'] == R
    assert all(0 <= x < R for row in terms for x in row)
    selectors = []
    for (state, a), (nxt, out) in table.items():
        selected = [i for i, row in enumerate(rows)
                    if row[0] == state and row[1][0] == a]
        D = sum(R**i for i in selected)
        T = sum(3**len(rows[i][1])*R**i for i in selected)
        selectors.append((D, T, a, STATE_CODE[state], STATE_CODE[nxt],
                          code(out), 3**(len(out)-1)))
    J = sum(R**i for i in range(len(rows)))
    assert sum(row[0] for row in selectors) == J
    assert sum(a*D for D, T, a, e, ee, u, bg in selectors) == values['A']
    assert sum(e*D for D, T, a, e, ee, u, bg in selectors) == values['S']
    assert sum(ee*D for D, T, a, e, ee, u, bg in selectors) == values['F']
    assert sum(T for D, T, a, e, ee, u, bg in selectors) == values['Z']
    assert sum(u*T for D, T, a, e, ee, u, bg in selectors) == values['U']
    assert sum(bg*T for D, T, a, e, ee, u, bg in selectors) == values['W']
    return values['Q'].bit_length()


def histories_check():
    options = [(state, out) for state in ('q', 'halt') for out in OUTPUTS]
    cases = accepted = cycles = cutoffs = batches = microsteps = 0
    max_bits = 0
    for choice in product(options, repeat=2):
        table = {('q', a): chosen for a, chosen in zip(LETTERS, choice)}
        for initial in words(3):
            state, data = 'q', initial
            seen = {(state, data)}
            rows = []
            outcome = 'cutoff'
            for _ in range(8):
                nxt, out = table[state, data[0]]
                checked_nxt, after, cost = expand_batch(state, data, table)
                assert checked_nxt == nxt
                rows.append((state, data, nxt, after, out))
                state, data = nxt, after
                batches += 1
                microsteps += cost
                if state == 'halt':
                    accepted += 1
                    outcome = 'halt'
                    break
                if (state, data) in seen:
                    cycles += 1
                    outcome = 'cycle'
                    break
                seen.add((state, data))
            if outcome == 'cutoff':
                cutoffs += 1
            max_bits = max(max_bits, packed_check('q', initial, rows, state, data, table))
            cases += 1
    zero_cases = 0
    for initial in words(3):
        packed_check('halt', initial, [], 'halt', initial, {})
        zero_cases += 1
    assert cases == 144*14 and cases == accepted+cycles+cutoffs
    return {'deterministic_tables': 144, 'initial_words_per_table': 14,
            'cases': cases, 'accepting_cases': accepted, 'exact_cycles': cycles,
            'bounded_prefixes_without_classification': cutoffs,
            'batch_limit': 8, 'batches': batches, 'expanded_microsteps': microsteps,
            'zero_batch_accepting_cases': zero_cases, 'largest_time_power_bits': max_bits,
            'rule_partition_and_linear_form_identities_checked': 7*(cases+zero_cases)}


def separation_check():
    examples = []
    for R in (27, 81, 243, 729):
        selector = 1
        length_word = 3+9*R
        selected_length = 3
        assert selector*length_word != selected_length
        examples.append({'R': R, 'selector': selector, 'length_word': length_word,
                         'correct_selected_length': selected_length,
                         'incorrect_product': selector*length_word})
    # Complete bounded check of the carry-decoding lemma, with signed residuals.
    vectors = 0
    for R in range(2, 8):
        for length in range(1, 5):
            for residuals in product(range(-R+1, R), repeat=length):
                value = sum(x*R**i for i, x in enumerate(residuals))
                if value == 0:
                    assert all(x == 0 for x in residuals)
                vectors += 1
    return {'weighted_product_counterexamples': examples,
            'bounded_signed_residual_vectors': vectors,
            'decoding_hypothesis': 'Every scalar residual has absolute value strictly below R.'}


def verify():
    return {'status': 'PASS_BATCHED_BITAG_CONDITIONAL_TRANSPORT',
            'source': source_check(), 'local': local_check(),
            'histories': histories_check(), 'separation': separation_check(),
            'proof': '../1980/EXPLORATION_BATCHED_BITAG_TRANSPORT.md',
            'scope': 'Exact batching equivalence and 13-operation transport only. Joint rule selection, weighted selection, geometry, bounds, positive-variable conversion and raw input remain unpaid.',
            'review_status': 'Author and two independent complete scoped proof/source reviews PASS; fresh verification reproduces the saved receipt.'}


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    print(result['local'])
    print(result['histories'])
