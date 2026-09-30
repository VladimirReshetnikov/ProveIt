"""Exact fixed terminal words for the six-selector Rule110 queue; no compiler claim."""
import argparse
from collections import Counter, deque
import hashlib
import json
from pathlib import Path
import sympy as sp
import native_controller_rule110_selector73 as prior

MARKER_BITS = '01101001101000'  # first displayed bit is read first
MARKER = int(MARKER_BITS[::-1], 2)


def source_check(marker, terminal_c=False, preamble=True):
    assert marker > 0
    parameters = ['q'] + [f'F{i}' for i in range(6)] + ['W', 'x']
    auxiliaries = prior.prior.CORE_NAMES + ['odd_half', 'bound_beta', 'width_beta', 'L']
    z = {name: sp.Symbol(name) for name in parameters + auxiliaries}
    extra = prior.composition_rows(terminal_c, preamble, True)
    if marker == 1:
        extra = [row for row in extra if row[0] != 'six_terminal_scaled']
        extra[-1] = ('six_transport_left', '+', 'six_read', 'q')
    else:
        extra = [tuple(marker if item == 'terminal_queue' else item for item in row)
                 for row in extra]
    schedule = prior.selector_outer() + prior.prior.CORE + prior.prior.BOUND + extra
    env = prior.prior.ternary.execute(schedule, dict(z, n2=z['q']))
    equalities = [('r', 'six_pack_a0'), ('six_q', 'q'), ('s', 'six_odd'),
                  ('bs_X_bound', 'wn2')] + prior.prior.CORE_EQUALITIES
    equalities += [('six_state_b', 'six_target_b'),
                   ('six_lhs_c' if terminal_c else 'F4', 'six_rhs_c'),
                   ('six_transport_left', 'six_transport'),
                   ('six_width_bound', 'W'), ('six_divisor', 'q')]
    polys = prior.prior.independent_sources(z)
    polys[0] = z['r'] - sum(z[f'F{i}'] * z['q']**i for i in range(6))
    polys[1] = sum(z[f'F{i}'] for i in range(6)) + 1 - z['q']
    app = sum(z[f'F{i}'] for i in (1, 2, 3, 4))
    read = sum(z[f'F{i}'] for i in (1, 3, 5))
    initial = 128*z['x'] + 46 if preamble else 2*z['x']
    polys += [z['F2'] + z['F3'] - 2*z['F1'],
              z['F4'] + int(terminal_c)*z['q'] - 2*z['F3'] - z['F5'],
              read + marker*z['q'] - initial - z['W']*app,
              initial + z['width_beta'] - z['W'], z['W']*z['L'] - z['q']]
    u = z['j']*z['c'] - (2*z['r'] + 1)
    correction = polys[11]*(u*u-z['y_aux']**2)
    records = []
    for i, ((left, right), poly) in enumerate(zip(equalities, polys)):
        adjust = correction if i == 12 else 0
        assert sp.expand(env[left]-env[right]-poly-adjust) == 0, i
        records.append(dict(equality=[left, right], source=str(sp.expand(poly)),
                            correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in schedule)
    operations = 73 + int(marker != 1) + int(terminal_c) + int(preamble)
    assert len(schedule) == operations
    assert counts['*'] == 36 + int(marker != 1)
    assert len(equalities) == len(polys) == 19 and len(auxiliaries) == 21
    assert set().union(*(p.free_symbols for p in polys)) == set(z.values())
    return dict(operations=operations, multiplications=counts['*'],
                additions_subtractions=counts['+']+counts['-'], equations=19,
                positive_witnesses_excluding_x=29, parameters=parameters,
                auxiliaries=auxiliaries, initial='128x+46' if preamble else '2x',
                terminal_queue=marker, terminal_state='C' if terminal_c else 'A',
                instructions=[list(row) for row in schedule], sources=records)


def orbit(initial, m):
    width = 1 << m
    assert 0 < initial < width and initial % 2 == 0
    queue, state, mask = initial, 0, 0
    records, labels, seen = [], [], set()
    while (queue, state, mask) not in seen:
        seen.add((queue, state, mask))
        records.append((queue, state, mask))
        append, target, label = prior.TABLE[state, queue % 2]
        labels.append(label)
        queue, state, mask = queue//2 + (width//2)*append, target, mask | (1 << label)
    return records, labels, (queue, state, mask)


def outer_map(x, m, labels, marker, terminal_c=False, preamble=True):
    width, q = 1 << m, 1 << len(labels)
    initial = 128*x + 46 if preamble else 2*x
    queue, state = initial, 0
    for label in labels:
        old, read, append, target = prior.TRANSITIONS[label]
        assert old == state and read == queue % 2
        queue, state = queue//2 + (width//2)*append, target
    fields = prior.words(labels)
    app = sum(fields[i] for i in (1, 2, 3, 4))
    read = sum(fields[i] for i in (1, 3, 5))
    r = sum(value*q**i for i, value in enumerate(fields))
    assert all(fields) and labels[0] == 0 and len(labels) >= m
    assert queue == marker and state == (2 if terminal_c else 0)
    assert read + q*marker == initial + width*app
    assert fields[2] + fields[3] == 2*fields[1]
    assert fields[4] + int(terminal_c)*q == 2*fields[3] + fields[5]
    assert 0 < initial < width and 0 < marker < width
    assert sum(fields) == q-1 and r % 2 == 1 and r.bit_count() == len(labels)
    if preamble: assert labels[:7] == [0, 1, 3, 5, 4, 1, 2]
    return dict(x=x, m=m, W=width, t=len(labels), q=q, fields=list(fields),
                initial=initial, terminal_queue=marker, terminal_state=state,
                read=read, append=app, width_beta=width-initial, L=q//width,
                r=str(r), labels=labels,
                positive_kernel_extension='The reviewed62 selector theorem supplies all remaining positive coordinates.')


def singleton_checks():
    cases = states = 0
    for m in range(8, 13):
        width = 1 << m
        for x in range(1, (width-47)//128 + 1):
            records, labels, repeat = orbit(128*x+46, m)
            empty = any(n == 0 and s == 2 and used == 63 for n, s, used in records)
            for j in range(m):
                singleton = any(n == 1 << j and s == 0 and used == 63
                                for n, s, used in records)
                assert singleton == empty
                cases += 1
            states += len(records)
    # Positivity caveat: the first empty-C visit can precede the first label4.
    records, labels, _ = orbit(10, 4)
    first_empty = next(i for i, (n, s, _) in enumerate(records) if n == 0 and s == 2)
    assert first_empty == 11 and set(labels[:first_empty]) == {0, 1, 2, 3, 5}
    return dict(fixed_width_singleton_comparisons=cases, complete_orbit_states=states,
                preamble_inputs_checked=57,
                positivity_caveat=dict(initial=10, m=4, first_empty=11,
                                      prefix_labels=labels[:first_empty]))


def backward_marker_checks():
    counts = []
    for m in range(MARKER.bit_length(), 31):
        width = 1 << m
        front = {(MARKER, 2)}
        depth = 0
        while front:
            previous = set()
            for queue, state in front:
                for old, read, append, target in prior.TRANSITIONS:
                    if target == state and append == queue//(width//2):
                        previous.add((2*(queue % (width//2))+read, old))
            front = previous
            depth += 1
        assert depth == m-MARKER.bit_length()+2 and depth <= m
        counts.append(dict(m=m, impossible_predecessor_depth=depth))
    assert all(append == 1 for old, read, append, target in prior.TRANSITIONS if target == 1)
    return dict(marker=MARKER, low_first_bits=MARKER_BITS,
                terminal_C_backward_checks=counts,
                terminal_B_bound='W <= 2P, since every transition into B appends1')


def positive_marker():
    records, labels, _ = orbit(128*10+46, 11)
    stop = next(i for i, (n, s, mask) in enumerate(records)
                if n == MARKER and s == 0 and mask == 63)
    assert stop == 87
    return outer_map(10, 11, labels[:stop], MARKER)


def substring_separation():
    x, m, time, offset = 28, 21, 176, 7
    records, labels, repeat = orbit(128*x+46, m)
    queue, state, mask = records[time]
    assert (queue, state, mask) == (183075, 0, 63)
    assert (queue >> offset) % (1 << len(MARKER_BITS)) == MARKER
    assert time >= m and offset+len(MARKER_BITS) <= m
    assert not any(n == MARKER and s == 0 and used == 63 for n, s, used in records)
    assert len(records) == 3529
    positive_map = outer_map(x, m, labels[:time], queue)
    return dict(x=x, m=m, at_time=time, marker_offset=offset,
                complete_orbit_states=len(records), repeated_state=list(repeat),
                positive_prefix=positive_map,
                scope='At this fixed width, an admitted all-label path contains the marker but the entire orbit never reaches the fixed marker word/stateA. No assertion about other widths.')


def verify():
    return dict(status='PASS_EXACT_FIXED_TERMINAL_WORD_COMPONENTS',
                singleton_A74=source_check(1), marker_A75=source_check(MARKER),
                marker_C75_empty=source_check(MARKER, True, False),
                singleton=singleton_checks(), backward=backward_marker_checks(),
                marker_positive_map=positive_marker(), substring=substring_separation(),
                dependency_sha256=hashlib.sha256(Path(prior.__file__).read_bytes()).hexdigest(),
                scope='Exact finite-machine relations and scoped endpoint obstructions; ordinary-input universal compiler and halting correspondence remain open.',
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
    print(json.dumps(dict(status=result['status'], marker=MARKER,
                         ledgers={key:result[key]['operations'] for key in
                                  ('singleton_A74', 'marker_A75', 'marker_C75_empty')},
                         singleton=result['singleton'],
                         substring_orbit_states=result['substring']['complete_orbit_states']), indent=2))
