"""Literal counterexamples to weakening the primary CTS initialization.

These are finite clockwise/CTS traces, not counterexamples to any frozen
Diophantine compiler or to the separate fixed-halt tag bridge.
"""
import argparse
from collections import deque
import json
from pathlib import Path

import neary_woods_u15_tag_metadata as primary


RULES = {(1, '0'): ('0', 2), (1, '1'): ('1', 3),
         (2, '0'): ('0', 2), (2, '1'): ('1', 2)}


def initial_word(table, tape, counter):
    assert tape and set(tape) <= set('01') and counter >= len(tape)
    z, p = table['z'], table['p']
    result = primary.one(p, 50)
    for bit in tape:
        result += primary.one(p, 1+int(bit))
    for _ in range(counter):
        result += primary.one(z, 0)
    return result


def literal(word):
    assert word.length <= 200000, 'Bounded finite fixtures only.'
    bits = ['0']*word.length
    for j in word.ones:
        bits[j] = '1'
    return ''.join(bits)


def decode_cut(table, word):
    """Decode an exact whole-object cut, including interleaved counters."""
    p, z = table['p'], table['z']
    objects = [(f'S{i}', primary.one(p, 30*i+20)) for i in range(1, 4)]
    objects += [(bit, primary.one(p, 1+int(bit))) for bit in '01']
    objects += [('mu', primary.one(z, 0)), ('slash', primary.one(p, 5)),
                ('prime', primary.one(p, 6))]
    patterns = [(name, literal(obj)) for name, obj in objects]
    bits = literal(word)
    j, result = 0, []
    while j < len(bits):
        found = next(((name, pattern) for name, pattern in patterns
                      if bits.startswith(pattern, j)), None)
        assert found is not None, ('non-object boundary', j)
        name, pattern = found
        result.append(name)
        j += len(pattern)
    return result


def sparse_run(table, tape, counter, event_limit=10000, capture=False):
    """Exact acceleration: skip only zero deletions between successive ones."""
    initial = initial_word(table, tape, counter)
    ones, end = deque(initial.ones), initial.length
    transitions, prefix, cut = [], [], None
    for event in range(event_limit):
        if not ones:
            return dict(status='empty', steps=end, events=event,
                        transitions=transitions[:8], first_state2_cut=cut,
                        prefix_events=prefix)
        position = ones.popleft()
        index = position % table['p']
        family = table['families'].get(index, 'empty_appendant')
        appendant = table['rows'].get(index, primary.Word(0))
        if capture and cut is None:
            prefix.append([position, index, family, appendant.length])
        if family == 'transition':
            transitions.append([position, index])
        if capture and cut is None and index == 80:
            start = position-80
            word = primary.Word(end-start, (80,)+tuple(j-start for j in ones))
            cut = dict(activation_step=position, marker=index,
                       decoded=decode_cut(table, word))
        if index == table['halt']:
            return dict(status='halt_activation', steps=position, events=event,
                        transitions=transitions[:8], first_state2_cut=cut,
                        prefix_events=prefix)
        ones.extend(end+j for j in appendant.ones)
        end += appendant.length
    return dict(status='event_budget', events=event_limit,
                transitions=transitions[:8], first_state2_cut=cut,
                prefix_events=prefix)


def bit_run(table, tape, counter, event_limit):
    """Separate, unaccelerated deletion/append executor for cross-checking."""
    queue = deque(literal(initial_word(table, tape, counter)))
    appendants = {i: literal(w) for i, w in table['rows'].items()}
    steps = events = 0
    transitions = []
    while queue and events < event_limit:
        index = steps % table['p']
        bit = queue.popleft()
        if bit == '1':
            if table['families'].get(index) == 'transition':
                transitions.append([steps, index])
            if index == table['halt']:
                return 'halt_activation', steps, events, transitions[:8]
            queue.extend(appendants.get(index, ''))
            events += 1
        steps += 1
    return ('empty' if not queue else 'event_budget'), steps, events, transitions[:8]


def verify():
    table = primary.cts_table(3, RULES)
    assert (table['z'], table['p'], table['halt']) == (151, 302, 110)
    # Every tested tape starts with zero. The actual clockwise machine enters
    # state2 on its first step, and state2 has only self-copying transitions.
    assert RULES[1, '0'] == ('0', 2)
    assert all(RULES[2, bit] == (bit, 2) for bit in '01')
    examples = {}
    for counter in (2, 3, 4, 8, 16):
        examples[str(counter)] = sparse_run(table, '01', counter, 512, True)
    good, odd, large = (examples[str(c)] for c in (2, 3, 4))
    assert good['status'] == 'event_budget'
    assert good['first_state2_cut'] == dict(activation_step=9140, marker=80,
                                          decoded=['S2', '1', 'mu', 'mu', '0'])
    assert odd['status'] == 'halt_activation' and odd['steps'] == 6150
    assert odd['transitions'][:2] == [[3383, 61], [3686, 62]]
    assert odd['first_state2_cut']['decoded'] == ['S2', '1', 'S3', 'mu', 'mu', '0']
    assert large['status'] == 'empty'
    assert large['first_state2_cut'] == dict(activation_step=18804, marker=80,
        decoded=['S2', '1', 'mu', 'mu', 'mu', '0'])
    assert [17894, 76, 'empty_appendant', 0] in large['prefix_events']
    for counter in (4, 8, 16):
        result = examples[str(counter)]
        assert result['status'] == 'empty'
        assert result['first_state2_cut']['decoded'] == ['S2', '1']+['mu']*(counter-1)+['0']
    cross_checks = []
    for counter, limit in ((2, 128), (3, 128), (4, 256), (8, 256), (16, 512)):
        fast = sparse_run(table, '01', counter, limit)
        status, steps, events, transitions = bit_run(table, '01', counter, limit)
        assert status == fast['status'] and events == fast['events']
        assert transitions == fast['transitions']
        if status != 'event_budget':
            assert steps == fast['steps']
        cross_checks.append(dict(counter=counter, status=status, bit_steps=steps,
                                 one_events=events))
    family = []
    for j in range(7):
        tape, counter = '0'*(1 << j)+'1', 3*(1 << j)
        result = sparse_run(table, tape, counter)
        assert result['status'] == 'halt_activation'
        family.append(dict(j=j, tape_length=len(tape), counter=counter,
                           halt_step=result['steps'], one_events=result['events'],
                           first_two_transitions=result['transitions'][:2]))
    return dict(status='PASS_CLOCKWISE_CTS_COUNTER_INITIALIZATION_OBSTRUCTION',
        clockwise_rules={f'{i}:{bit}': [write, target]
                         for (i, bit), (write, target) in RULES.items()},
        CTS=dict(Q=3, z=151, appendants=302, halt_activation=110),
        examples=examples, independent_bit_executor_checks=cross_checks,
        additional_nondyadic_fixtures=family,
        scope='The printed CTS table does not support arbitrary counters at least '
              'tape length, nor all larger dyadic counters. False designated-halt '
              'activation and malformed/empty CTS traces are certified separately. '
              'No claim about arbitrary counter safe sets, a full tag false zero, '
              'or the frozen universal polynomial is made.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print({c: (r['status'], r.get('steps')) for c, r in result['examples'].items()})
