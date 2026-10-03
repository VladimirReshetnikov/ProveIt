"""Exact reachable-control bisimulation quotients of the U9/U15 binary tables.

The quotient preserves every circular tape step, including halting. This
packet computes machine/CTS/tag metadata, not a universal polynomial cost.
"""
import argparse
from collections import Counter, deque
import hashlib
import json
from pathlib import Path
import random

import neary_woods_u9_tag_metadata as u9
import neary_woods_u15_tag_metadata as u15


def quotient(binary):
    """Minimize a finite total binary transducer, distinguishing its halt.

    Inputs use the emitted compiler format: transitions[(state, bit)] is
    (one_or_two_bit_word, target). The distinct initial and halt states
    must both be graph reachable. Arbitrary nonempty circular bit tapes
    are allowed; no valid-block invariant is used by the quotient.
    """
    delta = binary['transitions']
    start, halt = binary['start'], binary['halt']
    states = {q for q, _ in delta} | {halt}
    assert start in states and start != halt
    assert set(delta) == {(q, b) for q in states - {halt} for b in '01'}
    assert len({repr(q) for q in states}) == len(states)
    for (q, bit), (word, target) in delta.items():
        assert isinstance(word, str) and len(word) in (1, 2)
        assert set(word) <= set('01') and target in states

    reachable = {start}
    queue = deque([start])
    while queue:
        q = queue.popleft()
        if q == halt:
            continue
        for bit in '01':
            target = delta[q, bit][1]
            if target not in reachable:
                reachable.add(target)
                queue.append(target)
    assert halt in reachable, 'This interface retains a graph-reachable distinguished halt.'
    ordered = sorted(reachable, key=repr)
    parts = {q: int(q == halt) for q in ordered}
    history = [len(set(parts.values()))]
    while True:
        signatures, new = {}, {}
        for q in ordered:
            signature = (('HALT',) if q == halt else
                         tuple((delta[q, bit][0], parts[delta[q, bit][1]]) for bit in '01'))
            if signature not in signatures:
                signatures[signature] = len(signatures)
            new[q] = signatures[signature]
        # The successive equivalences refine one another. Check this without
        # relying on coincidental equality of arbitrary integer class names.
        previous = {}
        for q in ordered:
            assert new[q] not in previous or previous[new[q]] == parts[q]
            previous[new[q]] = parts[q]
        history.append(len(signatures))
        stable = len(signatures) == history[-2]
        parts = new
        if stable:
            break

    classes = {}
    for q in ordered:
        classes.setdefault(parts[q], []).append(q)
    first, last = parts[start], parts[halt]
    assert first != last and classes[last] == [halt]
    class_order = [first] + sorted(set(classes) - {first, last}) + [last]
    labels = {c: i + 1 for i, c in enumerate(class_order)}
    mapping = {q: labels[parts[q]] for q in ordered}
    Q = len(classes)
    assert mapping[start] == 1 and mapping[halt] == Q

    rules = {}
    for q in ordered:
        if q == halt:
            continue
        for bit in '01':
            word, target = delta[q, bit]
            key, row = (mapping[q], bit), (word, mapping[target])
            assert key not in rules or rules[key] == row
            rules[key] = row
    assert set(rules) == {(q, b) for q in range(1, Q) for b in '01'}
    # Every quotient state remains reachable, and every reachable original
    # transition has the identical output word and the mapped target.
    seen, todo = {1}, [1]
    while todo:
        q = todo.pop()
        if q == Q:
            continue
        for bit in '01':
            target = rules[q, bit][1]
            if target not in seen:
                seen.add(target)
                todo.append(target)
    assert seen == set(range(1, Q + 1))
    for (q, bit), (word, target) in delta.items():
        if q in mapping:
            assert rules[mapping[q], bit] == (word, mapping[target])
    return dict(start=1, halt=Q, transitions=rules, mapping=mapping,
                unreachable=tuple(sorted(states-reachable, key=repr)),
                original_states=len(states), reachable_states=len(reachable),
                quotient_states=Q, refinement_class_counts=history,
                class_size_histogram=dict(sorted(Counter(map(len, classes.values())).items())))


def build(machine='u9'):
    assert machine in ('u9', 'u15')
    module, cells = (u9, 64) if machine == 'u9' else (u15, 128)
    ordinary, binary, _ = getattr(module, 'compiled_' + machine)()
    result = quotient(binary)
    table = u15.cts_table(result['halt'], result['transitions'])
    summary = u15.row_summary(table)
    counts = u15.track_counts(table['p'], table['total_length'], summary['maximum'])
    D = 2*cells*table['z']*counts['bit_block_length']
    result.update(machine=machine, ordinary=ordinary, original_binary=binary,
                  cts_table=table, cts_summary=summary, tag_counts=counts,
                  data_physical_bit_width=cells, initial_counter_coefficient=2*cells,
                  data_binary_width=D)
    return result


def trace_checks(packet, seed):
    rng = random.Random(seed)
    old = packet['original_binary']
    delta, rules = old['transitions'], packet['transitions']
    mapping, halt = packet['mapping'], packet['halt']
    reachable = list(mapping)
    steps = ended = 0
    for case in range(768):
        state = old['start'] if case < 256 else rng.choice(reachable)
        q = mapping[state]
        tape = ''.join(rng.choice('01') for _ in range(rng.randrange(1, 65)))
        original, changed = deque(tape), tape
        for _ in range(384):
            assert (state == old['halt']) == (q == halt)
            assert mapping[state] == q and ''.join(original) == changed
            if state == old['halt']:
                ended += 1
                break
            bit = original.popleft()
            written, state = delta[state, bit]
            original.extend(written)
            rewritten, q = rules[q, changed[0]]
            changed = changed[1:] + rewritten
            assert written == rewritten
            steps += 1

    # Do not rely on the random traces to sample acceptance. Exhaust all
    # reachable transitions entering halt, each with five different tails.
    terminal = 0
    for (state, bit), (word, target) in delta.items():
        if state in mapping and target == old['halt']:
            for tail in ('', '0', '1', '01', '101'):
                output, target_class = rules[mapping[state], bit]
                assert output == word and target_class == halt
                assert tail + word == tail + output
                terminal += 1
    assert terminal > 0 and mapping[old['halt']] == halt
    return dict(circular_trace_cases=768, circular_steps=steps,
                halted_random_traces=ended, immediate_halt_tape_cases=terminal,
                distinguished_halt_case=True)


def machine_record(packet):
    binary = packet['original_binary']
    delta, mapping, rules = binary['transitions'], packet['mapping'], packet['transitions']
    wire = [[q, b, w, target] for (q, b), (w, target) in sorted(rules.items())]
    # Compact, complete encodings: each key is state:read and each value is
    # written_word:target. No original state is identified merely by a hash.
    rule_encoding = {f'{q}:{b}': f'{w}:{target}' for q, b, w, target in wire}
    restored = {tuple((int(k.split(':')[0]), k.split(':')[1])):
                (v.split(':')[0], int(v.split(':')[1])) for k, v in rule_encoding.items()}
    assert restored == rules
    D = packet['data_binary_width']
    return dict(machine=packet['machine'],
                original_states=packet['original_states'],
                reachable_states=packet['reachable_states'],
                quotient_states=packet['quotient_states'],
                removed_unreachable_states=len(packet['unreachable']),
                merged_reachable_states=packet['reachable_states']-packet['quotient_states'],
                reachable_two_cell_instructions=sum(len(w) == 2 for (q, b), (w, t) in delta.items() if q in mapping),
                quotient_two_cell_instructions=packet['cts_table']['T2'],
                exact_original_row_checks=2*(packet['reachable_states']-1),
                refinement_class_counts=packet['refinement_class_counts'],
                class_size_histogram=packet['class_size_histogram'],
                start=1, halt=packet['halt'],
                quotient_sha256=hashlib.sha256(json.dumps(wire, separators=(',', ':')).encode()).hexdigest(),
                cts={**{k: packet['cts_table'][k] for k in ('Q', 'z', 'p', 'halt', 'T2')},
                     **packet['cts_summary']}, tag_counts=packet['tag_counts'],
                data_physical_bit_width=packet['data_physical_bit_width'],
                initial_counter_coefficient=packet['initial_counter_coefficient'],
                data_binary_width=D, width_bit_length=D.bit_length(), width_population=D.bit_count(),
                binary_power_chain_multiplications=D.bit_length()+D.bit_count()-2,
                trace_checks=trace_checks(packet, 19681611 if packet['machine'] == 'u9' else 30892575),
                quotient_rules=rule_encoding,
                original_state_to_quotient={repr(q): c for q, c in mapping.items()},
                removed_original_states=[repr(q) for q in packet['unreachable']])


def verify():
    records = [machine_record(build(name)) for name in ('u9', 'u15')]
    assert [(r['original_states'], r['reachable_states'], r['quotient_states'],
             r['quotient_two_cell_instructions']) for r in records] == [
                 (1968, 1814, 1611, 64), (3089, 2895, 2575, 118)]
    assert [r['data_binary_width'] for r in records] == [
        17644409035916092600397268366080,
        367306347065639997480389946211840]
    return dict(status='PASS_BINARY_CLOCKWISE_CONTROL_QUOTIENT', machines=records,
                scope='Exact reachable-control bisimulation quotient; same complete '
                      'circular tape/head trajectory and halting event. Actual CTS/tag '
                      'metadata and original frame contracts retained. No minimum '
                      'clockwise machine, optimal exponent chain, composed universal '
                      'polynomial operation count, expanded tag production or native Pell zero.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2) + '\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    for row in result['machines']:
        print({k: row[k] for k in ('machine', 'original_states', 'reachable_states',
               'quotient_states', 'quotient_two_cell_instructions', 'data_binary_width')})
