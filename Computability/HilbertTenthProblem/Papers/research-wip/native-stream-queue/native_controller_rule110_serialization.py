"""Exact complete macro-graph checks for two scoped Rule110 candidates."""
import argparse
from collections import deque
from itertools import product
import json
from pathlib import Path

CODE = (3, 1)  # Low-first trits: logical0 -> (0,1), logical1 -> (1,0).
BOOLEAN_WORDS = (0, 1, 3, 4)
RAILS = {word: tuple((a, b) for a, b in product(BOOLEAN_WORDS, repeat=2)
                     if a + b == word) for word in range(9)}
RULE = {(0, 0): (0, 0), (0, 1): (1, 1),
        (1, 0): (1, 0), (1, 1): (1, 2),
        (2, 0): (1, 0), (2, 1): (0, 2)}
LARGE = dict(weights=(-2288, -2280, -12, 228), offset=1539,
             state_codes=(0, 456, 480))
SMALL = dict(weights=(-88, -40, 8, 4), offset=27,
             state_codes=(0, 8, 4))


def micro_path(config, start, read, append):
    weights, h = config['weights'], config['offset']
    carries = [start]
    for j in range(2):
        bits = tuple((value // (3 ** j)) % 3 for value in read + append)
        assert all(bit in (0, 1) for bit in bits)
        numerator = carries[-1] + h + sum(w * bit for w, bit in zip(weights, bits))
        assert numerator % 3 == 0
        carries.append(numerator // 3)
    return carries


def macro_edges(config, carry, coded_outputs):
    weights, h = config['weights'], config['offset']
    outputs = CODE if coded_outputs else range(9)
    rows = []
    for input_bit, output_word in product(range(2), outputs):
        for read, append in product(RAILS[CODE[input_bit]], RAILS[output_word]):
            numerator = carry + 4 * h + sum(w * digit for w, digit in zip(weights, read + append))
            if numerator % 9:
                continue
            target = numerator // 9
            path = micro_path(config, carry, read, append)
            assert path[-1] == target
            rows.append(dict(source=carry, target=target, input_bit=input_bit,
                             output_word=output_word, read_rails=list(read),
                             append_rails=list(append), micro_carries=path))
    return rows


def whole_graph(config, coded_outputs):
    bound = abs(config['offset']) + sum(abs(w) for w in config['weights'])
    # If |c|<=bound, every integral Boolean-label step again has |c|<=bound.
    pending = deque([0])
    reached = {0}
    edges = []
    while pending:
        carry = pending.popleft()
        for row in macro_edges(config, carry, coded_outputs):
            assert all(abs(c) <= bound for c in row['micro_carries'])
            edges.append(row)
            if row['target'] not in reached:
                reached.add(row['target'])
                pending.append(row['target'])
    backward = {carry: set() for carry in reached}
    for row in edges:
        backward[row['target']].add(row['source'])
    coreachable = {0}
    pending = deque([0])
    while pending:
        for source in sorted(backward[pending.popleft()]):
            if source not in coreachable:
                coreachable.add(source)
                pending.append(source)
    trimmed = [row for row in edges
               if row['source'] in coreachable and row['target'] in coreachable]
    return dict(coded_outputs=coded_outputs, invariant_absolute_carry_bound=bound,
                reachable=sorted(reached), coreachable_to_A=sorted(coreachable),
                edges=edges, trimmed_edges=trimmed)


def expected_internal_edges(config):
    states = config['state_codes']
    return {(states[old], states[new], bit, CODE[out])
            for (old, bit), (out, new) in RULE.items()}


def logical_output(bits):
    state = 0
    output = []
    for bit in bits:
        out, state = RULE[state, bit]
        output.append(out)
    return output, state


def large_example():
    coded = whole_graph(LARGE, True)
    all_outputs = whole_graph(LARGE, False)
    assert len(coded['reachable']) == 27 and len(coded['coreachable_to_A']) == 17
    assert len(all_outputs['reachable']) == 88 and len(all_outputs['coreachable_to_A']) == 58
    states = LARGE['state_codes']
    internal = {(row['source'], row['target'], row['input_bit'], row['output_word'])
                for carry in states for row in macro_edges(LARGE, carry, False)
                if row['target'] in states}
    assert internal == expected_internal_edges(LARGE)
    # Every block is a valid coded input/output pair, and the full path returns A.
    rail_pairs = (((0, 1), (0, 1)), ((3, 0), (0, 3)),
                  ((3, 0), (0, 1)), ((3, 0), (3, 0)),
                  ((1, 0), (3, 0)), ((1, 0), (0, 3)),
                  ((3, 0), (0, 1)), ((1, 0), (0, 1)),
                  ((0, 3), (0, 1)))
    carry = 0
    path = []
    bits = []
    output = []
    for read, append in rail_pairs:
        input_bit = CODE.index(sum(read))
        output_bit = CODE.index(sum(append))
        carries = micro_path(LARGE, carry, read, append)
        path.append(dict(source=carry, target=carries[-1], input_bit=input_bit,
                         output_bit=output_bit, read_rails=list(read),
                         append_rails=list(append), micro_carries=carries))
        bits.append(input_bit)
        output.append(output_bit)
        carry = carries[-1]
    expected, final = logical_output(bits)
    assert carry == final == 0 and output != expected
    assert ''.join(map(str, bits)) == '100011010'
    assert ''.join(map(str, output)) == '101000111'
    assert ''.join(map(str, expected)) == '110011111'
    configuration = {key: list(value) if isinstance(value, tuple) else value
                     for key, value in LARGE.items()}
    return dict(configuration=configuration, coded_graph=coded, unrestricted_output_graph=all_outputs,
                exact_three_state_boundary_subgraph=True,
                false_return_A_transduction=dict(input_bits=bits, output_bits=output,
                                                expected_output=expected, path=path),
                scope='Counterexample to the transducer relation; not asserted to satisfy a whole FIFO run')


def small_example():
    coded = whole_graph(SMALL, True)
    all_outputs = whole_graph(SMALL, False)
    assert coded['reachable'] == [-16, 0, 4, 8]
    assert coded['coreachable_to_A'] == [0, 4, 8]
    actual = {(row['source'], row['target'], row['input_bit'], row['output_word'])
              for row in coded['trimmed_edges']}
    assert actual == expected_internal_edges(SMALL)
    assert all_outputs['reachable'] == all_outputs['coreachable_to_A'] == [-16, -12, 0, 4, 8, 12]
    # Input logical0 has trits(0,1), while the output has uncoded trits(2,0).
    read, append = (0, 3), (1, 1)
    path = micro_path(SMALL, 0, read, append)
    assert path == [0, 13, 0]
    assert sum(read) == CODE[0] and sum(append) == 2 and 2 not in CODE
    configuration = {key: list(value) if isinstance(value, tuple) else value
                     for key, value in SMALL.items()}
    return dict(configuration=configuration, coded_graph=coded,
                unrestricted_output_graph=all_outputs,
                exact_coded_return_A_transduction=True,
                uncoded_return_A_counterexample=dict(input_bit=0, output_trits=[2, 0],
                    read_rails=list(read), append_rails=list(append), micro_carries=path),
                scope='Exact Rule110 transducer only conditional on both stream block codes; their typing is unpaid')


def verify():
    return dict(status='PASS_SCOPED_RULE110_SERIALIZATION_AND_ESCAPE_AUDITS',
                code_low_first=[[0, 1], [1, 0]], large_candidate=large_example(),
                small_conditional_candidate=small_example(),
                scope=('Complete finite carry graphs for these two fixed candidates, with valid coded inputs. '
                       'No search completeness for other coefficients/codes, paid code filter, input loader, '
                       'queue row geometry, or universal certificate is asserted.'),
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(json.dumps(dict(status=result['status'],
        large_coded_graph=[len(result['large_candidate']['coded_graph'][key])
                           for key in ('reachable', 'coreachable_to_A')],
        large_unrestricted_output_graph=[len(result['large_candidate']['unrestricted_output_graph'][key])
                                         for key in ('reachable', 'coreachable_to_A')],
        small_coded_graph=[len(result['small_conditional_candidate']['coded_graph'][key])
                           for key in ('reachable', 'coreachable_to_A')],
        small_unrestricted_output_graph=[len(result['small_conditional_candidate']['unrestricted_output_graph'][key])
                                         for key in ('reachable', 'coreachable_to_A')],
        scope=result['scope']), indent=2))
