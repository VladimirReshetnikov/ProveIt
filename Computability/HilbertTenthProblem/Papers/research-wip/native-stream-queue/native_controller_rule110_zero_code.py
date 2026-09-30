"""Conditional Rule110 controller with a zero codeword; no paid code filter."""
import argparse
from collections import deque
from itertools import product
import json
from pathlib import Path
import sympy as sp
import native_controller_rule110_serialization as previous

CODE = (0, 7)
WEIGHTS = (-28, 56, -5, 2)
STATES = (0, 14, 7)
CONFIG = dict(weights=WEIGHTS, offset=0, state_codes=STATES)


def controller_source():
    schedule = [('r110_rd0', '*', 56, 'Fread0'),
                ('r110_rd1', '*', 112, 'Fread1'),
                ('r110_ap0', '*', 10, 'Fappend0'),
                ('r110_ap1', '*', 4, 'Fappend1'),
                ('r110_mask', '*', 25, 'Q'),
                ('r110_left', '+', 'r110_rd1', 'r110_ap1'),
                ('r110_right0', '+', 'r110_rd0', 'r110_ap0'),
                ('r110_right', '+', 'r110_right0', 'r110_mask')]
    env = {name: sp.Symbol(name) for name in ('Fread0', 'Fread1', 'Fappend0', 'Fappend1', 'Q')}
    for target, op, left, right in schedule:
        assert target not in env
        left = env[left] if isinstance(left, str) else left
        right = env[right] if isinstance(right, str) else right
        env[target] = left * right if op == '*' else left + right
    source = -56*env['Fread0']+112*env['Fread1']-10*env['Fappend0']+4*env['Fappend1']-25*env['Q']
    assert sp.expand(env['r110_left']-env['r110_right']-source) == 0
    assert len(schedule) == 8 and sum(row[1] == '*' for row in schedule) == 5
    return dict(operations=8, multiplications=5, additions_subtractions=3,
                instructions=[list(row) for row in schedule],
                equality=['r110_left', 'r110_right'], source=str(sp.expand(source)))


def edges(carry, coded_outputs):
    outputs = CODE if coded_outputs else range(9)
    result = []
    for bit, output in product(range(2), outputs):
        for read, append in product(previous.RAILS[CODE[bit]], previous.RAILS[output]):
            numerator = carry + sum(w * digit for w, digit in zip(WEIGHTS, read + append))
            if numerator % 9:
                continue
            micro = previous.micro_path(CONFIG, carry, read, append)
            assert micro[-1] == numerator // 9
            result.append(dict(source=carry, target=micro[-1], input_bit=bit,
                               output_word=output, read_rails=list(read),
                               append_rails=list(append), micro_carries=micro))
    return result


def graph(coded_outputs):
    bound = sum(abs(w) for w in WEIGHTS)
    reached = {0}
    pending = deque([0])
    rows = []
    while pending:
        carry = pending.popleft()
        for row in edges(carry, coded_outputs):
            assert all(abs(c) <= bound for c in row['micro_carries'])
            rows.append(row)
            if row['target'] not in reached:
                reached.add(row['target'])
                pending.append(row['target'])
    reverse = {c: set() for c in reached}
    for row in rows:
        reverse[row['target']].add(row['source'])
    good = {0}
    pending = deque([0])
    while pending:
        for source in sorted(reverse[pending.popleft()]):
            if source not in good:
                good.add(source)
                pending.append(source)
    return dict(reachable=sorted(reached), returnable=sorted(good), edges=rows,
                invariant_absolute_bound=bound)


def verify():
    coded = graph(True)
    unrestricted = graph(False)
    assert coded['reachable'] == coded['returnable'] == [0, 7, 14]
    actual = {(row['source'], row['target'], row['input_bit'], row['output_word'])
              for row in coded['edges']}
    expected = {(STATES[old], STATES[new], bit, CODE[out])
                for (old, bit), (out, new) in previous.RULE.items()}
    assert actual == expected and len(coded['edges']) == 6
    assert len(unrestricted['reachable']) == 16
    assert unrestricted['reachable'] == unrestricted['returnable']
    # A false transduction through two uncoded outputs, not a full FIFO witness.
    first = previous.micro_path(CONFIG, 0, (0, 0), (4, 1))
    second = previous.micro_path(CONFIG, first[-1], (0, 0), (0, 1))
    assert first == [0, -1, -2] and second == [-2, 0, 0]
    # The A/read1/write1 route can meet the retained first-append-rail bit.
    initial_edge = next(row for row in coded['edges']
                        if row['source'] == 0 and row['input_bit'] == 1)
    assert initial_edge['append_rails'][0] % 3 == 1
    # Doubling all controller constants preserves integral paths bijectively.
    # It gives even coefficient sum and zero initial/terminal carry.
    doubled = tuple(2 * w for w in WEIGHTS)
    assert sum(doubled) == 50
    # With Q=2H and Fi=H+the native rail, this equation is precisely sum(w*rail)=0.
    assert sum(doubled) + 2 * (-25) == 0
    return dict(status='PASS_CONDITIONAL_RULE110_ZERO_CODE_CONTROLLER',
                code_low_first=[[0, 0], [1, 2]], state_codes=list(STATES),
                read_weights=list(WEIGHTS[:2]), append_weights=list(WEIGHTS[2:]),
                offset=0, initial_carry=0, terminal_carry=0,
                coded_graph=coded, unrestricted_output_graph=unrestricted,
                uncoded_zero_input_return=dict(input_blocks=[[0, 0], [0, 0]],
                    output_blocks=[[2, 1], [1, 0]],
                    read_rail_words=[[0, 0], [0, 0]],
                    append_rail_words=[[4, 1], [0, 1]],
                    individual_carries=first + second[1:]),
                source_identity=dict(doubled_weights=list(doubled), width_mask_coefficient=-25,
                    equation='-56*Fread0+112*Fread1-10*Fappend0+4*Fappend1-25*Q=0',
                    literal_audit=controller_source(),
                    scope='Controller identity only; block typing and ordinary input are not compiled'),
                scope=('Exact six-edge relation conditional on both streams using code00/12. '
                       'Zero codeword permits coded zero padding; no code filter, input loader, '
                       'row boundary initialization or complete universal simulation is supplied.'),
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
    print(json.dumps({key: value for key, value in result.items()
                      if key not in ('coded_graph', 'unrestricted_output_graph')}, indent=2))
