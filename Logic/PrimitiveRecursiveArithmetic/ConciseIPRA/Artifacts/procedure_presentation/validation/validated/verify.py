"""Offline tests for the two complete, validated procedure checkers.

The subprocess checks include the actual JSON reader and output contract.
The instrumented comparisons also check call states and packet consumption;
they deliberately disregard the changed internal success return value.
"""
import ast
import copy
import hashlib
import json
from pathlib import Path
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PAIRS = [
    ('native', 'checker_native579.py', 'checker_native_procedure.py'),
    ('strict', 'checker_strict606.py', 'checker_strict_procedure.py'),
]


def process(path, certificate, optimized=False):
    result = subprocess.run(
        [sys.executable, *(['-O'] if optimized else []), str(path)],
        input=json.dumps(certificate), text=True, capture_output=True,
        timeout=15,
    )
    return result.returncode == 0 and result.stdout == 'ACCEPT\n'


def kernel(path):
    tree = ast.parse(path.read_text())
    tree.body = [node for node in tree.body
                 if isinstance(node, ast.FunctionDef)
                 or isinstance(node, ast.Assign)
                 and any(isinstance(target, ast.Name) and target.id == 'c'
                         for target in node.targets)]
    namespace = {}
    exec(compile(tree, str(path), 'exec'), namespace)
    return namespace


class StepLimit(Exception):
    pass


def trace(namespace, certificate):
    stack = copy.deepcopy(certificate)
    states, packets = [], []
    function = namespace['c']

    def packet():
        value = stack.pop()
        packets.append(copy.deepcopy(value))
        return value

    def profile(frame, event, _):
        if event == 'call' and frame.f_code is function.__code__:
            if len(states) >= 1000:
                raise StepLimit
            states.append(hashlib.sha256(repr([frame.f_locals[name]
                                         for name in ('g', 'a', 'k', 'v')]).encode()).hexdigest())

    namespace['q'] = packet
    outcome = 'returned'
    try:
        goal = stack.pop()
        sys.setprofile(profile)
        function([], goal, v=1)
    except BaseException as error:
        outcome = type(error).__name__
    finally:
        sys.setprofile(None)
    return {'outcome': outcome, 'states': states, 'packets': packets,
            'remaining': stack}


def main():
    positive = [(p.stem, json.loads(p.read_text()))
                for p in sorted((ROOT / 'fixtures').glob('*.json'))]
    positive.append(('direct_zero', [[0, 0, 1, 1], [[1, 1, 1], 1]]))
    negative = [
        ('false_zero_equals_one', [[0, 0, 1, 1], [1, [1]]]),
        ('wrong_compute_endpoint', [[0, 0, 1, 1], [[1, 1, 1], [1]]]),
        ('future_capture', [[0, 0, 1, 1], [[-1, 1], -1, 1, [3, [1]]], [1, [1]]]),
        ('public_old_zero', [[0, 0, 1, 1], [0, 0]]),
        ('public_even_alias', [[0, 0, 1, 1], [2, 2]]),
        ('public_free_hole', [[0, 0, 1, 1], [3, 3]]),
        ('public_Q', [[0, 0, 1, 1], [[1, 1], [1, 1], [1, 1]]]),
        ('public_empty_term', [[0, 0, 1, 1], [[], []]]),
        ('public_negative_parameter', [[0, 0, 1, 1], [-1, -1]]),
        ('missing_packet', [[1, 1, 1], 1]),
    ]
    for name, data in positive:
        data = copy.deepcopy(data)
        data[-1] = [1, [1]]
        negative.append(('false_goal_mutation_' + name, data))
    results = []
    for category, control, candidate in PAIRS:
        for filename, folder in ((control, 'controls'), (candidate, 'code')):
            for optimized in (False, True):
                for expected, cases in ((True, positive), (False, negative)):
                    for name, data in cases:
                        actual = process(ROOT / folder / filename, data, optimized)
                        results.append(dict(checker=filename, optimized=optimized,
                                            case=name, expected=expected, actual=actual))
                for typ, obj in [('float', 1.0), ('bool', True), ('null', None),
                                 ('string', 'unused'), ('object', {'x': 1})]:
                    data = [obj] + copy.deepcopy(positive[-1][1])
                    expected = category == 'native'
                    actual = process(ROOT / folder / filename, data, optimized)
                    results.append(dict(checker=filename, optimized=optimized,
                                        case='unused_prefix_' + typ,
                                        expected=expected, actual=actual))

    print('Completed subprocess checks:', len(results), flush=True)
    rng = random.Random(20261112)
    values = [0, 1, 2, 3, 4, 5, 6, -1, -2, -3, [], [1], [0, 0],
              [1, 1], [[1, 1]], [1, [1]], [0, 0, 0], 1.0, True, None,
              'x', {'x': 1}]
    trace_inputs = [copy.deepcopy(data) for _, data in positive + negative]
    # Mutate each position of actual instructions as well as the public goal.
    for _, data in positive:
        for _ in range(2):
            mutated = copy.deepcopy(data)
            packet_index = rng.randrange(len(mutated))
            target = mutated[packet_index]
            if isinstance(target, list) and target:
                target[rng.randrange(len(target))] = copy.deepcopy(rng.choice(values))
            else:
                mutated[packet_index] = copy.deepcopy(rng.choice(values))
            trace_inputs.append(mutated)
    comparisons = []
    digests = []
    for category, control, candidate in PAIRS:
        left, right = kernel(ROOT / 'controls' / control), kernel(ROOT / 'code' / candidate)
        states = packets = returned = 0
        for index, data in enumerate(trace_inputs):
            a, b = trace(left, data), trace(right, data)
            same = a == b
            comparisons.append({'category': category, 'case': index, 'equal': same})
            if not same:
                raise AssertionError((category, index, data, a, b))
            states += len(a['states'])
            packets += len(a['packets'])
            returned += a['outcome'] == 'returned'
        digests.append(dict(category=category, comparisons=len(trace_inputs),
                            call_states=states, consumed_packets=packets,
                            returned=returned))
    summary = {
        'python': sys.version,
        'executions': len(results),
        'unexpected': [row for row in results if row['expected'] != row['actual']],
        'trace_summary': digests,
        'trace_comparisons': len(comparisons),
        'trace_input_sha256': hashlib.sha256(json.dumps(trace_inputs).encode()).hexdigest(),
        'results': results,
    }
    (ROOT / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({key: value for key, value in summary.items() if key != 'results'}, indent=2))
    if summary['unexpected']:
        raise SystemExit('Unexpected subprocess outcome')


if __name__ == '__main__':
    main()
