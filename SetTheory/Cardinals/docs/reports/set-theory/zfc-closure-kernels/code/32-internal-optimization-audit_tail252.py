"""Independent finite check of the proposed positive-decrement spare-tail variant.

This checks a runtime macro, not blank initialization or a consistency theorem.
Inputs are read from the literal old-label candidate produced by zf_machine.
"""
from pathlib import Path
import json
import random

ROOT = Path(__file__).resolve().parent
rows = {}
for line in (ROOT / 'candidate252_tail_oldlabels.tm').read_text().splitlines():
    if not line or line.startswith('#'):
        continue
    q, b, w, d, target = line.split()
    rows[int(q), int(b)] = (int(w), 1 if d == 'R' else -1, int(target))

def seps(values, mark=None):
    result = []
    for i, value in enumerate(values):
        result.extend([0, int(i != mark)] + [1] * value)
    return result

def support(left, right):
    return {-i - 1 for i, bit in enumerate(left) if bit} | {i for i, bit in enumerate(right) if bit}

def check_macro(values, register, left):
    old_values = list(values)
    tape = support(left, seps(values, mark=register))
    values = list(values)
    values[register] -= 1
    values.append(1)
    expected = support(left, seps(values))
    q, head = 43, 0
    goal = 63 if register == 0 else 48
    bound = 100 + 12 * len(seps(old_values))
    for steps in range(bound + 1):
        if q == goal and head == -1 and tape == expected:
            return steps
        w, direction, q = rows[q, int(head in tape)]
        if w:
            tape.add(head)
        else:
            tape.discard(head)
        head += direction
    raise AssertionError({'values': old_values, 'r': register, 'left': left,
                          'final': (q, head), 'missing': sorted(expected - tape),
                          'extra': sorted(tape - expected)})

def main():
    rng = random.Random(20261016)
    steps = []
    cases = 0
    for r in range(9):
        for v in (1, 2, 5, 17):
            for suffix in ([], [0], [1], [3, 0, 2]):
                values = [0] * 9 + suffix
                values[r] = v
                for left in ([], [0], [1], [1, 0, 1, 1, 0, 1]):
                    steps.append(check_macro(values, r, left))
                    cases += 1
    for _ in range(6000):
        r = rng.randrange(9)
        values = [rng.randrange(20) for _ in range(9 + rng.randrange(8))]
        values[r] = 1 + rng.randrange(30)
        left = [rng.randrange(2) for _ in range(rng.randrange(30))]
        steps.append(check_macro(values, r, left))
        cases += 1
    result = {'claim': 'finite tests of runtime box_decp append-one variant',
              'cases': cases, 'min_steps': min(steps), 'max_steps': max(steps),
              'total_literal_steps': sum(steps),
              'blank_bootstrap_verified': False}
    (Path(__file__).parent / 'tail252_audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
