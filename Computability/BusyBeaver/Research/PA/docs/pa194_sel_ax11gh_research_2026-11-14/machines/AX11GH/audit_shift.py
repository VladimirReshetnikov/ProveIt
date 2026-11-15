#!/usr/bin/env python3
"""Independent literal-source audit of AX11GH Shift and its exact cost.

The all-natural proof is in source_shift_audit.tex. The finite checks here
audit its source indexing and cost formulas; they do not prove PA calibration.
No construction compiler, symbolic arithmetic engine or TM oracle is imported.
"""
import argparse
import hashlib
import json
from pathlib import Path


PREFIX = [
    ['dec', 5, 4, 1], ['dec', 6, 3, 2], ['jump', 0], ['jump', 5],
    ['dec', 6, 10, 5], ['dec', 5, 7, 6], ['jump', 5],
    ['dec', 6, 9, 8], ['jump', 5], ['jump', 11], ['halt'],
    ['dec', 2, 19, 12], ['inc', 7, 13], ['dec', 6, 15, 14],
    ['jump', 18], ['dec', 7, 18, 16], ['inc', 6, 17],
    ['jump', 15], ['jump', 11], ['dec', 7, 22, 20],
    ['inc', 2, 21], ['jump', 19], ['dec', 6, 25, 23],
    ['inc', 5, 24], ['jump', 22]
]
SHIFT = [
    ['dec', 1, 3662, 3661], ['jump', 3660],
    ['dec', 5, 3666, 3663], ['inc', 1, 3664],
    ['inc', 6, 3665], ['jump', 3662],
    ['dec', 6, 3669, 3667], ['inc', 5, 3668],
    ['jump', 3666], ['inc', 6, 3670], ['jump', 0]
]


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def run(instructions, t, h, a, b):
    regs = [91, t, pair(a, b), 0, 73, h, 0, 0, 29]
    pc, count = 3660, 0
    expected = 2 * t + 17 if h == 1 else (
        2 * t + 9 * h + 4 * (a + b) ** 2 + 7 * a + 12 * b + 13)
    while pc not in (10, 25):
        assert count < expected, ('late endpoint', t, h, a, b, pc, regs)
        op = instructions[pc]
        count += 1
        if op[0] == 'inc':
            regs[op[1]] += 1
            pc = op[2]
        elif op[0] == 'dec':
            if regs[op[1]]:
                regs[op[1]] -= 1
                pc = op[3]
            else:
                pc = op[2]
        elif op[0] == 'jump':
            pc = op[1]
        else:
            raise AssertionError(('unexpected operation', pc, op))
    assert count == expected, ('cost', t, h, a, b, count, expected)
    if h == 1:
        assert pc == 10
    else:
        assert pc == 25
        assert regs == [91, h, b, 0, 73, a, 0, 0, 29]
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path,
                        default=Path(__file__).resolve().parent / 'machine/instructions.json')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parent / 'machine/shift_audit.json')
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError('Run with assertions enabled.')
    data = args.source.read_bytes()
    instructions = json.loads(data)
    assert len(instructions) == 3671
    assert instructions[:25] == PREFIX
    assert instructions[3660:] == SHIFT
    counts = [run(instructions, t, h, a, b)
              for t in range(8) for h in range(8)
              for a in range(8) for b in range(8)]
    receipt = {
        'status': 'PASS', 'source_sha256': hashlib.sha256(data).hexdigest(),
        'inspected_blocks': [[0, 24], [3660, 3670]],
        'cases': len(counts), 'exact_cost_checks': len(counts),
        'minimum_instructions': min(counts), 'maximum_instructions': max(counts),
        'halt_entry': 'h=1, at pc10 after 2*t+17 instructions',
        'return': 'h!=1, at pc25 after 2*t+9*h+4*(a+b)^2+7*a+12*b+13 instructions',
        'output': '(C,h,b,0,d,a,0,0,V), input W=p(a,b)',
        'proof': 'source_shift_audit.tex',
        'scope': 'Independent literal-source finite audit supporting an explicit all-natural loop proof; no absolute iPRA/PA calibration.'
    }
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
