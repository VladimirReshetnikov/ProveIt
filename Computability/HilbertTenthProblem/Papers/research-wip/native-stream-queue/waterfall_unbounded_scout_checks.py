#!/usr/bin/env python3
"""Portable source-pinned replay for the bounded Waterfall algebra scout.

No supplied Python module is imported. This checks the finite row identities
and the same 64 bounded TM prefixes as the original scout. It does not certify
packed field typing, unbounded-history arithmetization, or an operation bound.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

SOURCE_PINS = {
    'source/UniversalTM15x2.twm.txt': '52cfed3f6cba671ed7b166c126288d555ed687b74622ae5a9aaa5bee1345e46a',
    'source/UniversalTM15x2.tm.txt': 'ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae',
    'replay/verify_frontend.py': '951c3482067c6754f23f3ad4cf21e13efe32f51ec9eed599bce02cac6117589d',
    'paper/waterfall-diophantine.tex': '22d6fc7aa755dcd3f6043f1b7472a82f6df2221bc3b21582a9c0fa76372a4e2f',
}
NAMES = (['LeftTape', 'LeftTemp', 'LeftTrans', 'LeftDiv0', 'LeftDiv1',
          'LeftMult', 'LeftWrite0', 'LeftWrite1']
         + [f'Trans{chr(65+q)}{s}' for q in range(15) for s in range(2)]
         + ['RightWrite0', 'RightWrite1', 'RightMult', 'RightDiv0',
            'RightDiv1', 'RightTrans', 'RightTemp', 'RightTape'])
INDEX = {name: i for i, name in enumerate(NAMES)}
HALT = INDEX['TransJ1']


def require(condition, message):
    if not condition:
        raise ValueError(message)


def _canonical(state, symbol, left, right):
    deadlines = [2] * 46
    deadlines[INDEX['LeftTape']] = 2 + 2 * left
    deadlines[INDEX['RightTape']] = 2 + 2 * right
    for direction in ('Left', 'Right'):
        for t in (0, 1):
            deadlines[INDEX[f'{direction}Div{t}']] = 2 + int(t != symbol)
    for q in range(15):
        for t in (0, 1):
            deadlines[INDEX[f'Trans{chr(65+q)}{t}']] = 1 + int(q != state) + int(t != symbol)
    return deadlines


def verify(source_root):
    """Read an extracted waterfall-diophantine directory; write nothing."""
    root = Path(source_root)
    for name, expected in SOURCE_PINS.items():
        actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
        require(actual == expected, 'source hash mismatch: ' + name)
    serialized = json.loads((root / 'source/UniversalTM15x2.twm.txt').read_text())
    rows = [row[1:] for row in serialized[1:]]
    table = (root / 'source/UniversalTM15x2.tm.txt').read_text().splitlines()[0].split('_')
    forms = entries = 0
    for q in range(15):
        for b in (0, 1):
            deadlines = [value + 136 for value in _canonical(q, b, 3, 5)]
            for name in NAMES:
                i = INDEX[name]
                if 8 <= i < 38 and name != f'Trans{chr(65+q)}{b}':
                    continue
                if i == HALT or ('Div' in name and int(name[-1]) != b):
                    continue
                next_q, next_b = q, b
                if 8 <= i < 38:
                    next_q, next_b = ord(table[q][3*b+2]) - 65, 0
                elif 'Div' in name:
                    next_b = 1 - b
                successor = [u + v for u, v in zip(deadlines, rows[i])]
                minimum = min(successor[8:38])
                for u in range(15):
                    for t in (0, 1):
                        expected = minimum + int(u != next_q) + int(t != next_b)
                        require(successor[INDEX[f'Trans{chr(65+u)}{t}']] == expected,
                                'control row identity')
                        entries += 1
                for direction in ('Left', 'Right'):
                    minimum = min(successor[INDEX[direction+'Div0']],
                                  successor[INDEX[direction+'Div1']])
                    for t in (0, 1):
                        require(successor[INDEX[direction+f'Div{t}']] == minimum + int(t != next_b),
                                'division pair row identity')
                        entries += 1
                forms += 1

    # Direct TM prefixes, independent of the Waterfall macrostep frontend.
    # Endpoints need not halt; the final state/head are kept in the shift laws.
    macrosteps = packed = 0
    for left0 in range(8):
        for right0 in range(8):
            q, b, left, right = 0, 0, left0, right0
            trace = []
            for _ in range(24):
                rule = table[q][3*b:3*b+3]
                if rule == '---':
                    break
                write, direction, next_q = int(rule[0]), rule[1], ord(rule[2]) - 65
                d = int(direction == 'L')
                popped, other = (left, right) if d else (right, left)
                quotient, residue = divmod(popped, 2)
                next_left, next_right = ((quotient, 2*other + write) if d
                                         else (2*other + write, quotient))
                require(2*next_left == 4*left - 3*d*left + 2*write - 2*d*write - d*residue,
                        'left macrostep identity')
                require(2*next_right == right + 3*d*right + 2*d*write - residue + d*residue,
                        'right macrostep identity')
                require(6 + 3*quotient + residue + 3*other ==
                        6 + left + right + next_left + next_right - write,
                        'event-count identity')
                trace.append((q, b, left, right, write, d, residue, next_q))
                macrosteps += 1
                q, b, left, right = next_q, residue, next_left, next_right
            k = len(trace)
            bound = max([left, right, left0, right0] +
                        [x for row in trace for x in row[2:4]]) + 1
            base = 32*bound + 64
            power = base**k

            def pack(field):
                return sum(field(row) * base**j for j, row in enumerate(trace))

            h = pack(lambda z: z[2])
            g = pack(lambda z: z[3])
            w = pack(lambda z: z[4])
            u = pack(lambda z: z[6])
            symbol = pack(lambda z: z[1])
            state = pack(lambda z: z[0])
            next_state = pack(lambda z: z[7])
            zl = pack(lambda z: z[5]*z[2])
            zr = pack(lambda z: z[5]*z[3])
            zw = pack(lambda z: z[5]*z[4])
            zu = pack(lambda z: z[5]*z[6])
            require(2*(h - left0 + power*left) == base*(4*h - 3*zl + 2*w - 2*zw - zu),
                    'packed left identity')
            require(2*(g - right0 + power*right) == base*(g + 3*zr + 2*zw - u + zu),
                    'packed right identity')
            require(base*next_state == state + power*q, 'packed state shift')
            require(base*u == symbol + power*b, 'packed head shift')
            packed += 1
    return {
        'status': 'PASS',
        'source_pins': dict(SOURCE_PINS),
        'finite_control_forms': forms,
        'reconstructed_clock_entries': entries,
        'direct_macrosteps': macrosteps,
        'packed_prefixes': packed,
        'scope': 'Scout algebra only; no packed field typing certificate or universal bound.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True,
                        help='extracted waterfall-diophantine directory')
    parser.add_argument('--expect', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.root)
    if args.expect:
        require(result == json.loads(args.expect.read_text()), 'saved receipt mismatch')
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
