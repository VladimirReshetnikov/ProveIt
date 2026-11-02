#!/usr/bin/env python3
"""Finite radix-window geometry; no all-model or graph-soundness claim."""
import ast
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parents[3]
RECIPE = BASE / 'candidates/free-j-polarized-positive/source/positive/coefficients/recipe'
TABLE = BASE / 'con-zfc-diophantine-forms/36-small-tuple/coefficients/wang943_tiles.json'
PINS = {
    RECIPE / 'build_coefficients.py': 'a003f26c5ef2dc1782e37be2a91abe25e59e5ff39f12bd142f2d6c1d4d8cf82b',
    RECIPE / 'COEFFICIENT_BINDING.json': '0599543212b8d2bbed2db018a29d6826702e1877faa5c8a1861d041998cb1783',
    TABLE: '66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f',
}
L, WIDTH = 8807, 67
RADIX = 1 << WIDTH
TARGETS = (4393, 5495)


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def extract_support(data):
    constants = {}
    for node in ast.parse(data[RECIPE / 'build_coefficients.py'].decode()).body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id in ('WIDTHS', 'OFFSETS', 'ANCHORS'):
                    need(target.id not in constants, 'duplicate recipe constant')
                    constants[target.id] = ast.literal_eval(node.value)
    need(constants == {'WIDTHS': (9, 10, 9, 10), 'OFFSETS': (1023, 1013, 1003, 983),
                       'ANCHORS': (1095, 2195, 3296)}, 'recipe constants')
    binding = json.loads(data[RECIPE / 'COEFFICIENT_BINDING.json'])
    rows = json.loads(data[TABLE])
    need(len(rows) == 943 and rows[1] == [5, 0, 0, 0], 'ordered selector table')
    need((binding['L'], binding['b'], binding['d']) == (L, WIDTH, L * WIDTH), 'radix')
    need(binding['port_widths'] == list(constants['WIDTHS']), 'port widths')
    need(binding['anchors'] == list(constants['ANCHORS']), 'anchors')
    copies = {start + j for start, width in zip(constants['OFFSETS'], constants['WIDTHS'])
              for j in range(width)} | set(constants['ANCHORS'])
    need(len(copies) == 41, 'copy support')
    support = set(range(len(rows))) | copies | {1063, 1064}
    expected = (set(range(943)) | set(range(983, 993)) | set(range(1003, 1012)) |
                set(range(1013, 1032)) | {1063, 1064, 1095, 2195, 3296})
    need(support == expected and len(support) == 986, 'support')
    return support


def cap(i, support):
    if i not in support or i == 1:
        return 0
    return 3 if i == 1063 else 1


def max_rotated_digit(target, shift, fraction, support):
    """Independent maximum over the two contributing source digits."""
    a = cap((target - shift) % L, support)
    b = cap((target - shift - 1) % L, support)
    low = max((x << fraction) % RADIX for x in range(a + 1))
    return low + (b >> (WIDTH - fraction))


def main():
    data = {path: path.read_bytes() for path in PINS}
    for path, expected in PINS.items():
        need(digest(data[path]) == expected, 'input pin ' + str(path))
    support = extract_support(data)

    # This particular word obeys the stated caps.  Rotate its full 590069-bit
    # representation, independently of the local two-digit formula.
    word = (1 << (WIDTH * 2195)) | (1 << (WIDTH * 3296))
    shift = WIDTH * 2198 + 1
    mask = (1 << (WIDTH * L)) - 1
    rotated = ((word << shift) & mask) | (word >> (WIDTH * L - shift))
    digit = lambda k: (rotated >> (WIDTH * k)) & (RADIX - 1)
    need([digit(k) for k in (4392, 4393, 5494, 5495)] == [0, 2, 2, 0],
         'explicit fractional counterexample')
    need(not any(digit(t) == 0 and digit(t - 1) <= 1 for t in TARGETS),
         'incorrectly accepted predecessor bound 1')

    # A more permissive, uniformly safe finite bound: under the explicit caps,
    # one target is identically zero and its predecessor is at most rho/2.
    # Each maximum allows the two source digits to vary independently, so it
    # remains an upper bound regardless of dependencies in an actual word.
    maximum = 0
    worst = None
    for q in range(L):
        for fraction in range(WIDTH):
            candidates = [(max_rotated_digit(t - 1, q, fraction, support), t)
                          for t in TARGETS if max_rotated_digit(t, q, fraction, support) == 0]
            need(candidates, 'no universally clean target at ' + str((q, fraction)))
            value, target = min(candidates)
            if value > maximum:
                maximum, worst = value, (q, fraction, target)
    need(maximum == RADIX // 2 and worst == (2198, 66, 5495), 'sharp half-radix bound')

    for path, expected in PINS.items():
        need(digest(path.read_bytes()) == expected, 'post-check input drift ' + str(path))
    print(json.dumps({'status': 'PASS_COMPACT44_FRACTIONAL_CLEAN_FINITE',
                      'shift_fraction_cases': L * WIDTH, 'support_size': len(support),
                      'witness_rotation_bits': shift, 'witness_digits': [0, 2, 2, 0],
                      'worst_predecessor_bound': maximum, 'worst_case': worst}))


if __name__ == '__main__':
    main()
