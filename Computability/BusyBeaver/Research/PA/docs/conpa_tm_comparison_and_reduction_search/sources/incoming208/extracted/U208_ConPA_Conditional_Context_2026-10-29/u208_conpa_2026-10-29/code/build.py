#!/usr/bin/env python3
"""Deterministic two-row construction. No optimizer, search, or network."""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
PINS = {
    'primary': ('d0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16',
                'b348a466a2c316511e0037ea3824de29d4c6ad37338404fbc98a3968fdb25135',
                'a2fee9e41311c0d43aaac871ea411be24eada17e6b3633c55f40b437101144e1'),
    'alternative': ('4564c4876f9b18725bfb3505ec1f50d1ebce572502f2c6381ad673ecfdc3c3e1',
                    '5f936da0cf393548cdd1eeebcaf7490d7a42f4ccca115f865a7bcc045463eb52',
                    '9865dcd7bd44deece098c16dcec7b90a96cf111592cbd37e3531b50f7b09276c'),
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encode(table):
    return ('#! start 0\n' + ''.join(
        f'{q} {b} {w} {d} {z}\n'
        for (q, b), (w, d, z) in sorted(table.items()))).encode('ascii')


def build(out, alternative=False):
    family = 'alternative' if alternative else 'primary'
    parent = ROOT / ('alternative/parent209.native.tm' if alternative
                     else 'machine_parent/u209.native.tm')
    raw = parent.read_bytes()
    need(sha(raw) == PINS[family][0], 'Frozen parent changed')
    table = {}
    for line in raw.decode('ascii').splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        key = int(q), int(b)
        need(key not in table, 'Duplicate row')
        table[key] = int(w), d, int(z)
    helper = 214 if alternative else 217
    need(table[116, 0] == (0, 'R', 172), 'Incoming redirect precondition')
    need(table[211, 0] == (0, 'R', 157), 'Selector precondition')
    new = {(q, b): (w, d, 211 if z == 172 else z)
           for (q, b), (w, d, z) in table.items() if q != 172}
    new[211, 0] = 0, 'L', helper
    states = sorted({q for q, b in new})
    need(len(states) == 208 and len(new) == 416, 'State count')
    mapping = {q: i for i, q in enumerate(states)}
    mapping[254] = 208
    dense = {(mapping[q], b): (w, d, mapping[z])
             for (q, b), (w, d, z) in new.items()}
    native_raw, dense_raw = encode(new), encode(dense)
    need(sha(native_raw) == PINS[family][1], 'Native reconstruction changed')
    need(sha(dense_raw) == PINS[family][2], 'Dense reconstruction changed')
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    (out / 'u208.native.tm').write_bytes(native_raw)
    (out / 'u208.tm').write_bytes(dense_raw)
    (out / 'state_map.json').write_text(json.dumps(mapping, indent=2) + '\n')
    print(f'EXACT_BUILD_PASS: {family}, 208 working states, 416 rows')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--alternative', action='store_true')
    args = parser.parse_args()
    build(args.output, args.alternative)
