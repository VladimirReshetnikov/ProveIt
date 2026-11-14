#!/usr/bin/env python3
"""Bind both delivered U208 tables to their respective portable fold proofs."""
from pathlib import Path
import argparse
import hashlib
import json
from check_local import require, read, census, encode
from portable_fold import roles, construct, verify
from compare import canonical

ROOT = Path(__file__).resolve().parents[1]


def check():
    records = []
    for tag, directory, parent in [
        ('primary', ROOT / 'machine',
         ROOT / 'comparison/U209_ConPA_2026-10-29'),
        ('compatibility', ROOT / 'machine/compatibility_variant',
         ROOT / 'comparison/U209_ConPA_Compatibility_2026-10-29'),
    ]:
        old = read(parent / 'u209.native.tm', 209)
        new = read(directory / 'u208.native.tm', 208)
        info = roles(old)
        require(new == construct(old, info['helper']), 'Variant construction mismatch')
        proof = verify(old, new)
        require((directory / 'sites.json').read_bytes() ==
                (parent / 'sites.json').read_bytes(), 'Variant source changed')
        state_map = json.loads((directory / 'state_map.json').read_text())
        mapping = {int(k): v for k, v in state_map['native_to_dense'].items()}
        require(set(mapping) == {q for q, b in new} | {254},
                'Variant mapping domain')
        require(set(mapping.values()) == set(range(209)) and
                mapping[0] == 0 and mapping[254] == 208, 'Variant mapping range')
        dense = {(mapping[q], b): (w, d, mapping[z])
                 for (q, b), (w, d, z) in new.items()}
        census(dense, 208, 208)
        require(encode(dense) == (directory / 'u208.tm').read_bytes(),
                'Variant dense bytes')
        canonical_rows = canonical(new)[0]
        records.append({
            'variant': tag, 'proof_status': proof['status'],
            'working_states': 208, 'literal_rows': 416,
            'roles': info, 'source_unchanged': True,
            'canonical_sha256': hashlib.sha256(
                json.dumps(canonical_rows, separators=(',', ':')).encode()).hexdigest(),
            'dense_sha256': hashlib.sha256(encode(dense)).hexdigest(),
        })
    require(records[0]['canonical_sha256'] != records[1]['canonical_sha256'],
            'Expected two different rooted graph classes')
    return {'status': 'TWO_U208_VARIANTS_BOUND_AND_NONISOMORPHIC', 'variants': records}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=ROOT / 'build/variants.json')
    args = parser.parse_args()
    result = check()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
