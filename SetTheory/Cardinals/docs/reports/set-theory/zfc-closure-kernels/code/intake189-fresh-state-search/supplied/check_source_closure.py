#!/usr/bin/env python3
"""Independently check the exact, closed rho6 parameter-push subtrees.

Standard library only. Reads the pinned K219 ZIP directly; extracts no files.
This checks the structural premise of the ordinary macro-replacement proof.
"""
from pathlib import Path
import argparse
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent.parent
ARCHIVE_HASH = '04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b'
INTERVALS = [(66, 92), (947, 973), (1125, 1151)]
PREFIXES = ['11101001001001', '1110100100111000111001', '111010010011100011111']


def need(value, reason):
    if not value:
        raise ValueError(reason)


def parse(rows):
    lookup = {row[0]: tuple(row[1:]) for row in rows}
    need(len(lookup) == len(rows), 'Repeated primitive path')
    prefixes = {path[:i] for path in lookup for i in range(len(path) + 1)}

    def visit(prefix):
        if prefix in lookup:
            need(prefix + '0' not in prefixes and prefix + '1' not in prefixes,
                 'Primitive path overlaps another primitive')
            return lookup[prefix]
        need(prefix + '0' in prefixes and prefix + '1' in prefixes,
             'Source subtree is not full')
        return visit(prefix + '0'), visit(prefix + '1')

    result = visit('')
    need(list(lookup) == sorted(lookup), 'Primitive ordinal order differs')
    return result


def boundary(node):
    if isinstance(node[0], str):
        op, arg = node
        need(op in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Unknown primitive')
        if op == 'CD': return 1, 0, False
        if op == 'CB': return arg, 0, False
        if op == 'CC': return 0, arg, False
        return 0, 0, op == 'CH'
    left, right = map(boundary, node)
    return max(left[0] - 1, right[0], 0), max(left[1], right[1] - 1, 0), left[2] or right[2]


def exact_subtree(rows, lo, hi, prefix):
    selected = [i for i, row in enumerate(rows) if row[0].startswith(prefix)]
    need(selected == list(range(lo, hi)), 'Interval is not exactly the stated subtree')
    local = [[path[len(prefix):], op, arg] for path, op, arg in rows[lo:hi]]
    tree = parse(local)
    need(boundary(tree) == (0, 0, False), 'Parameter push is not closed')
    return tree, [row[0] for row in local]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    archive = ROOT / 'vendor/K219_Construction_2026-10-20.zip'
    need(hashlib.sha256(archive.read_bytes()).hexdigest() == ARCHIVE_HASH, 'Parent archive hash differs')
    with zipfile.ZipFile(archive) as z:
        raw_old = z.read('K219_Construction_2026-10-20/machine/sites219.json')
    raw_new = (ROOT / 'machines/rho6_219/sites.json').read_bytes()
    old, new = json.loads(raw_old), json.loads(raw_new)
    need(len(old) == len(new) == 4744, 'Source length differs')
    parse(old); parse(new)
    originals = [exact_subtree(old, lo, hi, prefix) for (lo, hi), prefix in zip(INTERVALS, PREFIXES)]
    replacements = [exact_subtree(new, lo, hi, prefix) for (lo, hi), prefix in zip(INTERVALS, PREFIXES)]
    need(all(shape == originals[0][1] for _, shape in originals + replacements),
         'Parameter-push subtrees have different binary shapes')
    need(originals[1][0] == originals[2][0], 'The old c-push subtrees differ')
    need(all(tree == originals[0][0] for tree, _ in replacements),
         'A replacement differs from the complete existing b-push subtree')
    result = {
        'status': 'EXACT_CLOSED_RHO6_SUBTREE_REPLACEMENT_PASS',
        'intervals': [list(x) for x in INTERVALS],
        'prefixes': PREFIXES,
        'boundary': [0, 0, False],
        'leaves_per_subtree': 26,
        'equal_relative_binary_shapes': True,
        'new_subtrees_equal_original_b_push': True,
        'parent_archive_sha256': ARCHIVE_HASH,
        'old_source_sha256': hashlib.sha256(raw_old).hexdigest(),
        'new_source_sha256': hashlib.sha256(raw_new).hexdigest(),
        'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope': 'Exact syntax, whole-subtree intervals, and escaping-control bounds; ordinary macro/calculus proof is in the report.'
    }
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
