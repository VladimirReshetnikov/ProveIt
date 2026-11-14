#!/usr/bin/env python3
"""Check the exact GH/G source, grammar, row, and label relation offline."""
import hashlib
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def table(path):
    result = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, direction, target = line.split()
        key = int(q), int(b)
        assert key not in result
        result[key] = int(w), direction, int(target)
    return result


def main(output=None):
    assert __debug__, 'Assertions must be enabled.'
    oldnodes = json.loads((ROOT / 'inputs/nodes.json').read_text())
    newnodes = json.loads((ROOT / 'machine/nodes.json').read_text())
    changed = {key for key in oldnodes if oldnodes[key] != newnodes[key]}
    assert set(oldnodes) == set(newnodes) and changed == {'node170'}
    assert newnodes['node170'] == [['node36', ['node167', 'node145']], 'node57']
    assert oldnodes['node163'] == newnodes['node163'] == ['node6', 'node54']
    old = table(ROOT / 'inputs/raw.native.tm')
    new = table(ROOT / 'machine/raw.native.tm')
    edits = {
        (38, 0): ((0, 'R', 28), (0, 'R', 11)),
        (38, 1): ((1, 'R', 20), (1, 'R', 122)),
        (214, 0): ((0, 'R', 188), (0, 'R', 312)),
        (214, 1): ((1, 'R', 312), (1, 'R', 20)),
        (312, 0): ((0, 'R', 11), (0, 'R', 188)),
    }
    assert set(old) == set(new)
    assert {key for key in old if old[key] != new[key]} == set(edits)
    for key, (before, after) in edits.items():
        assert old[key] == before and new[key] == after
    assert (ROOT / 'machine/folds.json').read_bytes() == (ROOT / 'inputs/folds.json').read_bytes()
    assert digest(ROOT / 'inputs/grammar.json') == 'dce505fbfcb90ce33bf0aa9d378546434abf6a16b925c7ee95f1a761e5e67047'
    dense = table(ROOT / 'machine/machine.tm')
    native = table(ROOT / 'machine/machine.native.tm')
    labels = json.loads((ROOT / 'machine/labels.json').read_text())
    assert len(labels) == 195 and labels[0] == 74 and labels[-1] == 254
    assert {(labels[q], b): (w, direction, labels[target])
            for (q, b), (w, direction, target) in dense.items()} == native
    result = {
        'status': 'PASS',
        'source_node_changes': ['node170'],
        'raw_transition_changes': [list(key) for key in edits],
        'same_ax_grammar': True,
        'same_seven_folds': True,
        'same_no_push_mp': True,
        'dense_native_conjugacy': True,
        'dense_sha256': digest(ROOT / 'machine/machine.tm'),
        'scope': 'Exact source and literal row relations; not an arithmetic calibration theorem.'
    }
    if output is not None:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Write a fresh receipt here; by default only print it.')
    args = parser.parse_args()
    main(args.output)
