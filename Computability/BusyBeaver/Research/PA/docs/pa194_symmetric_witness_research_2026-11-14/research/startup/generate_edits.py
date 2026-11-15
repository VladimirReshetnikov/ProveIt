#!/usr/bin/env python3
"""Regenerate the frozen edit lists without accessing the source repository."""
from pathlib import Path
from collections import defaultdict
import hashlib
import itertools
import json

BASE = Path(__file__).resolve().parent


def generate(destination):
    destination = Path(destination)
    destination.mkdir(parents=True, exist_ok=True)
    candidates = json.loads((BASE / 'box_source_neutral.json').read_text())
    groups = defaultdict(list)
    for c in candidates:
        groups[tuple(c['row'])].append(c)

    def action(c):
        return list(c['row']) + [c['action'][0], 1 if c['action'][1] else -1, c['action'][2]]

    single = [action(c) for c in candidates]
    (destination / 'single.tsv').write_text(''.join(
        ' '.join(map(str, [i] + e)) + '\n' for i, e in enumerate(single)))

    def write_multi(name, variants):
        with (destination / name).open('w') as f:
            count = 0
            for i, changes in enumerate(variants):
                f.write(' '.join(map(str, [i, len(changes)] + [x for row in changes for x in row])) + '\n')
                count += 1
        return count

    products = itertools.product(*[[None] + group for group in groups.values()])
    combinations = write_multi('combinations.tsv', ([action(c) for c in vs if c] for vs in products))
    source = [tuple(map(int, line.split()[1:]))
              for line in (BASE / 'runtime193_neutral_source.tsv').read_text().splitlines()
              if int(line.split()[1]) >= 0]
    all_edits = sorted(set(source + [tuple(e) for e in single]))
    ray_edits = [e for e in all_edits if e[:2] in [(35, 0), (24, 0), (45, 0), (16, 0)]]
    pairs = sorted(set(tuple(sorted((e, f))) for e in ray_edits for f in all_edits if e[:2] != f[:2]))
    pair_count = write_multi('pairs.tsv', pairs)
    assert (len(single), combinations, pair_count) == (28, 15120, 12167)
    return {'single': len(single), 'combinations': combinations, 'pairs': pair_count}


if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('destination', type=Path)
    print(json.dumps(generate(p.parse_args().destination), indent=2))
