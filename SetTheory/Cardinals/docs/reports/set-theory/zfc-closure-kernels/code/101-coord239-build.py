#!/usr/bin/env python3
"""Rebuild both exact machine tables from the pinned 240-state input."""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'verification'))
from verify_construction import construct, serialize


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', type=Path, default=ROOT / 'rebuilt')
    a = p.parse_args()
    if not __debug__:
        raise SystemExit('Assertions must be enabled; omit -O.')
    _, old_labels, canonical, ren = construct()
    a.out.mkdir(parents=True, exist_ok=True)
    (a.out / 'zfc239_old.tm').write_bytes(serialize(old_labels, 95))
    (a.out / 'zfc239.tm').write_bytes(serialize(canonical, 0))
    (a.out / 'renumbering.json').write_text(json.dumps({
        'old_to_canonical': ren,
        'canonical_to_old': {v: k for k, v in ren.items()}
    }, indent=2) + '\n')
    print('Rebuilt 239 working states and 478 transitions in', a.out)


if __name__ == '__main__':
    main()
