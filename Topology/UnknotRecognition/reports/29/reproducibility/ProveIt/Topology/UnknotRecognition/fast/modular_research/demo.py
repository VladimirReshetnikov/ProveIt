#!/usr/bin/env python3
"""Produce and independently replay representative modular observations."""
import argparse
import json
from pathlib import Path
import sys

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))
from fastunknot import Diagram
from fastunknot.modular_shadow import modular_shadow_khovanov_decide
from fastunknot.modular_verify import replay_modular_shadow


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    rows = []
    for name, strands, word in (
        ('trefoil', 2, [1, 1, 1]),
        ('figure_eight', 3, [1, -2] * 2),
        ('torus_3_5', 3, [1, 2] * 5),
        ('unknot', 3, [1, 2]),
    ):
        diagram = Diagram.from_braid(strands, word)
        claim = modular_shadow_khovanov_decide(diagram.pd,
            order=list(range(len(word))), shadow_max_work=None,
            primes=(3, 5, 7, 11, 13))
        replay = (replay_modular_shadow(diagram.pd, claim)
                  if claim['method'] == 'marked-residue-four-modular' else None)
        rows.append(dict(name=name, braid=dict(strands=strands, word=word),
                         pd=diagram.pd, claim=claim, replay=replay))
    result = dict(schema='modular-boundary-demo-v1', cases=rows,
        scope='Positive raw modular claims are replayed by the old integer observer. '
              'The unknot decision comes from final closed rank, not a small modular bound.')
    content = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(content)
    else:
        print(content, end='')


if __name__ == '__main__':
    main()
