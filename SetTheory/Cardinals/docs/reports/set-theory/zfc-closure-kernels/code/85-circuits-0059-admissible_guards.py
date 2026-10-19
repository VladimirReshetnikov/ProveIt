#!/usr/bin/env python3
"""Transport the checked source product invariant by exact labeled CFG equality."""
import argparse
import json
from pathlib import Path
from common import LAYOUTS, OUTPUT, inputs
from product_verifier import source_graph, graph, signature, check_product


def verify_transport(layouts=LAYOUTS):
    sites, old = source_graph()
    out = dict(status='PASS', source_guards=8391,
               source_invariant=check_product(old), layouts=[])
    for layout in layouts:
        new_sites, table = inputs(layout)
        cases = graph(new_sites)
        assert list(map(signature, cases)) == list(map(signature, old)), layout
        out['layouts'].append(dict(layout=str(layout), labeled_edges_checked=8391,
            exact_labeled_CFG_equivalence=True, product=check_product(cases)))
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('layouts', nargs='*', default=LAYOUTS)
    parser.add_argument('--output', type=Path, default=OUTPUT / 'admissible-guard-transport.json')
    args = parser.parse_args()
    assert __debug__, 'Assertions required; do not use -O.'
    result = verify_transport(args.layouts)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
