#!/usr/bin/env python3
"""Replay the experimental table from a blank tape to a complete safe root.

Uses the same literal table parser and explicit root predicate as fold search;
this finite prefix transports the inherited safe-root theorem, not by itself
the rest of the unbounded simulation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import fold_search246 as fold


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--limit', type=int, default=3000000)
    ap.add_argument('--output', type=Path, default=Path(__file__).with_name('detector8-bootstrap.json'))
    a = ap.parse_args()
    result = fold.bootstrap(fold.T, a.limit)
    result['table_sha256'] = hashlib.sha256(fold.TABLE.read_bytes()).hexdigest()
    result['scope'] = 'Literal finite blank-tape prefix, with complete safe-root predicate checked at the endpoint.'
    if result['outcome'] == 'complete_safe_root_candidate':
        result['logical_values'] = [result['values'][fold.L.PHYSICAL[r]] for r in range(9)]
        result['spare_count'] = len(result['spares'])
    a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('spares', 'ones')}, indent=2))


if __name__ == '__main__':
    main()
