#!/usr/bin/env python3
"""Check a JSON certificate, or examine a bounded interval of candidate indices.

This is a reference implementation, not a small Turing machine. A negative
bounded-search result says nothing about consistency or eventual halting.
"""
from __future__ import annotations
import argparse
from dataclasses import asdict
import json
from pathlib import Path
from codec import decode_index, index
from kernel import check


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--file', type=Path, help='JSON certificate to check')
    group.add_argument('--start', type=int, help='first candidate index to examine')
    parser.add_argument('--count', type=int, default=1000,
                        help='finite number of candidates, used with --start')
    args = parser.parse_args()
    if args.file is not None:
        try:
            proof = json.loads(args.file.read_text(encoding='utf-8'))
            result = asdict(check(proof))
            if result['valid']:
                result['candidate_index_hex'] = hex(index(proof))
            print(json.dumps(result, indent=2))
            return 0 if result['valid'] else 1
        except (OSError, ValueError) as exc:
            parser.error(str(exc))
    if args.start < 0 or args.count < 0:
        parser.error('--start and --count must be nonnegative')
    valid = 0
    for n in range(args.start, args.start + args.count):
        try:
            candidate = decode_index(n)
        except ValueError:
            continue
        result = check(candidate)
        valid += result.valid
        if result.refutation:
            print(json.dumps({'refutation': True, 'index_hex': hex(n),
                              'certificate': candidate}, indent=2))
            return 0
    print(json.dumps({'refutation_found_in_interval': False,
                      'start': args.start, 'count': args.count,
                      'valid_certificates': valid,
                      'consistency_conclusion': 'none'}, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
