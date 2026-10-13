"""CLI for a local matrix/graph query, deliberately not a knot recognizer."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys
from .model import from_data
from .solver import solve, solve_pair
from .verify import verify_positive, verify_pair_optimality, verify_negative


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--max-branches', type=int, default=10000)
    parser.add_argument('--max-bytes', type=int, default=5_000_000)
    parser.add_argument('--pair-only', action='store_true')
    parser.add_argument('--no-incumbent', action='store_true')
    args = parser.parse_args(argv)
    scope = 'Fixed unsigned matrix and rooted dual graph only; this is not a topology or knot verdict.'
    try:
        if args.max_bytes < 0:
            raise ValueError('max-bytes must be nonnegative')
        with args.input.open('rb') as stream:
            raw = stream.read(args.max_bytes + 1)
        if len(raw) > args.max_bytes:
            raise ValueError('input exceeds byte limit')
        inst = from_data(json.loads(raw))
        result = solve_pair(inst) if args.pair_only else solve(
            inst, max_branches=args.max_branches, try_incumbent=not args.no_incumbent)
        if result['status'] == 'yes':
            if not verify_positive(inst, result['certificate']):
                raise RuntimeError('independent positive replay failed')
        elif result['status'] == 'no':
            verified = (verify_pair_optimality(inst, result['optimality'])
                        if 'optimality' in result else verify_negative(inst, result['negative_certificate']))
            if not verified:
                raise RuntimeError('independent negative replay failed')
        print(json.dumps(dict(scope=scope, result=result), indent=2))
        return 3 if result['status'] == 'unknown' else 0
    except (OSError, ValueError, TypeError, KeyError, IndexError) as error:
        print(json.dumps(dict(scope=scope, status='invalid-input', error=str(error)), indent=2))
        return 2

if __name__ == '__main__':
    sys.exit(main())
