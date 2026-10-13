"""JSON CLI for the standalone matrix optimizer (never a knot verdict)."""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
from . import optimize_counts, Limits, transport_circuit


def integer_keys(value, nested=False):
    if type(value) is not dict: raise ValueError('expected a JSON object')
    result = {}
    for key, item in value.items():
        if not key.isdecimal() or str(int(key)) != key:
            raise ValueError('labels must use canonical nonnegative decimal strings')
        result[int(key)] = integer_keys(item) if nested else item
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--max-work', type=int, default=2_000_000)
    parser.add_argument('--max-block-rank', type=int, default=12)
    parser.add_argument('--transport', action='store_true')
    args = parser.parse_args()
    try:
        if args.input.stat().st_size > 32*1024*1024:
            raise ValueError('CLI input exceeds 32 MiB admission limit')
        packet = json.loads(args.input.read_text())
        counts = integer_keys(packet['counts'], nested=True)
        weights = integer_keys(packet['weights']) if 'weights' in packet else None
        allowed = packet.get('allowed')
        result = optimize_counts(counts, weights, allowed=allowed,
                    limits=Limits(max_work=args.max_work,
                                  max_block_rank=args.max_block_rank))
        if args.transport and result['status'] == 'OPTIMAL_MATRIX_PLAN':
            result['transport'] = transport_circuit(counts, result, weights, allowed=allowed)
        print(json.dumps(result, sort_keys=True, indent=2))
        return 0 if result['status'] == 'OPTIMAL_MATRIX_PLAN' else 2
    except (ValueError, KeyError, OSError, TypeError) as exc:
        print(f'input error: {exc}', file=sys.stderr)
        return 1

if __name__ == '__main__': raise SystemExit(main())
