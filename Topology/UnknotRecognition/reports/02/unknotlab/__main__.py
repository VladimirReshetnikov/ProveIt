"""Command line entry point: python -m unknotlab diagram.json."""
from __future__ import annotations
import argparse
import json
import sys
from .recognize import parse_input, recognize


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description='Exact unknot recognizer with an EXPONENTIAL complete backend. '
                    'This is not a quasi-polynomial implementation.')
    parser.add_argument('input', help='JSON diagram filename, or - for standard input')
    methods = parser.add_mutually_exclusive_group()
    methods.add_argument('--force-homology', action='store_true',
                         help='Skip fast certificates; construct the full reduced complex')
    methods.add_argument('--fast-only', action='store_true',
                         help='Return unknown when polynomial-time filters are inconclusive')
    parser.add_argument('--check-d2', action='store_true',
                        help='Additionally verify d^2=0 on every complex generator')
    parser.add_argument('--max-states', type=int,
                        help='Return unknown rather than exceed this number of resolutions')
    parser.add_argument('--max-generators', type=int,
                        help='Return unknown rather than exceed this many chain generators')
    args = parser.parse_args(argv)
    try:
        if args.input == '-':
            data = json.load(sys.stdin)
        else:
            with open(args.input, encoding='utf-8') as stream:
                data = json.load(stream)
        diagram = parse_input(data)
        result = recognize(diagram, force_homology=args.force_homology,
                           fast_only=args.fast_only, check_d_squared=args.check_d2,
                           max_states=args.max_states, max_generators=args.max_generators)
        print(json.dumps(result.as_json(), indent=2, sort_keys=True))
        return 2 if result.status == 'unknown' else 0
    except (ValueError, OSError) as exc:
        print(json.dumps({'status': 'invalid-input', 'error': str(exc)}, indent=2))
        return 3
    except (MemoryError, KeyboardInterrupt) as exc:
        print(json.dumps({'status': 'unknown', 'method': 'interrupted',
                          'reason': type(exc).__name__}, indent=2))
        return 2


if __name__ == '__main__':
    sys.exit(main())
