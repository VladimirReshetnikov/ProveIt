"""Command line: python -m fastunknot recognize FILE [options]."""
from __future__ import annotations
import argparse
import json
import sys

from .diagram import Diagram
from .recognize import recognize
from .scan import ScanLimit, khovanov_rank
from .factor import factored_khovanov_rank
from .jones import bracket_evaluation
from .alexander import alexander_polynomial, format_polynomial
from .verify import verify_result


def read_json(path):
    if path == '-':
        return json.load(sys.stdin)
    with open(path, encoding='utf-8') as stream:
        return json.load(stream)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    rec = sub.add_parser('recognize')
    rec.add_argument('file')
    for name in ('reduction', 'descending', 'alexander', 'jones', 'factor'):
        rec.add_argument('--no-' + name, action='store_true')
    rec.add_argument('--max-objects', type=int)
    rec.add_argument('--jones-max-states', type=int, default=4096)
    rec.add_argument('--seconds', type=float)
    rec.add_argument('--check-d2', action='store_true')
    rec.add_argument('--output')
    kh = sub.add_parser('khovanov')
    kh.add_argument('file')
    kh.add_argument('--no-factor', action='store_true', help='raw optimized scan, for comparisons')
    kh.add_argument('--max-objects', type=int)
    kh.add_argument('--seconds', type=float)
    kh.add_argument('--check-d2', action='store_true')
    jo = sub.add_parser('jones')
    jo.add_argument('file')
    jo.add_argument('--A', type=int, default=2)
    jo.add_argument('--modulus', type=int, default=1_000_000_007)
    jo.add_argument('--max-states', type=int, default=4096)
    jo.add_argument('--seconds', type=float)
    al = sub.add_parser('alexander')
    al.add_argument('file')
    ve = sub.add_parser('verify')
    ve.add_argument('file')
    ve.add_argument('result')
    ve.add_argument('--seconds', type=float)
    args = parser.parse_args(argv)
    try:
        diagram = Diagram.from_json(read_json(args.file))
        code = 0
        if args.command == 'recognize':
            result = recognize(diagram, **{
                'use_' + k: not getattr(args, 'no_' + k)
                for k in ('reduction', 'descending', 'alexander', 'jones', 'factor')},
                max_objects=args.max_objects, jones_max_states=args.jones_max_states,
                seconds=args.seconds, check_d_squared=args.check_d2)
            output = result.to_json()
            code = 3 if result.status == 'UNKNOWN' else 0
        elif args.command == 'khovanov':
            options = dict(max_objects=args.max_objects, seconds=args.seconds,
                           check_d_squared=args.check_d2)
            output = (khovanov_rank(diagram.pd, **options) if args.no_factor else
                      factored_khovanov_rank(diagram, **options))
        elif args.command == 'jones':
            output = bracket_evaluation(diagram, a=args.A, modulus=args.modulus,
                                        max_states=args.max_states, seconds=args.seconds).to_json()
        elif args.command == 'alexander':
            poly = alexander_polynomial(diagram)
            output = {'coefficients': poly, 'polynomial': format_polynomial(poly)}
        else:
            valid = verify_result(diagram, read_json(args.result), seconds=args.seconds)
            output = {'verified': valid}
            code = 0 if valid else 2
        text = json.dumps(output, indent=2, sort_keys=True)
        if getattr(args, 'output', None):
            with open(args.output, 'w', encoding='utf-8') as stream:
                stream.write(text + '\n')
        print(text)
        return code
    except (ScanLimit, MemoryError) as exc:
        print(json.dumps({'status': 'UNKNOWN', 'reason': str(exc) or 'memory allocation failed'}))
        return 3
    except (ValueError, TypeError, OSError) as exc:
        print(f'invalid input: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
