"""Command line: python -m fastunknot recognize FILE [options]."""
from __future__ import annotations
import argparse
import json
import sys
from .alexander import alexander_polynomial, format_polynomial
from .diagram import Diagram, DiagramError
from .factor import factorized_khovanov_rank
from .jones import jones_modular, verify_jones_witness
from .recognize import recognize
from .scan import ScanLimit, khovanov_rank


def load(path):
    if path == '-':
        return Diagram.from_json(json.load(sys.stdin))
    with open(path, encoding='utf8') as handle:
        return Diagram.from_json(json.load(handle))


def main(argv=None):
    parser = argparse.ArgumentParser(prog='fastunknot', description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    rec = sub.add_parser('recognize')
    rec.add_argument('file')
    for name in ('reduction', 'descending', 'alexander', 'jones', 'factor'):
        rec.add_argument('--no-' + name, action='store_true')
    rec.add_argument('--seconds', type=float)
    rec.add_argument('--max-objects', type=int)
    rec.add_argument('--check-d2', action='store_true')
    rec.add_argument('--jones-max-states', type=int, default=100_000)
    rec.add_argument('--jones-max-transitions', type=int, default=200_000)
    rec.add_argument('--pivot', choices=('fill', 'lifo'), default='fill')
    rec.add_argument('--output')
    kh = sub.add_parser('khovanov')
    kh.add_argument('file')
    kh.add_argument('--seconds', type=float)
    kh.add_argument('--max-objects', type=int)
    kh.add_argument('--check-d2', action='store_true')
    kh.add_argument('--factor', action='store_true', help='multiply reduced ranks of visible summands')
    kh.add_argument('--pivot', choices=('fill', 'lifo'), default='fill')
    al = sub.add_parser('alexander')
    al.add_argument('file')
    jo = sub.add_parser('jones', help='a modular rejection test, never a complete recognizer')
    jo.add_argument('file')
    jo.add_argument('--modulus', type=int, default=1_000_000_007)
    jo.add_argument('--A', type=int, default=2)
    ve = sub.add_parser('verify-jones', help='recompute a Jones witness on the SAME PD diagram')
    ve.add_argument('file')
    ve.add_argument('witness')
    args = parser.parse_args(argv)
    try:
        diagram = load(args.file)
        code = 0
        if args.command == 'recognize':
            answer = recognize(diagram, use_reduction=not args.no_reduction,
                use_descending=not args.no_descending, use_alexander=not args.no_alexander,
                use_jones=not args.no_jones, use_factorization=not args.no_factor,
                max_objects=args.max_objects, seconds=args.seconds,
                check_d_squared=args.check_d2, jones_max_states=args.jones_max_states,
                jones_max_transitions=args.jones_max_transitions,
                pivot_strategy=args.pivot).to_json()
            code = 3 if answer['status'] == 'UNKNOWN' else 0
        elif args.command == 'khovanov':
            kwargs = dict(max_objects=args.max_objects, seconds=args.seconds,
                          check_d_squared=args.check_d2, pivot_strategy=args.pivot)
            answer = factorized_khovanov_rank(diagram, **kwargs) if args.factor else \
                     khovanov_rank(diagram.pd, **kwargs)
        elif args.command == 'jones':
            answer = jones_modular(diagram, modulus=args.modulus, A=args.A)
        elif args.command == 'verify-jones':
            with open(args.witness, encoding='utf8') as handle:
                witness = json.load(handle)
            answer = {'verified': verify_jones_witness(diagram, witness)}
            code = 0 if answer['verified'] else 2
        else:
            poly = alexander_polynomial(diagram)
            answer = {'alexander_polynomial': format_polynomial(poly), 'coefficients': poly}
        text = json.dumps(answer, indent=2)
        if getattr(args, 'output', None):
            with open(args.output, 'w', encoding='utf8') as handle:
                handle.write(text + '\n')
        print(text)
        return code
    except ScanLimit as exc:
        print(json.dumps({'status': 'UNKNOWN', 'reason': str(exc)}))
        return 3
    except (DiagramError, ValueError, TypeError, OSError, KeyError) as exc:
        print(f'invalid input: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
