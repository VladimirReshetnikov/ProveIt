"""Command line: python -m fastunknot recognize FILE [options]."""
from __future__ import annotations
import argparse
import json
import sys
from .alexander import alexander_polynomial, format_polynomial
from .diagram import Diagram, DiagramError
from .jones import jones_obstruction, verify_obstruction, FilterLimit
from .recognize import recognize
from .scan import ScanLimit, khovanov_rank

EXIT = {'UNKNOT': 0, 'KNOTTED': 0, 'UNKNOWN': 3}


def load(path):
    if path == '-':
        return Diagram.from_json(json.load(sys.stdin))
    with open(path, encoding='utf-8') as handle:
        return Diagram.from_json(json.load(handle))


def main(argv=None):
    parser = argparse.ArgumentParser(prog='fastunknot', description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    rec = sub.add_parser('recognize', help='exact unknot recognition')
    rec.add_argument('file')
    for flag in ('reduction', 'descending', 'alexander', 'jones', 'modular', 'factor'):
        rec.add_argument('--no-' + flag, action='store_true')
    rec.add_argument('--jones-states', type=int, default=2048)
    rec.add_argument('--output')
    kh = sub.add_parser('khovanov', help='exact total F2 Khovanov ranks')
    kh.add_argument('file')
    kh.add_argument('--no-factor', action='store_true')
    kh.add_argument('--order', help='JSON array of crossing indices, for exact replay')
    for cmd in (rec, kh):
        cmd.add_argument('--max-objects', type=int)
        cmd.add_argument('--seconds', type=float, help='cooperative time budget')
        cmd.add_argument('--check-d2', action='store_true')
        cmd.add_argument('--pivot', choices=['markowitz', 'lifo'], default='markowitz')
    al = sub.add_parser('alexander', help='full Alexander polynomial')
    al.add_argument('file')
    jo = sub.add_parser('jones', help='exact finite-field Jones evaluation (not a complete test)')
    jo.add_argument('file')
    jo.add_argument('--max-states', type=int, default=2048)
    ve = sub.add_parser('verify-jones', help='recompute a Jones obstruction witness')
    ve.add_argument('file')
    ve.add_argument('witness')
    args = parser.parse_args(argv)
    try:
        diagram = load(args.file)
        if args.command == 'recognize':
            result = recognize(diagram, use_reduction=not args.no_reduction,
                use_descending=not args.no_descending, use_alexander=not args.no_alexander,
                use_jones=not args.no_jones, use_modular=not args.no_modular,
                use_factorization=not args.no_factor, jones_max_states=args.jones_states,
                max_objects=args.max_objects, seconds=args.seconds,
                check_d_squared=args.check_d2, pivot=args.pivot).to_json()
            text = json.dumps(result, indent=2)
            if args.output:
                with open(args.output, 'w', encoding='utf-8') as handle:
                    handle.write(text + '\n')
            print(text)
            return EXIT[result['status']]
        if args.command == 'khovanov':
            order = None if args.order is None else json.loads(args.order)
            result = khovanov_rank(diagram.pd, order=order, max_objects=args.max_objects,
                seconds=args.seconds, check_d_squared=args.check_d2,
                pivot=args.pivot, factor=not args.no_factor)
        elif args.command == 'jones':
            result = jones_obstruction(diagram, max_states=args.max_states)
        elif args.command == 'verify-jones':
            with open(args.witness, encoding='utf-8') as handle:
                witness = json.load(handle)
            # Accept a standalone witness, or the whole recognizer output.
            if 'evidence' in witness:
                evidence = witness['evidence']
                if ('jones_diagram' in evidence
                        and diagram.to_json() != evidence['jones_diagram']):
                    from .simplify import simplify
                    reduced, _ = simplify(diagram)
                    if reduced.to_json() != evidence['jones_diagram']:
                        raise ValueError('reduced witness diagram does not match the input')
                    diagram = reduced
                witness = evidence.get('jones', {})
            verified = verify_obstruction(diagram, witness)
            print(json.dumps({'verified': verified, 'status': 'KNOTTED' if verified else 'UNVERIFIED'}))
            return 0 if verified else 2
        else:
            poly = alexander_polynomial(diagram)
            result = {'alexander_polynomial': format_polynomial(poly), 'coefficients': poly}
        print(json.dumps(result, indent=2))
        return 0
    except (ScanLimit, FilterLimit, MemoryError) as exc:
        print(json.dumps({'status': 'UNKNOWN', 'reason': str(exc) or 'memory allocation failed'}))
        return 3
    except (DiagramError, ValueError, TypeError, KeyError, OSError) as exc:
        print(f'invalid input: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
