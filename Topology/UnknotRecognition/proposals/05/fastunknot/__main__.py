"""Command line interface: python -m fastunknot --help."""
from __future__ import annotations
import argparse
import json
import sys
from .alexander import alexander_polynomial, format_polynomial
from .diagram import Diagram, DiagramError
from .filters import bracket_obstruction
from .recognize import recognize, verify_modular_result
from .scan import ScanLimit, khovanov_rank

EXIT = {'UNKNOT': 0, 'KNOTTED': 0, 'UNKNOWN': 3}

def load_json(path: str):
    if path == '-':
        return json.load(sys.stdin)
    with open(path, encoding='utf-8') as handle:
        return json.load(handle)

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog='fastunknot', description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    rec = sub.add_parser('recognize', help='exact unknot recognition')
    rec.add_argument('file')
    rec.add_argument('--max-objects', type=int, default=None)
    rec.add_argument('--seconds', type=float, default=None, help='cooperative time budget')
    for name in ('reduction', 'descending', 'alexander', 'modular', 'jones', 'integer-jones'):
        rec.add_argument('--no-' + name, action='store_true')
    rec.add_argument('--jones-max-transitions', type=int, default=None)
    rec.add_argument('--jones-max-states', type=int, default=4096)
    rec.add_argument('--check-d2', action='store_true')
    rec.add_argument('--output')
    kh = sub.add_parser('khovanov', help='unreduced/reduced total F2 ranks; no recognition filters')
    kh.add_argument('file')
    kh.add_argument('--check-d2', action='store_true')
    kh.add_argument('--max-objects', type=int, default=None)
    kh.add_argument('--seconds', type=float, default=None)
    al = sub.add_parser('alexander', help='full exact Alexander polynomial')
    al.add_argument('file')
    br = sub.add_parser('bracket', help='one-sided modular bracket obstruction, NOT a recognizer')
    br.add_argument('file')
    br.add_argument('--max-transitions', type=int, default=None)
    br.add_argument('--max-states', type=int, default=None)
    br.add_argument('--integer', action='store_true')
    vr = sub.add_parser('verify', help='replay and verify a modular KNOTTED result')
    vr.add_argument('file')
    vr.add_argument('result')
    args = parser.parse_args(argv)
    try:
        diagram = Diagram.from_json(load_json(args.file))
        if args.command == 'recognize':
            result = recognize(diagram, use_reduction=not args.no_reduction,
                               use_descending=not args.no_descending,
                               use_alexander=not args.no_alexander,
                               use_modular=not args.no_modular, use_jones=not args.no_jones,
                               use_integer_jones=not args.no_integer_jones,
                               jones_max_transitions=args.jones_max_transitions,
                               jones_max_states=args.jones_max_states, max_objects=args.max_objects,
                               seconds=args.seconds, check_d_squared=args.check_d2).to_json()
            text = json.dumps(result, indent=2)
            if args.output:
                with open(args.output, 'w', encoding='utf-8') as handle:
                    handle.write(text + '\n')
            print(text)
            return EXIT[result['status']]
        if args.command == 'khovanov':
            print(json.dumps(khovanov_rank(diagram.pd, check_d_squared=args.check_d2,
                                           max_objects=args.max_objects, seconds=args.seconds), indent=2))
        elif args.command == 'alexander':
            poly = alexander_polynomial(diagram)
            print(json.dumps({'alexander_polynomial': format_polynomial(poly), 'coefficients': poly}))
        elif args.command == 'bracket':
            print(json.dumps(bracket_obstruction(diagram, modulus=None if args.integer else 2147483647,
                                                 max_transitions=args.max_transitions,
                                                 max_states=args.max_states), indent=2))
        else:
            verified = verify_modular_result(diagram, load_json(args.result))
            print(json.dumps({'verified': verified}))
            return 0 if verified else 4
    except ScanLimit as exc:
        print(json.dumps({'status': 'UNKNOWN', 'reason': str(exc)}))
        return 3
    except (DiagramError, ValueError, OSError, TypeError, KeyError, AttributeError) as exc:
        print(f'invalid input: {exc}', file=sys.stderr)
        return 2
    return 0

if __name__ == '__main__':
    sys.exit(main())
