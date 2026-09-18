"""Command-line tools for exact accelerated unknot recognition."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from .alexander import alexander_polynomial, format_polynomial
from .diagram import Diagram, DiagramError
from .decompose import factor_diagram
from .filters import bracket_evaluation
from .recognize import recognize
from .scan import ScanLimit, khovanov_rank

EXIT = {'UNKNOT': 0, 'KNOTTED': 0, 'UNKNOWN': 3}


def load(path: str) -> Diagram:
    if path == '-':
        return Diagram.from_json(json.load(sys.stdin))
    with open(path, encoding='utf-8') as handle:
        return Diagram.from_json(json.load(handle))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog='fastunknot', description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    rec = sub.add_parser('recognize', help='exact verdict or UNKNOWN at a resource ceiling')
    rec.add_argument('file')
    rec.add_argument('--max-objects', type=int, help='per-factor Khovanov object ceiling')
    rec.add_argument('--seconds', type=float, help='cooperative total time budget')
    for flag in ('reduction', 'descending', 'alexander', 'modular', 'jones', 'factor'):
        rec.add_argument('--no-' + flag, action='store_true')
    rec.add_argument('--jones-max-states', type=int, default=20000)
    rec.add_argument('--check-d2', action='store_true')
    rec.add_argument('--output')
    kh = sub.add_parser('khovanov', help='total and homological F2 ranks')
    kh.add_argument('file')
    kh.add_argument('--check-d2', action='store_true')
    kh.add_argument('--no-factor', action='store_true', help='benchmark the scan kernel alone')
    kh.add_argument('--max-objects', type=int)
    kh.add_argument('--seconds', type=float)
    al = sub.add_parser('alexander', help='exact Alexander polynomial')
    al.add_argument('file')
    jo = sub.add_parser('jones', help='one-sided modular bracket obstruction (not a recognizer)')
    jo.add_argument('file')
    jo.add_argument('--a', type=int, default=2)
    jo.add_argument('--modulus', type=int, default=1_000_000_007)
    jo.add_argument('--max-states', type=int, default=20000)
    de = sub.add_parser('decompose', help='visible connected-sum factors and replay data')
    de.add_argument('file')
    args = parser.parse_args(argv)
    try:
        diagram = load(args.file)
        code = 0
        if args.command == 'recognize':
            data = recognize(diagram, use_reduction=not args.no_reduction,
                             use_descending=not args.no_descending,
                             use_alexander=not args.no_alexander,
                             use_modular=not args.no_modular, use_jones=not args.no_jones,
                             use_factorization=not args.no_factor,
                             jones_max_states=args.jones_max_states,
                             max_objects=args.max_objects, seconds=args.seconds,
                             check_d_squared=args.check_d2).to_json()
            code = EXIT[data['status']]
        elif args.command == 'khovanov':
            data = khovanov_rank(diagram.pd, check_d_squared=args.check_d2,
                                 factor=not args.no_factor, max_objects=args.max_objects,
                                 seconds=args.seconds)
        elif args.command == 'alexander':
            poly = alexander_polynomial(diagram)
            data = {'alexander_polynomial': format_polynomial(poly), 'coefficients': poly}
        elif args.command == 'jones':
            data = bracket_evaluation(diagram, a=args.a, modulus=args.modulus,
                                       max_states=args.max_states)
            data['interpretation'] = 'KNOTTED' if data['obstruction'] else 'INCONCLUSIVE'
        else:
            factors, trace = factor_diagram(diagram)
            data = {'factors': [d.to_json() for d in factors], 'split_trace': trace,
                    'prime_decomposition_claimed': False}
        text = json.dumps(data, indent=2)
        if getattr(args, 'output', None):
            Path(args.output).write_text(text + '\n', encoding='utf-8')
        print(text)
        return code
    except ScanLimit as exc:
        print(json.dumps({'status': 'UNKNOWN', 'reason': str(exc)}))
        return 3
    except (DiagramError, ValueError, TypeError, OSError) as exc:
        print(f'invalid input: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
