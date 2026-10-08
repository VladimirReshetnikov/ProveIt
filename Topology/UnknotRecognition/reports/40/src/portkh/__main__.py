"""python -m portkh example 40 | python -m portkh analyze -"""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path
from .complexes import PortComplex, analyze, coupled_pair, connected_singular_pair


def main() -> int:
    # Exact scientific cardinalities may exceed CPython's decimal digit guard.
    # This changes only this CLI process, not an importing application's policy.
    if hasattr(sys, 'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description='Exact homology of port-register complexes; not a standalone knot recognizer.')
    sub = parser.add_subparsers(dest='command', required=True)
    ex = sub.add_parser('example')
    ex.add_argument('length', type=int)
    ex.add_argument('--kind', choices=['singular','connected-singular','invertible','large_homology'], default='singular')
    an = sub.add_parser('analyze')
    an.add_argument('input', help='JSON presentation path, or - for stdin')
    an.add_argument('--languages', help='JSON array of deterministic language descriptors (or null)')
    mi = sub.add_parser('minimize')
    mi.add_argument('input', help='presentation path, or - for stdin')
    ve = sub.add_parser('verify')
    ve.add_argument('input')
    ve.add_argument('certificate')
    ve.add_argument('--languages', help='language array used for a restricted certificate')
    args = parser.parse_args()
    try:
        if args.command == 'example':
            example = (connected_singular_pair(args.length) if args.kind == 'connected-singular'
                       else coupled_pair(args.length, args.kind))
            result = example.to_dict()
        else:
            text = sys.stdin.read() if args.input == '-' else Path(args.input).read_text()
            obj = PortComplex.from_dict(json.loads(text))
            if args.command == 'minimize':
                from .minimize import minimize_ports
                minimized, _ = minimize_ports(obj)
                result = minimized.to_dict()
            else:
                if args.languages:
                    from .languages import Language, analyze_restricted
                    language_data = json.loads(Path(args.languages).read_text())
                    languages = tuple(None if x is None else Language.from_dict(x) for x in language_data)
                    result = analyze_restricted(obj, languages)
                else:
                    result = analyze(obj)
            if args.command == 'verify':
                claimed = json.loads(Path(args.certificate).read_text())
                if result != claimed:
                    raise ValueError('certificate does not match exact replay')
                result = {'verified': True, 'homology_dimension': result['homology_dimension'],
                          'scope': result['scope']}
        json.dump(result, sys.stdout, indent=2)
        print()
        return 0
    except (ValueError, KeyError, TypeError, OSError, ArithmeticError, MemoryError) as exc:
        print(f'portkh: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
