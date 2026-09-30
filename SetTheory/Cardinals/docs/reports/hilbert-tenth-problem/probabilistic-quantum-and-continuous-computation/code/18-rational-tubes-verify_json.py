"""Check supplied *_certificate.json files with exact integer arithmetic."""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys
from tubes import Instance, Certificate, verify, require


def load_instance(data: dict) -> Instance:
    initial = []
    for pair in data['initial']:
        require(len(pair) == 2 and all(type(x) is int for x in pair),
                'initial coordinates must be integer numerator/denominator pairs')
        initial.append(Fraction(pair[0], pair[1]))
    polynomials = tuple(tuple((coefficient, tuple(alpha)) for coefficient, alpha in p)
                        for p in data['polynomials'])
    target = tuple((tuple(a), b) for a, b in data['target'])
    return Instance(polynomials, data['denominator'], tuple(initial), target)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths', nargs='+', type=Path)
    args = parser.parse_args()
    failed = False
    for path in args.paths:
        try:
            data = json.loads(path.read_text(encoding='utf-8'))
            instance = load_instance(data['instance'])
            certificate = Certificate(**data['certificate'])
            result = verify(instance, certificate)
            print(f"ACCEPT {path.name}: T={result['physical_time']}, "
                  f"error={result['final_error']}")
        except (OSError, KeyError, TypeError, ValueError, ZeroDivisionError) as exc:
            print(f"REJECT {path}: {exc}", file=sys.stderr)
            failed = True
    return int(failed)


if __name__ == '__main__':
    raise SystemExit(main())
