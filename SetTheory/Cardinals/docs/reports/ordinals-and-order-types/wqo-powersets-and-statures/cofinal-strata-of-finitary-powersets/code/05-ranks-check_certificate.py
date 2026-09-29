"""Check a saved finite height or point-rank certificate.

Usage: python code/check_certificate.py examples/weighted_N_certificate.json
A successful result is a finite recurrence/path check, not a formal proof of
the transfinite theorem relating that recurrence to ordinal heights.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from heights import check_certificate, point_rank
from ordinals import Ordinal, ONE


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    args = parser.parse_args()
    try:
        data = json.loads(args.certificate.read_text(encoding='utf-8'))
        if 'lower_interval_certificate' in data:
            cert = data['lower_interval_certificate']
            rank = Ordinal.from_json(data['rank'])
            valid = check_certificate(cert)
            valid = valid and rank + ONE == Ordinal.from_json(cert['height'])
            # Also check that the original generators specify this local problem.
            rebuilt = point_rank(data['original_input'], data['generators'], cert['vertices'])
            valid = valid and rebuilt['rank'] == data['rank']
            valid = valid and rebuilt['lower_interval_certificate']['source_input'] == cert['source_input']
        else:
            valid = check_certificate(data)
        if not valid:
            parser.exit(1, 'FAIL: certificate does not satisfy the finite checks\n')
        print('PASS: finite recurrence, witness path, and recorded source refinement checked.')
    except (OSError, ValueError, KeyError, TypeError, IndexError) as error:
        parser.exit(2, f'error: {error}\n')


if __name__ == '__main__':
    main()
