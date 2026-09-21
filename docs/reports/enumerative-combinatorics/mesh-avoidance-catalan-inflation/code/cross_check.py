#!/usr/bin/env python3
"""Cross-check the two independent coefficient implementations.

code/verify.py (excedance-based) and code/verify_records.py (record-based)
were written independently and share no code.  Each is a complete checker on
its own; this script only compares their arithmetic, so that the O(N) linear
recurrence of verify_records.py is pinned against the O(N^2) positive
recurrences and the radical expansion of verify.py.

Standard library only.  Run without Python's -O switch.
Agreement of two algorithms at finitely many indices is corroboration, not
a proof of the identity for all n; the proof is in the article.
"""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path
from time import perf_counter

sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify import coeffs, radical_coeffs                     # noqa: E402
from verify_records import fast_coefficients, positive_coefficients  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=1000)
    parser.add_argument('--out', type=Path,
                        default=Path(__file__).resolve().parents[1]/'data')
    args = parser.parse_args()
    if not __debug__:
        parser.error('Do not use -O: this checker uses assertions.')
    if args.max_n < 0:
        parser.error('Require max-n >= 0')
    args.out.mkdir(parents=True, exist_ok=True)
    start = perf_counter()

    N = args.max_n
    core_exc, _, _, a_positive_exc = coeffs(N)      # excedance side, O(N^2)
    a_radical = radical_coeffs(N)                   # excedance side, radical
    core_rec, a_positive_rec = positive_coefficients(N)  # record side, O(N^2)
    a_linear = fast_coefficients(N)                 # record side, O(N)

    assert a_positive_exc == a_radical, 'excedance-side algorithms disagree'
    assert a_positive_rec == a_linear, 'record-side algorithms disagree'
    assert a_positive_exc == a_linear, 'the two packages disagree on a_n'
    assert core_exc == core_rec, 'the two packages disagree on the core series'

    result = {'status': 'all four coefficient algorithms agree',
              'max_n': N,
              'terms_compared': N+1,
              'algorithms': ['verify.coeffs (positive O(N^2), excedances)',
                             'verify.radical_coeffs (radical expansion)',
                             'verify_records.positive_coefficients '
                             '(positive O(N^2), records)',
                             'verify_records.fast_coefficients '
                             '(linear-arithmetic O(N))'],
              'core_series_agrees': True,
              'seconds': round(perf_counter()-start, 3),
              'note': 'Finite agreement corroborates but does not replace '
                      'the proof in the article.'}
    (args.out/'cross_check_results.json').write_text(
        json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
