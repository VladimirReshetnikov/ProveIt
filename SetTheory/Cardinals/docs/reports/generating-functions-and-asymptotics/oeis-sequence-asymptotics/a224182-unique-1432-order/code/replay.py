#!/usr/bin/env python3
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True
"""Combine independently computed exact integer results."""
import primary
import coordinate


def run():
    a, b = primary.run(), coordinate.run()
    for field in ('by_size', 'inverse_certificate', 'obstruction_records'):
        if a[field] != b[field]:
            raise RuntimeError('independent implementations disagree: ' + field)
    certificate = a.pop('obstruction_records')
    b.pop('obstruction_records')
    return {'obstruction_certificate': certificate, 'schema': 'report139-exact-v1', 'status': 'PASS',
            'primary': a, 'independent': b,
            'scope': 'Finite cross-checks supplement the computer-free order theorem. The exact image theorem uses the finite obstruction certificate. No formal verification or amplitude limit is claimed.'}
