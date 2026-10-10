#!/usr/bin/env python3
"""Replay every exact certificate in this package (standard library only)."""
from __future__ import annotations
import json
import platform
from pathlib import Path
import sys

if not __debug__:
    raise RuntimeError('Do not use -O: assertion checks are part of this verifier.')
if sys.version_info < (3,10):
    raise RuntimeError('Python 3.10 or newer is required.')

from verify_global import run as global_run
from verify_roots import run as roots_run
from verify_identities import run as identities_run

ROOT=Path(__file__).resolve().parents[1]

def main() -> None:
    print('Replaying uniform-parameter certificate ...',flush=True)
    g=global_run()
    print('Replaying eight rational root brackets ...',flush=True)
    r=roots_run()
    print('Replaying positive identities and elementary control ...',flush=True)
    i=identities_run()
    receipt={
        'status':'PASS',
        'python':platform.python_version(),
        'acceptance_arithmetic':'Python standard library fractions.Fraction; no floating point',
        'global_outer_threshold':g['outer_order_threshold'],
        'positive_Bernstein_coefficients':10,
        'certified_angular_brackets':len(r['brackets']),
        'certified_Gaussian_values':len(i['enclosures']),
        'positive_binomial_moments':i['positive_binomial_moments_checked'],
        'finite_geometric_identities':i['geometric_remainder_identities_checked'],
        'large_inner_order_thresholds':g['large_b_thresholds'],
        'scope':'Finite certificates replayed. Analytic lemmas and transfer arguments are proved in article.tex, not proof-assistant formalized.'
    }
    (ROOT/'data'/'verification_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS: all exact certificate suites completed.')
    print('10 Bernstein coefficients; 8 root brackets; 9 Gaussian values;')
    print('720 positive binomial moments; 100 finite geometric identities.')

if __name__=='__main__':
    main()
