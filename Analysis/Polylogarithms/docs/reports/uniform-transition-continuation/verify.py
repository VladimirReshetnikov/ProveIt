#!/usr/bin/env python3
"""Replay all exact checks in an isolated temporary copy of the code.

Default: exact symbolic/algebraic checks, the exact interval proof, and the
small independent Hurwitz diagnostic included in the distribution verifier.
Add --numerical to replay the longer harmonic and joint-moment quadratures.
The analytic theorems are justified by their article proofs, not these tests.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--numerical', action='store_true')
    parser.add_argument('--receipt', type=Path,
                        default=ROOT/'provenance'/'verification_receipt.json')
    args = parser.parse_args()
    import sympy
    import mpmath
    records = []
    with tempfile.TemporaryDirectory(prefix='proveit_polylog_checks_') as tmp:
        code = Path(tmp)/'code'
        shutil.copytree(ROOT/'code', code,
                        ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))

        def run(label, relative, *extra):
            path = code/relative
            start = time.monotonic()
            result = subprocess.run([sys.executable, str(path), *map(str, extra)],
                                    cwd=path.parent, text=True, capture_output=True)
            if result.returncode:
                print(result.stdout)
                print(result.stderr, file=sys.stderr)
                raise RuntimeError(label+' failed')
            records.append({'check': label, 'script': relative,
                            'passed': True,
                            'seconds': round(time.monotonic()-start, 3),
                            'stdout_sha256': hashlib.sha256(result.stdout.encode()).hexdigest()})
            print('PASS:', label, flush=True)
            return result.stdout

        run('Harmonic inverse by exact forward compilation',
            'harmonic/compile_inverse.py')
        produced=json.loads((code/'harmonic'/'inverse_polynomials.json').read_text())
        saved=json.loads((ROOT/'code'/'harmonic'/'inverse_polynomials.json').read_text())
        assert produced['Q']==saved['Q'] and produced['verification']['all_checks_passed']

        independent=json.loads(run('Independent shifted-gamma inverse derivation',
                                   'gaussian/audit_inverse_q1.py'))
        assert all(independent['agrees_with_stored_inverse'])
        assert all(independent['exact_inverse_residual_zero'])

        run('Moment corrections from centered gamma moments',
            'moments/derive_correction.py')
        run('Moment corrections from finite offset residues',
            'moments/verify_residue_polynomials.py')
        run('All-order moment generator through order three',
            'moments/generate_transition_polynomials.py', '--order', 3)
        produced=json.loads((code/'moments'/'transition_polynomials.json').read_text())
        saved=json.loads((ROOT/'code'/'moments'/'transition_polynomials.json').read_text())
        assert [x['sympy'] for x in produced]==[x['sympy'] for x in saved]

        certificate=code/'moments'/'gamma_saddle_replay.json'
        run('Exact rational interval proof of reflected slope monotonicity',
            'moments/certify_gamma_saddle.py', '--output', certificate)
        cert=json.loads(certificate.read_text())
        expected=json.loads((ROOT/'code'/'moments'/'gamma_saddle_certificate.json').read_text())
        assert cert['verified'] and cert['segments']==256 and cert['series_terms']==40
        assert Fraction(cert['minimum_certified_lower_bound'])>Fraction(7,4)
        assert cert['minimum_certified_lower_bound']==expected['minimum_certified_lower_bound']
        assert cert['all_interval_lower_numerators']==expected['all_interval_lower_numerators']

        run('Integral grid, determinant, resolution, and Smith checks',
            'distribution/verify_integral_distribution.py')
        dist=json.loads((code/'distribution'/'verification_summary.json').read_text())
        assert dist['all_checks_passed']
        assert (dist['symbolic_grid_levels'],dist['integral_determinant_levels'],
                dist['finite_characteristic_resolution_checks'],
                dist['complete_two_prime_smith_checks'])==(59,19,112,504)
        assert dist['examples']['q15_s2']['exact_common_denominator']==511680
        assert dist['examples']['q15_s2']['nonunit_smith_signature']==[2,4,511680]

        eq=json.loads(run('Exact equivalence of the two S6 conjectures',
                          'gaussian/verify_s6_equivalence.py'))
        assert eq['verified'] and eq['residual_terms']==0

        if args.numerical:
            run('Harmonic quadrature diagnostics (not interval certificates)',
                'harmonic/diagnostics.py')
            run('Joint-moment quadrature diagnostics (not interval certificates)',
                'moments/verify_joint_moments.py')

    script_hashes={p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in sorted((ROOT/'code').rglob('*.py'))}
    receipt={'all_checks_passed': True,
             'created_utc': datetime.now(timezone.utc).isoformat(),
             'python': platform.python_version(), 'sympy': sympy.__version__,
             'mpmath': mpmath.__version__,
             'long_numerical_diagnostics_replayed': args.numerical,
             'checks': records, 'script_sha256': script_hashes,
             'distribution_counts': {k: dist[k] for k in (
                 'symbolic_grid_levels','integral_determinant_levels',
                 'finite_characteristic_resolution_checks','complete_two_prime_smith_checks')},
             'gamma_slope_minimum_certified_lower_bound': cert['minimum_certified_lower_bound'],
             'scope': 'Exact finite verification supplements article proofs. S6 itself remains conjectural.'}
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(json.dumps(receipt, indent=2)+'\n')
    print('All requested checks passed. Receipt:', args.receipt)


if __name__=='__main__':
    main()
