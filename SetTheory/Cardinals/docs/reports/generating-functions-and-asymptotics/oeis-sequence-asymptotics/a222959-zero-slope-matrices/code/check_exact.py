#!/usr/bin/env python3
"""Reproduce bounded exact checks; never mutate the package or overwrite output."""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import hashlib
import json
import os
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent.parent
sys.path.insert(0,str(ROOT))
sys.path.insert(0,str(ROOT/'code'))
import verify_manifest as manifest
import matrix_exact as matrix
import derive_second_correction as second
import verify_second_correction as second_verifier

FIXTURE_SHA256 = 'd90754d3d7932d36fdb1768c2b0fd40971192ab20088d657d0a3cdcce32d0bb7'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+'\n').encode('utf-8')


def checked_output(output):
    output = Path(output).absolute()
    need('..' not in output.parts, 'unsafe output path')
    manifest.check_directory(output.parent)
    need(not os.path.lexists(output), 'exact output already exists')
    need(not output.resolve().is_relative_to(ROOT.resolve()), 'output must be outside package')
    return output


def parse_fixture(raw):
    need(hashlib.sha256(raw).hexdigest() == FIXTURE_SHA256, 'reference checksum mismatch')
    data = manifest.load_json(raw)
    need(type(data) is dict and data.get('schema') == 'report194-finite-reference-v1'
         and type(data.get('report')) is int and data['report'] == 194,
         'reference identity mismatch')
    return data


def run_checks(max_n9=False):
    need(type(max_n9) is bool, 'max_n9 must be boolean')
    reference = parse_fixture(manifest.read_regular(ROOT/'data/reference.json'))
    local = [matrix.local_projection(n) for n in range(2,13)]
    structural = [matrix.structure(n) for n in range(2,15)]
    expected_structure = {row['n']:row for row in reference['structural_reference']}
    for row in structural:
        expected = expected_structure[row['n']]
        need(row['alphabet_size'] == expected['alphabet_size']
             and row['alphabet_rank'] == expected['alphabet_rank'], 'row alphabet reference mismatch')
    counts = [matrix.count_mitm(n,allow_n9=max_n9) for n in range(1,10 if max_n9 else 9)]
    expected_counts = {row['n']:row['count'] for row in reference['square_counts']}
    for row in counts:
        need(row['count'] == expected_counts[row['n']], 'matrix count reference mismatch')
        if row['n'] <= 7:
            need(row['count'] == matrix.count_tuple_reference(row['n']), 'packed/unpacked count mismatch')
    # Distinguish covariance from the theorem's half-covariance quadratic form.
    # A truncated gauge has norm squared 2S-1 and image norm squared S;
    # Bernoulli covariance is one quarter of the Gram matrix.
    rayleigh=[]
    for n in range(2,15):
        w=matrix.weights(n); S=sum(x*x for x in w); ell=w.index(1)
        v=w+[-w[j] for j in range(n) if j != ell]
        a=matrix.design(n)
        image=[sum(a[i][j]*v[i] for i in range(2*n-1)) for j in range(n*n)]
        need(sum(x*x for x in v) == 2*S-1 and sum(x*x for x in image) == S,
             'truncated-gauge Rayleigh identity failure')
        rayleigh.append({'n':n,'bernoulli_rayleigh_quotient':str(F(S,4*(2*S-1))),
                         'half_covariance_quadratic_quotient':str(F(S,8*(2*S-1)))})
    return {'status':'passed','report':194,'arithmetic':'integer and Fraction only',
            'network_required':False,'local_projection_checks':local,
            'structural_checks':structural,'matrix_counts':counts,
            'unpacked_crosscheck_through':7,'matrix_counts_recomputed_through':9 if max_n9 else 8,
            'first_coefficient':matrix.first_coefficient(),'second_coefficient_derivation':second.derive(),
            'second_coefficient_verification':second_verifier.verify(),'bernoulli_rayleigh_checks':rayleigh,
            'n9_recorded_evidence':reference['n9_evidence'],
            'n9_rerun_in_this_invocation':max_n9,
            'scope':'Finite exact arithmetic, saturation and enumeration checks only; analytic theorems and eventual error estimates are proved in Report194; computed coefficients are c0=1, c1=171/350, c2=483051/245000; no general all-order Wick engine is implemented.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='new JSON file outside package')
    parser.add_argument('--max-n9',action='store_true',help='optional 7,311,616-tuple n=9 rerun; substantially more memory and time')
    args=parser.parse_args()
    try:
        output=checked_output(args.output) if args.output is not None else None
        data=canonical(run_checks(args.max_n9))
        if output is not None:
            with output.open('xb') as stream:
                stream.write(data)
        sys.stdout.buffer.write(data)
    except (ValueError,OSError,TypeError) as exc:
        print(json.dumps({'status':'FAIL','error':str(exc)},sort_keys=True),file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
