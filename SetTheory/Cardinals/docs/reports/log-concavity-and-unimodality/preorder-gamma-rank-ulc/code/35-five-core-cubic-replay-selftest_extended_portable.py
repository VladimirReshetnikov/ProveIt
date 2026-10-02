#!/usr/bin/env python3
"""Portable adversarial tests of the independent extended checker.
Usage: python selftest_extended_portable.py SOURCE --output RECEIPT"""
from pathlib import Path
from tempfile import TemporaryDirectory
from copy import deepcopy
from collections import Counter
import argparse
import hashlib
import json
import time
import check_extended as check


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = time.time()
    cores, catalog_hash = check.read_catalog(args.source/'cores.txt')
    support_totals = Counter()
    for code, rows in cores:
        gamma = check.construct_gammas(code, rows)
        for k, polynomial in enumerate(gamma):
            support_totals[k] += len(polynomial)
            # The two universal sinks must be interchangeable independently
            # of all core activities and all labels of the core relation.
            swapped = {}
            for e, c in polynomial.items():
                a = (e // check.UNIT[10]) % check.RADIX
                b = (e // check.UNIT[11]) % check.RADIX
                swapped[e + (b-a)*check.UNIT[10] + (a-b)*check.UNIT[11]] = c
            check.require(swapped == polynomial, 'Sink-swap symmetry failed')
    empty = check.construct_gammas(0, (0,0,0,0,0))
    complete = check.construct_gammas((1 << 20)-1, (30,29,27,23,15))
    check.require([len(g) for g in empty] == [1,10,10,0], 'Wrong empty-core counts')
    check.require([len(g) for g in complete] == [1,30,100,40], 'Wrong complete-core counts')
    valid = {'rows': [0]*5, 'sink_count': 2, 'target': check.TARGET, 'terms': []}
    tests = []
    with TemporaryDirectory(prefix='five-core-cubic-selftest-') as temp:
        directory = Path(temp)/'two-sink-cubic'
        directory.mkdir()
        path = directory/'certificate_0.json'
        def run(name, certificate, must_reject):
            path.write_text(json.dumps(certificate))
            try:
                check.check_one((temp, 0, 0, (0,0,0,0,0)))
            except (ValueError, TypeError, ZeroDivisionError, IndexError):
                check.require(must_reject, 'Unexpected selftest rejection: '+name)
                tests.append({'test': name, 'result': 'rejected as required'})
            else:
                check.require(not must_reject, 'Failed to reject: '+name)
                tests.append({'test': name, 'result': 'accepted as required'})
        run('valid coefficientwise-positive target', valid, False)
        m1 = [1,1,0,0,0,0,0,0,0,0,1,1]
        m2 = [0,0,1,1,0,0,0,0,0,0,1,1]
        with_square = deepcopy(valid)
        with_square['terms'] = [['1', [[0]*12, [[m1,'1'],[m2,'-1']]]]]
        run('valid exact binomial square including signed cross terms', with_square, False)
        for name, edit in [
            ('wrong sink count', lambda c: c.update(sink_count=3)),
            ('wrong target', lambda c: c.update(target='2G2^2-3G1G3')),
            ('wrong rows', lambda c: c.update(rows=[2,0,0,0,0])),
            ('unsupported change-of-variables metadata', lambda c: c.update(substitution='w0=w1+x')),
        ]:
            c=deepcopy(valid); edit(c); run(name,c,True)
        c=deepcopy(with_square); c['terms'][0][0]='-1'; run('negative square multiplier',c,True)
        c=deepcopy(with_square); c['terms'][0][0]=0.5; run('inexact floating-point scalar',c,True)
        c=deepcopy(with_square); c['terms'][0][1][1][0][0][0]=-1; run('negative exponent',c,True)
        c=deepcopy(with_square); c['terms'][0][1][1][0][0].append(0); run('wrong exponent dimension',c,True)
        c=deepcopy(with_square); c['terms'][0][1][1][0][0][0]=0; run('nonhomogeneous inner polynomial',c,True)
        c=deepcopy(valid)
        absent=[0]*12; absent[5]=4
        c['terms']=[['1',[[0]*12,[[absent,'1']]]]]
        run('negative remainder at a monomial absent from the target',c,True)
        c=deepcopy(valid); c['terms']=[['2',[[0]*12,[[m1,'1']]]]]
        run('negative remainder at a present target monomial',c,True)
    receipt={
        'status':'PASS', 'all_9608_representatives_literal_vs_hall_checked':True,
        'all_9608_representatives_sink_symmetry_checked':True,
        'support_counts_summed_over_representatives':dict(sorted(support_totals.items())),
        'empty_core_gamma_support_counts':[len(g) for g in empty],
        'complete_core_gamma_support_counts':[len(g) for g in complete],
        'adversarial_tests':tests,
        'catalog_sha256':catalog_hash,
        'checker_sha256':hashlib.sha256(Path(check.__file__).read_bytes()).hexdigest(),
        'selftest_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'producer_code_imported_or_executed':False,
        'seconds':round(time.time()-started,3),
    }
    out=args.output
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':
    main()
