#!/usr/bin/env python3
"""Emit complete unrestricted-integer circuits by a three-square substitution.

Default mode checks the supplied receipts without modifying any file.
--write regenerates only the two integer-domain JSON outputs.
All dependencies are sibling files in this artifact folder and Python's stdlib.
The algebra fixtures test transcription, not existence of any halting witness.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import random
from fractions import Fraction
from pathlib import Path

from build_fixed_sources import (check_graph, degree_upper, evaluate, ledger,
                                 line_degree, require)
from verify_closed_forms import expected, forms


SPECS = [
    ('fixed15_product82_degree295',
     'fd2d22a506631d1fc6cfbe35c65c8cd403e8ead08846c6ad996cb5a39e0651d7',
     'integer45_product187_degree590', 45, 187, 91, 96, 590),
    ('fixed16_sos86_degree68',
     '4d9aa14bc25a7590241b71599d903d47cb8102b6800a521504a690f5f368db73',
     'integer48_sos198_degree136', 48, 198, 90, 108, 136),
]


def lift(parent, source_hash, name):
    """The original positive witnesses become computed polynomial registers."""
    rows, free, substitutions = [], [], {}
    for z in parent['witnesses']:
        stem = 'integer_lift_' + z
        a, b, c = [stem + '_' + s for s in ('a', 'b', 'c')]
        free.extend([a, b, c])
        substitutions[z] = [a, b, c]
        rows.extend([
            [stem+'_a2', '*', a, a],
            [stem+'_b2', '*', b, b],
            [stem+'_cplus1', '+', c, 1],
            [stem+'_cproduct', '*', c, stem+'_cplus1'],
            [stem+'_squares', '+', stem+'_a2', stem+'_b2'],
            [stem+'_sum', '+', stem+'_squares', stem+'_cproduct'],
            [z, '+', stem+'_sum', 1],
        ])
    rows += parent['source']
    output = parent['output']
    require(output is not None and parent['equations'] is None,
            'integer lift expects a single polynomial parent')
    check_graph(rows, free+parent['fixed_numerals'], [output])
    degrees = degree_upper(rows, free)
    degree = 2*parent['exact_degree']
    require(degrees[output] == degree, 'doubled degree upper bound')
    diagnostic = line_degree(rows, free, [output])
    require(diagnostic[output]['degree'] == degree,
            'full-source degree diagnostic')
    return {
        'name': name,
        'source_commit': parent['source_commit'],
        'parent_positive_source': parent['name']+'.json',
        'parent_positive_source_sha256': source_hash,
        'witnesses': free,
        'witness_domain': 'all integers, with no sign restrictions',
        'fixed_numerals': parent['fixed_numerals'],
        'substitution_formula': 'z = 1 + a*a + b*b + c*(c+1)',
        'substitution_variables': substitutions,
        'substitution_lemma': (
            'For every integer triple the image is positive. For every '
            'positive z, Legendre three-square representation of 4*(z-1)+1, '
            'with one odd square and two even squares, gives such a triple.'),
        'source': rows,
        'output': output,
        'equations': None,
        'ledger': ledger(rows),
        'exact_degree': degree,
        'degree_proof': (
            'The parent has its stated nonzero highest homogeneous part. '
            'The substitution has degree two, giving the upper bound twice '
            'the parent degree. Setting every b=c=0 makes the leading '
            'substitution z=a*a, whose map on monomials is injective, so '
            'the highest part remains nonzero and the bound is exact.'),
        'degree_upper_by_register': degrees,
        'supplementary_full_source_degree_diagnostic': diagnostic,
        'diagnostic_scope': (
            'Arbitrary small numeral slice: an algebra check, not a valid '
            'compiler instance or a halting witness.'),
        'intermediate_domain': (
            'Computed registers, including all original positive witnesses, '
            'are polynomial abbreviations and not additional unknowns.'),
    }


def verify_closed_form(parent, packet):
    """Compare every complete lifted source to separately written formulas."""
    rng = random.Random(2026102203)
    for j in range(24):
        v = {n: rng.randint(-3, 5)
             for n in packet['witnesses']+packet['fixed_numerals']}
        if j % 2:
            v = {n: Fraction(x, rng.randint(1, 3)) for n, x in v.items()}
        positive = {n: v[n] for n in packet['fixed_numerals']}
        for z, (an, bn, cn) in packet['substitution_variables'].items():
            a, b, c = v[an], v[bn], v[cn]
            positive[z] = 1+a*a+b*b+c*(c+1)
            if not j % 2:
                require(positive[z] >= 1, 'integer image is positive')
        got = evaluate(packet['source'], v)[packet['output']]
        want = expected(parent['name'], forms(positive))
        require(got == want, 'independent lifted closed form')
    return {'exact_signed_integer_cases': 12, 'exact_rational_cases': 12}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    records = {}
    for stem, checksum, name, count, gates, mult, add, degree in SPECS:
        raw = (root/(stem+'.json')).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == checksum,
                'pinned positive source checksum: '+stem)
        parent = json.loads(raw)
        packet = lift(parent, checksum, name)
        require(len(packet['witnesses']) == count, 'unknown count')
        require(packet['ledger'] == {
            'operations': gates, 'multiplications': mult,
            'additions_subtractions': add}, 'operation ledger')
        require(packet['exact_degree'] == degree, 'degree')
        algebra = verify_closed_form(parent, packet)
        target = root/(name+'.json')
        if args.write:
            target.write_text(json.dumps(packet, indent=2)+'\n')
        else:
            require(json.loads(target.read_text()) == packet,
                    'integer source receipt mismatch: '+name)
        records[name] = dict(witnesses=count, **packet['ledger'],
                             degree=degree, **algebra)
    print(json.dumps({
        'status': 'PASS',
        'scope': ('Complete unrestricted-integer circuit reconstruction, '
                  'source hashes, liveness, operation counts, degree bounds '
                  'and supplementary full-source degree diagnostics, plus '
                  'independent exact closed-form fixtures; not a semantic '
                  'proof or a halting-witness claim.'),
        'circuits': records,
    }, indent=2))


if __name__ == '__main__':
    main()
