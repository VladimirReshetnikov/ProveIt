#!/usr/bin/env python3
"""Reproduce the finite compiler checks using Python's standard library.

This checks the pinned table, exact category counts, finite toy tableaux,
coefficient recipes and sparse support audits. It does not expand the fixed
coefficients, enumerate the giant alphabets, or verify imported Pell proofs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
COMPILER = ROOT / 'compiler'
sys.path.insert(0, str(COMPILER))
import blank_helical as blank
import count_blank_alphabet as cross_count
import cross_compiler_constants as cross
import tshape_compiler_constants as tshape
import tshape_helical as four_site
from verify_k215 import parse_tm

PINNED_HASHES = {
    'k215.tm': 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090',
    'blank_helical.py': '6f6ca0370faa612cde5136dfbd3d44f87e5e4694f2fefd3bdc77d84cf708d8f8',
    'count_blank_alphabet.py': '2837bebf8a5b71cb58e01c1bad7e142e1d2cdb6f7aa1011949974cba8fdd5589',
    'verify_k215.py': '9d7b1d0238e2348c59b2d1d4fd33b8a9116793b4bfd2362362c1b81f5487e3e8',
}

def require(condition, message):
    if not condition:
        raise ValueError(message)

def compare_receipt(name, result):
    expected = json.loads((COMPILER/name).read_text(encoding='utf-8'))
    actual = json.loads(json.dumps(result))
    require(actual == expected, f'Recomputed receipt differs: {name}')

def verify():
    for name, expected in PINNED_HASHES.items():
        require(hashlib.sha256((COMPILER/name).read_bytes()).hexdigest() == expected,
                f'Pinned source hash differs: {name}')
    rows = parse_tm((COMPILER/'k215.tm').read_bytes())
    require(len(rows) == 430, 'K215 must have exactly 430 actions')
    blank_result = blank.verify(rows)
    counted_crosses = cross_count.verify(rows, direct=True)
    compare_receipt('cross_count_verification.json', counted_crosses)
    counted_four_site = four_site.verify(rows, direct=True)
    compare_receipt('tshape_count_verification.json', counted_four_site)
    require(counted_crosses['valid_crosses'] == 38256607897, 'Cross count')
    require(counted_four_site['windows'] == 71356645, 'Four-site count')

    cross_result = {'constants': cross.specification(), 'verification': cross.verify()}
    tshape_result = {'constants': tshape.specification(), 'verification': tshape.verify()}
    compare_receipt('cross_constants.json', cross_result)
    compare_receipt('tshape_constants.json', tshape_result)
    for packet, expected_k, expected_d in [
            (cross_result, 38256607897, 5**36),
            (tshape_result, 71356645, 5**28)]:
        constants = packet['constants']
        require(constants['window_count'] == expected_k, 'Coefficient alphabet size')
        require(constants['layout']['cell_bits'] == expected_d, 'Coefficient bit length')
        require(constants['polynomial_ports'] == ['Bm1', 'Kconstant', 'MC', 'MF'],
                'Unexpected arithmetic coefficient ports')
        require(constants['free_parameters'] == [], 'Unexpected free compiler parameter')
        require(constants['machine_sha256'] == PINNED_HASHES['k215.tm'], 'Machine pin')

    # The cross predicate is exactly the inherited predicate without corners.
    table = blank.table_from_rows(rows)
    for marker in (cross.START, cross.EXCLUDED):
        window = [0]*9
        for position, value in zip((1,3,4,5,7), marker):
            window[position] = value
        require(blank.local_valid(window, table), 'A cross marker is not locally valid')
    require(blank.DECODED[cross.EXCLUDED[0]][0] !=
            blank.DECODED[cross.EXCLUDED[2]][0], 'Cross excluded-marker contradiction')

    return {
        'status': 'PASS',
        'pinned_source_hashes': len(PINNED_HASHES),
        'machine_actions': len(rows),
        'cross_windows': counted_crosses['valid_crosses'],
        'four_site_windows': counted_four_site['windows'],
        'center_classes_compared_to_local_predicate_per_variant': 13,
        'old_blank_control_presentations': blank_result['halting_control_presentations'],
        'four_site_semantic_checks': counted_four_site['semantic_checks'],
        'cross_sparse_basis_checks': sum(x['basis_checks'] for x in cross_result['verification']['toy_sparse_compilers']),
        'four_site_sparse_basis_checks': sum(x['basis_checks'] for x in tshape_result['verification']['toy_sparse_compilers']),
        'bit_lengths_Bminus1': {'cross': 5**36, 'four_site': 5**28},
        'saved_receipts_reproduced': 4,
        'coefficients_or_giant_alphabets_materialized': False,
        'formal_status': 'Finite checks supporting the mathematical proofs; no proof-assistant build.',
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Optional path for the combined JSON receipt')
    args = parser.parse_args()
    result = verify()
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({
        'status': result['status'],
        'cross_windows': result['cross_windows'],
        'four_site_windows': result['four_site_windows'],
        'sparse_basis_checks': result['cross_sparse_basis_checks'] + result['four_site_sparse_basis_checks'],
        'mutated_periodic_planes': result['four_site_semantic_checks']['single_cell_mutated_periodic_planes'],
        'saved_receipts_reproduced': result['saved_receipts_reproduced'],
    }))

if __name__ == '__main__':
    main()
