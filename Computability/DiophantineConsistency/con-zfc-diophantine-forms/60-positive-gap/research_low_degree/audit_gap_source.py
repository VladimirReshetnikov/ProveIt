#!/usr/bin/env python3
"""Independent exact polynomial audit of two positive source changes.

Only Python's standard library is required. No search or numerical
interpolation is used. Weighted records are interpreted as in the report.
"""
from collections import defaultdict
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
DATA = ROOT.parent / 'research_nine' / 'data'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def read_records(name):
    path = DATA / name
    return path, json.loads(path.read_text())


def expand_records(records):
    rows = defaultdict(lambda: defaultdict(int))
    for record in records:
        monomial = tuple(record['monomial'])
        factor = 2 if len(monomial) == 2 and monomial[0] != monomial[1] else 1
        for term in record['coefficient']:
            key = (monomial, tuple(term['powers']))
            rows[record['row']][key] += factor * term['coefficient']
    return {row: {key: value for key, value in poly.items() if value}
            for row, poly in rows.items()}


def substitute(rows, images):
    """Images are exact affine polynomials as {monomial: integer} maps."""
    result = {}
    for row, polynomial in rows.items():
        output = defaultdict(int)
        for (monomial, ports), coefficient in polynomial.items():
            terms = {(): coefficient}
            for index in monomial:
                image = images.get(index, {(index,): 1})
                new_terms = defaultdict(int)
                for old_mon, old_coefficient in terms.items():
                    for new_mon, new_coefficient in image.items():
                        key = tuple(sorted(old_mon + new_mon))
                        new_terms[key] += old_coefficient * new_coefficient
                terms = dict(new_terms)
            for mon, value in terms.items():
                output[(mon, ports)] += value
        result[row] = {key: value for key, value in output.items() if value}
    return result


def quadratic_records(polynomials):
    return {row: {key: value for key, value in poly.items() if len(key[0]) == 2}
            for row, poly in polynomials.items()}


def main():
    old_path, old = read_records('reconstructed_records.json')
    gap_path, gap = read_records('positive_gap_records.json')
    shifted_path, shifted = read_records('positive_gap_shift_records.json')
    old_pol, gap_pol, shifted_pol = map(expand_records, (old, gap, shifted))
    for row, polynomial in old_pol.items():
        if row not in (7, 8):
            need(all(11 not in mon and 18 not in mon for mon, ports in polynomial),
                 'P or tau is used outside the two isolated rows')
    gap_images = {18: {(18,): 1, (12,): 1, (13,): 1},
                  11: {(18,): 1, (11,): 1}}
    need(substitute(old_pol, gap_images) == gap_pol, 'Gap substitution failed')
    square_images = {24: {(24,): 1, (): -1}}
    need(substitute(gap_pol, square_images) == shifted_pol, 'Square shift failed')
    need(quadratic_records(gap_pol) == quadratic_records(shifted_pol),
         'Quadratic records changed under square shift')
    need((len(old), len(gap), len(shifted)) == (89, 87, 86), 'Wrong record counts')
    changed_rows = [row for row in sorted(gap_pol) if gap_pol[row] != shifted_pol[row]]
    need(changed_rows == [1, 2, 14], 'Unexpected changed rows')
    need(all(len(mon) <= 2 for poly in shifted_pol.values() for mon, ports in poly),
         'A row is no longer quadratic')
    receipt = {
        'status': 'PASS',
        'record_counts': [89, 87, 86],
        'positive_coordinates': 31,
        'equations': 22,
        'exact_gap_substitution': True,
        'exact_square_register_substitution': True,
        'quadratic_records_unchanged_by_square_shift': True,
        'square_shift_changed_rows': changed_rows,
        'checks_are_exact': True,
        'files': [{'path': str(path.relative_to(ROOT.parent)),
                   'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                  for path in (old_path, gap_path, shifted_path)],
        'proof_boundary': 'Local identities and unbounded positivity proof only; inherited compiler and final Jones bridge not reverified.'
    }
    (ROOT / 'gap_source_audit.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
