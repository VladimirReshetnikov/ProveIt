#!/usr/bin/env python3
"""Combine complete modular zero lists into a finite nonvanishing certificate.
Run from the archive root. This checks existing logs; rerun verify_modular to
independently reproduce the recurrence computations that generated those logs.
"""
from __future__ import annotations
import argparse
import csv
import json
from pathlib import Path


def load_csv(path: Path) -> list[dict[str, int]]:
    with path.open(newline='') as source:
        return [{k: int(v) for k, v in row.items()} for row in csv.DictReader(source)]


def upper_bound(n: int) -> int:
    return ((n * n + 2 * n + 2) // 2 if n % 2 == 0
            else (n * n + 2 * n + 1) // 2 - (n + 1) // 8)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-dir', type=Path, default=Path('data'))
    args = parser.parse_args()
    moduli = (1000000007, 1000000009)
    zero_sets, counts, witnesses = [], [], []
    for p in moduli:
        prefix = args.data_dir / f'p{p}'
        zero_rows = load_csv(Path(str(prefix) + '_zeros.csv'))
        zero_set = {(r['n'], r['k'], r['j']) for r in zero_rows}
        assert len(zero_set) == len(zero_rows), 'Duplicate zero coordinate'
        zero_sets.append(zero_set)
        count_rows = load_csv(Path(str(prefix) + '_counts.csv'))
        assert [r['n'] for r in count_rows] == list(range(len(count_rows)))
        for row in count_rows:
            n = row['n']
            assert row['modulus'] == p
            assert row['potential_cells'] - row['forced_zero_cells'] == upper_bound(n)
            assert row['nonzero_residues'] + row['extra_modular_zeros'] == upper_bound(n)
            assert row['extra_modular_zeros'] == sum(t[0] == n for t in zero_set)
        counts.append(count_rows)
        watch_rows = load_csv(Path(str(prefix) + '_watches.csv'))
        witnesses.append({(r['n'], r['k'], r['j']): r['residue'] for r in watch_rows})
    assert len(counts[0]) == len(counts[1]), 'Ranges differ'
    intersection = zero_sets[0] & zero_sets[1]
    assert not intersection, f'Unresolved candidates: {sorted(intersection)}'
    all_exceptions = sorted(zero_sets[0] | zero_sets[1])
    with (args.data_dir / 'modular_witnesses.csv').open('w', newline='') as out:
        writer = csv.writer(out)
        writer.writerow(['n', 'k', 'j', 'residue_mod_1000000007', 'residue_mod_1000000009'])
        for coord in all_exceptions:
            residues = [w[coord] for w in witnesses]
            assert any(residues)
            for i, p in enumerate(moduli):
                assert (residues[i] == 0) == (coord in zero_sets[i])
                assert 0 <= residues[i] < p
            writer.writerow([*coord, *residues])
    with (args.data_dir / 'certified_counts.csv').open('w', newline='') as out:
        writer = csv.writer(out)
        writer.writerow(['n', 'certified_term_count'])
        for row in counts[0]:
            writer.writerow([row['n'], upper_bound(row['n'])])
    max_n = len(counts[0]) - 1
    report = {
        'certified_range': [0, max_n],
        'moduli': list(moduli),
        'unpredicted_zero_residues_by_modulus': [len(s) for s in zero_sets],
        'intersection_of_unpredicted_zero_sets': [],
        'potential_cells_per_modulus': sum(r['potential_cells'] for r in counts[0]),
        'all_unpredicted_modular_zeros_have_nonzero_other_modulus_witness': True,
        'conclusion': f'a(n) equals U(n) for every integer 0 <= n <= {max_n}',
        'qualification': 'Combines exact modular arithmetic with the proved forced-zero identities; not a proof for all n.'
    }
    (args.data_dir / 'certificate_summary.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
