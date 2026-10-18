#!/usr/bin/env python3
"""Cross-check the loop driver against the independent source catalogue.

Also apply its DBM projector to deliberately nonidentity copy rows justified
by exact equalities in the independently checked original DBM certificate.
These controls check permutation direction and signs. They do not certify
any altered binary table or rerun a fold journal.
"""
from __future__ import annotations

import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'loop_experiments'))
import affine_reference_loops as driver
from countdown_loops import Source, PROG, catalogue


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('loop_projection_audit.json'))
    args = parser.parse_args()
    source = Source(PROG.read_bytes())
    independent, _ = catalogue(source)
    independent = {record['head_site']: record for record in independent}
    sites, cases, targets, first, decode, path_index, loops, rejected = driver.control_data()
    assert not rejected and set(loops) == set(independent)
    for site, record in loops.items():
        original = independent[site]
        assert record['path'] == original['head_path']
        assert record['counter'] == original['counter']
        assert record['body_sites'] == original['body_sites']
        assert record['body_increments'] == original['increments_per_positive_cycle']
        assert record['cycle_source_steps'] == original['positive_cycle_source_steps']
        assert record['cycle_gap_increment'] == original['positive_cycle_gap_increment']
        assert record['exit_gap_increment'] == original['zero_exit_gap_increment']
        assert record['exit_pc'].rstrip('0') == original['zero_exit_normalized_pc']
        assert record['exit_site'] == original['zero_exit_site']

    data_path = ROOT / 'proof_audit/relational_dbm_threshold2.json'
    data = json.loads(data_path.read_bytes())
    convert, zone, evidence = driver.dbm_projector()
    _, constraints, enabled, _ = driver.base.configure(64)
    identity = [tuple(int(i == j) for j in range(9)) + (0,) for i in range(9)]
    examples, kinds, checked, seen = [], Counter(), 0, set()
    for case_index, (site, _, _, _, _) in enumerate(cases):
        if not enabled[case_index]:
            continue
        bounds = constraints[case_index]
        roots, _ = zone(site, bounds)
        class_id = data['site_class_ids'][site]
        flat = data['invariant_classes'][class_id]
        for logical_a in range(9):
            for logical_b in range(9):
                if logical_a == logical_b:
                    continue
                a, b = logical_a + 1, logical_b + 1
                difference = flat[10*a+b]
                opposite = flat[10*b+a]
                if difference == data['infinity_sentinel'] or opposite == data['infinity_sentinel']:
                    continue
                if difference + opposite != 0:
                    continue
                kind = 'fixed_class' if roots[a] == 0 else 'free_class'
                signature = logical_a, logical_b, difference, kind
                if signature in seen:
                    continue
                seen.add(signature)
                physical_a = driver.c.PHYS[logical_a]
                physical_b = driver.c.PHYS[logical_b]
                rows = identity.copy()
                # The independent DBM fact is Ra-Rb=difference. Copy Rb+7
                # into Ra, preserving every other physical register.
                rows[physical_a] = tuple(int(j == physical_b) for j in range(9)) + (7,)
                expected = [0] * 9
                expected[physical_a] = 7 - difference
                actual = convert(rows, bounds, site)
                assert actual == tuple(expected), (case_index, signature, actual, expected)
                kinds[kind + '_difference_' + str(difference)] += 1
                checked += 1
                if len(examples) < 12 or kind == 'free_class' and not any(e['kind'] == kind for e in examples):
                    examples.append({'case': case_index, 'site': site,
                                     'logical_copy': [logical_a, logical_b],
                                     'physical_copy': [physical_a, physical_b],
                                     'known_original_difference': difference,
                                     'resulting_target_offset': 7-difference, 'kind': kind})
    assert checked > 0 and any(k.startswith('free_class_') for k in kinds)
    result = {
        'status': 'PASS independent catalogue comparison and signed permutation controls',
        'loop_catalogue_entries_compared': len(loops),
        'exact_equality_projection_controls': checked,
        'projection_control_kinds': dict(sorted(kinds.items())),
        'examples': examples,
        'driver_sha256': sha256(Path(driver.__file__).read_bytes()).hexdigest(),
        'checker_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'dbm_sha256': sha256(data_path.read_bytes()).hexdigest(),
        'scope': __doc__,
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('examples', 'scope')}, indent=2))


if __name__ == '__main__':
    main()
