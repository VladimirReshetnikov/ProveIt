"""Run from repository root: algebraic template feasibility, not a certificate.

Append candidate standard base-boundary rows to the real source core rows.
Genus columns and bridge columns that can never be singleton pivots are omitted.
The missing source-to-template gluing theorem and independent replay are NOT
provided here. This diagnostic must not supply any topological verdict.
"""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'fast'))
from fastunknot.core_handlebody import _forest, _occurrences, leaf_cancellation_plan, capped_cancellation_plan
from fastunknot.disk_bundle_absorption import source_core_circle
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from normal_orbit_research.seeds import sources

pins = sources()
audit = json.loads((ROOT / 'synthesis/data/core-annuli-audit.json').read_text())
selected = {c['id']: c for c in audit['cases'] if c['native_status'] != 'COMPLETE'
            and c['native_reason'] != 'core_has_three_handles'}
bank = json.loads((ROOT / 'fast/marked_parallelity_research/corpus.json').read_text())['cases']
records = []
for case in bank:
    if case['id'] not in selected:
        continue
    p = normal_cut_parallelity(case['triangulation'], case['coordinates'])
    b = normal_parallelity_boundary_words(case['triangulation'], case['coordinates'])
    g, profiles = p['geometry'], p['summary']['base_profiles']
    owner = {port: i for i, profile in enumerate(profiles) for port in profile['core_ports']}
    tree, _ = _forest(g['core'], lambda: None)
    counts = _occurrences(g['core'], tree, lambda: None)
    forest = set(tree)
    families = {}
    for index, a in enumerate(b['skeleton']['attachment_components']):
        if a['kind'] != 'circle':
            continue
        crossings, _ = source_core_circle(g, a['word'])
        row_id = len(g['core']['handles2']) + index
        row = {}
        for x in crossings:
            h = x['handle']
            if h not in forest:
                row[h] = min(2, row.get(h, 0) + 1)
        counts[row_id] = row
        base = owner[abs(a['word'][0]) - 1]
        families.setdefault(base, []).append(row_id)
    next_column = len(g['core']['handles1'])
    family_records = []
    for base, rows in sorted(families.items()):
        profile = profiles[base]
        a, boundary = len(rows), profile['boundary_components']
        assert 0 < a <= boundary and profile['multiplicity'] == 1
        dedicated = a if a < boundary else a - 1
        columns = list(range(next_column, next_column + dedicated))
        next_column += dedicated
        for r, h in zip(rows, columns):
            counts[r][h] = 1
        if a == boundary:
            for h in columns:
                counts[rows[-1]][h] = 1
        bulk = 1 - profile['euler_characteristic'] - dedicated
        assert bulk >= 0
        family_records.append(dict(base_profile=base, circles=a, boundary=boundary,
                                   finite_columns=columns, omitted_genus_columns=bulk))
    plan = leaf_cancellation_plan(counts)
    method = 'leaf'
    if plan['remaining_rows']:
        plan = capped_cancellation_plan(counts)
        method = 'capped'
    records.append(dict(id=case['id'], original_reason=selected[case['id']]['native_reason'],
                        rows=len(counts), added_boundary_columns=next_column-len(g['core']['handles1']),
                        families=family_records, all_rows_removed=not plan['remaining_rows'],
                        method=method, remaining_rows=plan['remaining_rows'],
                        oracle_histogram=selected[case['id']]['regina'].get('histogram')))
assert sources() == pins
report = dict(scope='Algebraic boundary-template diagnostic only; no topology certificate',
              native_source_sha256=pins, cases=records,
              all_rows_removed=sum(c['all_rows_removed'] for c in records))
Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2)+'\n')
for c in records:
    print(c['id'], c['all_rows_removed'], c['remaining_rows'])
