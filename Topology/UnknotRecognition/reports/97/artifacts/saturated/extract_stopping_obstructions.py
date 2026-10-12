"""Authenticate and classify only the eleven saved joint raw stalls.

This is a research extraction driver, not an additional recognition rule.
Source packets are regenerated and independently replayed; their canonical
JSON hashes are saved instead of duplicating the large orbit traces.
"""

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import sys
from unittest.mock import patch


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkout', type=Path, default=os.environ.get('PROVEIT_CHECKOUT'))
    parser.add_argument('--audit', type=Path, default=Path(__file__).with_name('audit.json'))
    parser.add_argument('--output', type=Path, default=Path('reproduced/saturated/stopping_obstructions.json'))
    args = parser.parse_args()
    if args.checkout is None:
        parser.error('Set PROVEIT_CHECKOUT or pass --checkout.')
    checkout = args.checkout.expanduser().resolve()
    fast = checkout / 'Topology/UnknotRecognition/fast'
    sys.path.insert(0, str(fast))
    from fastunknot.integer_codec import json_safe
    from fastunknot.normal_parallelity import normal_cut_parallelity
    from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
    from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
    from fastunknot.parallelity_boundary_words_verify import verify_parallelity_boundary_words
    from fastunknot.normal_cut_saturated import _forest, _source_rows
    from fastunknot.normal_cut_saturated_verify import _decode, _walk, _components_and_forest
    from fastunknot.core_handlebody import column_cancellation_plan
    from fastunknot.column_cancellation_verify import (
        verify_column_cancellations, verify_raw_cancellation_obstruction)

    def canonical_bytes(value):
        return (json.dumps(json_safe(value), sort_keys=True, separators=(',', ':')) + '\n').encode()

    def digest(value):
        return hashlib.sha256(canonical_bytes(value)).hexdigest()

    def independent_residual(rows):
        """Slow independent discovery with the opposite tie order."""
        active = set(rows)
        while active:
            totals = Counter()
            for r in active:
                totals.update(rows[r])
            leaves = [h for h, n in totals.items() if n == 1]
            if not leaves:
                break
            h = max(leaves)
            active.remove(next(r for r in active if rows[r].get(h, 0)))
        return sorted(active)

    corpus_path = fast / 'marked_parallelity_research/corpus.json'
    corpus_bytes = corpus_path.read_bytes()
    cases = json.loads(corpus_bytes)['cases']
    audit_bytes = args.audit.read_bytes()
    audit = json.loads(audit_bytes)
    assert hashlib.sha256(corpus_bytes).hexdigest() == audit['corpus_sha256']
    for name, expected in audit['native_changed_source_sha256'].items():
        assert hashlib.sha256((checkout / name).read_bytes()).hexdigest() == expected
    targets = {x['id'] for x in audit['cases']
               if x.get('reason') == 'saturated_raw_cancellation_stalled'}
    assert len(targets) == 11
    records, counts = [], Counter()
    for index, case in enumerate(cases):
        if case['id'] not in targets:
            continue
        tri, coordinates = case['triangulation'], case['coordinates']
        p = normal_cut_parallelity(tri, coordinates, record_certificate=True)
        b = normal_parallelity_boundary_words(tri, coordinates, record_certificate=True)
        assert p['status'] == b['status'] == 'COMPLETE'
        with patch('fastunknot.normal_parallelity.normal_cut_parallelity',
                   side_effect=AssertionError('parallelity producer invoked in replay')):
            with patch('fastunknot.parallelity_boundary_words.normal_parallelity_boundary_words',
                       side_effect=AssertionError('boundary producer invoked in replay')):
                assert verify_normal_cut_parallelity(tri, coordinates, p['certificate'])
                assert verify_parallelity_boundary_words(tri, coordinates, b['certificate'])
        g = _decode(p['certificate']['geometry'])
        summary = _decode(p['certificate']['summary'])
        skeleton = _decode(b['certificate']['skeleton'])
        core = g['core']
        forest, components = _forest(core, lambda: None)
        verified_forest = _components_and_forest(core, forest, lambda: None)
        assert verified_forest is not None and verified_forest[0] == components
        source, reason = _source_rows(g, summary, skeleton, forest, components, lambda: None)
        if source is None:
            records.append(dict(id=case['id'], unsupported_reason=reason))
            counts['unsupported'] += 1
            continue

        # Uncapped reconstruction from independently authenticated source packets.
        removed = set(forest)
        rows, labels = {}, []
        for h in core['handles2']:
            rows[h['id']] = dict(Counter(f['handle'] for f in h['cycle']
                if f['dimension'] == 1 and f['handle'] not in removed))
            labels.append(dict(row=h['id'], kind='original_core_two_handle',
                               source_two_handle=h['id']))
        old_count = len(rows)
        for s in source['saturated']:
            row = Counter()
            for a in s['annular_attachments']:
                row.update(h for h in _walk(g, skeleton['attachment_components'][a]['word'], lambda: None)
                           if h not in removed)
            rows[s['relation']] = dict(row)
            profile = summary['base_profiles'][s['base_profile']]
            labels.append(dict(row=s['relation'], kind='saturated_base',
                base_profile=s['base_profile'], annular_attachments=s['annular_attachments'],
                euler_characteristic=profile['euler_characteristic'],
                boundary_components=profile['boundary_components'],
                orientable=profile['orientable'], genus=profile['genus'],
                crosscaps=profile['crosscaps']))
        assert {r: {h: min(2, n) for h, n in row.items()} for r, row in rows.items()} == source['rows']
        joint = column_cancellation_plan(rows)
        blocked = joint['remaining_rows']
        old_rows = {r: row for r, row in rows.items() if r < old_count}
        old = column_cancellation_plan(old_rows)
        assert blocked and blocked == independent_residual(rows)
        assert old['remaining_rows'] == independent_residual(old_rows)
        assert verify_column_cancellations(rows, joint['cancellations'], complete=False)
        assert verify_raw_cancellation_obstruction(rows, blocked)
        assert verify_column_cancellations(old_rows, old['cancellations'], complete=not old['remaining_rows'])
        if old['remaining_rows']:
            assert verify_raw_cancellation_obstruction(old_rows, old['remaining_rows'])
            assert verify_raw_cancellation_obstruction(rows, old['remaining_rows'])
            assert set(old['remaining_rows']) <= set(blocked)
            classification = 'old_core_obstruction_already_present'
        else:
            classification = 'obstruction_requires_saturated_rows'
        counts[classification] += 1
        counts['source_packet_pairs_authenticated'] += 1
        counts['joint_stopping_sets_independently_verified'] += 1
        totals = Counter()
        for r in blocked:
            totals.update(rows[r])
        source_input = dict(triangulation=tri, coordinates=coordinates)
        records.append(dict(id=case['id'], corpus_index=index,
            source_input_sha256=digest(source_input),
            source_packet_sha256=dict(parallelity=digest(p['certificate']), boundary=digest(b['certificate'])),
            source_authentication='both independent replays passed with producer entrypoints disabled',
            forest=forest, columns=[h['id'] for h in core['handles1'] if h['id'] not in removed],
            row_labels=labels,
            raw_unsigned_sparse_matrix=[dict(row=r, entries=[[h, n] for h, n in sorted(row.items())])
                                        for r, row in sorted(rows.items())],
            row_counts=dict(total=len(rows), original_core=old_count, saturated=len(source['saturated']),
                stopping_total=len(blocked), stopping_original_core=sum(r < old_count for r in blocked),
                stopping_saturated=sum(r >= old_count for r in blocked)),
            joint_column_leaf_prefix=joint['cancellations'],
            canonical_joint_stopping_rows=blocked,
            stopping_column_totals=[[h, n] for h, n in sorted(totals.items())],
            old_core_column_leaf_prefix=old['cancellations'],
            canonical_old_core_stopping_rows=old['remaining_rows'],
            classification=classification,
            independent_obstruction_check='PASS',
            independent_canonical_residual_check='PASS'))
        print(json.dumps(dict(id=case['id'], classification=classification,
                              rows=len(rows), stopping_rows=blocked)), flush=True)
    assert len(records) == len(targets)
    report = dict(schema='saturated-stopping-obstructions-v1',
        repository_pin=audit['repository_pin'], corpus_sha256=hashlib.sha256(corpus_bytes).hexdigest(),
        audit_sha256=hashlib.sha256(audit_bytes).hexdigest(),
        native_source_sha256=audit['native_changed_source_sha256'],
        source_hash_encoding='SHA-256 of json_safe, sorted-key compact JSON with trailing newline, UTF-8',
        interpretation='Obstructions exclude full positive raw cancellation in the fixed source forest; they are not topological non-handlebody or nontrivial-knot certificates.',
        evidence='All source packet pairs independently replayed. Uncapped rows agree with the capped finite compiler. Every saved stopping set passes the independent obstruction checker; opposite-order peeling agrees on each canonical residual.',
        packet_storage='Full source packets are regenerated by this driver from the pinned corpus; only their exact canonical hashes are retained here.',
        counts=dict(counts), cases=records)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(report), indent=2)+'\n')
    print(json.dumps(dict(counts=counts, output=str(args.output))), flush=True)


if __name__ == '__main__':
    main()
