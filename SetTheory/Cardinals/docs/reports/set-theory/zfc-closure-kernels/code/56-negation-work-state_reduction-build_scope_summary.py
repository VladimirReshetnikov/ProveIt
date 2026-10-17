#!/usr/bin/env python3
"""Recompute exact search-scope accounting from archived and fresh evidence."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    archived_path = HERE / 'source50_degree2.json'
    archived = json.loads(archived_path.read_text())
    audit_path = HERE / 'degree2_partition_audit.json'
    audit = json.loads(audit_path.read_text())
    assert audit['status'] == 'PASS' and audit['total_remaining'] == 0
    old = {g['deleted_state']: g for g in archived['groups']}
    fresh = {int(p.name.split('_')[2]): (p, json.loads(p.read_text()))
             for p in HERE.glob('two_action_*_gap.json')}
    assert set(fresh) == {q for q, g in old.items() if g['pruned'] < g['planned']}
    audited = {g['deleted_state']: g for g in audit['results']}
    assert set(audited) == set(fresh)
    for q, (path, result) in fresh.items():
        assert result['status'] == 'completed'
        assert result['remaining'] == 0 and result['pruned'] == 1008 ** 2
        assert not result['survivors']
        assert result['incoming'] == old[q]['incoming_rows']
        assert audited[q]['result_sha256'] == sha(path)
        assert audited[q]['pruned'] == result['pruned']
    full_old = sorted(q for q in old if old[q]['pruned'] == old[q]['planned'])
    overlap = sum(old[q]['pruned'] for q in fresh)
    fresh_recipes = sum(d['planned'] for _, d in fresh.values())
    newly_covered = fresh_recipes - overlap
    full_combined = sum(g['planned'] for g in old.values())
    assert archived['pruned'] + newly_covered == full_combined == 46 * 1008 ** 2
    uniform = []
    names = ['gap_fold', 'action_fold', 'phase_action_fold',
             'quotient_action_fold', 'ranked_fold']
    for name in names:
        p = HERE / (name + '_results.json')
        d = json.loads(p.read_text())
        assert d['status'] == 'completed'
        assert d['completed_recipes'] == d['planned_recipes'] == 55471
        assert not d['affine_survivors'] and not d['whole_boot_survivors']
        baseline = next(k for k in d if k.startswith('baseline') and 'boot' not in k)
        uniform.append(dict(name=name, recipes=55471, completed_affine_diagnostics=d['affine_checks'],
                            baseline_suite=baseline, fuel=d['affine_fuel'], survivors=0,
                            result=p.name, sha256=sha(p)))
    box = json.loads((HERE / 'box_mixed_results.json').read_text())
    box_affine = json.loads((HERE / 'box_mixed_affine_results.json').read_text())
    box_gap = json.loads((HERE / 'box_mixed_gap_affine_results.json').read_text())
    assert len(box['survivors']) == 1821
    assert not box_affine['survivors'] and not box_gap['survivors']
    output = dict(
        status='PASS',
        scope='Finite diagnostics and exact coverage accounting. No smaller machine, semantic lower bound, or new kernel equivalence theorem is claimed.',
        pinned_repository_commit='43026ff42f0939f09b9e95495248cfadcad38e38',
        two_incoming_full_action=dict(
            domain='Delete one eligible nonprotected state with two external incoming rows; independently choose write, direction, and surviving target or halt at each incoming row; preserve all other retained rows.',
            actions_per_row=1008, recipes_per_deleted_state=1008 ** 2,
            all_deleted_states=sorted(old), archival_completed_deleted_states=full_old,
            archival_completed_domains=len(full_old),
            archival_partial_domains=[dict(state=q, pruned=g['pruned'], remaining=g['planned']-g['pruned'])
                                      for q, g in old.items() if 0 < g['pruned'] < g['planned']],
            archival_total_pruned=archived['pruned'],
            fresh_completed_deleted_states=sorted(fresh), fresh_completed_domains=len(fresh),
            fresh_audited_recipe_count=fresh_recipes,
            overlap_with_archived_partial_coverage=overlap,
            additional_distinct_recipes=newly_covered,
            combined_distinct_recipes=full_combined, combined_remaining=0, survivors=0,
            fresh_evaluated_lazy_nodes=sum(d['evaluated_nodes'] for _, d in fresh.values()),
            fresh_completed_affine_diagnostics=sum(d['checks'] for _, d in fresh.values()),
            fresh_elapsed_seconds_sum=sum(d['elapsed_seconds'] for _, d in fresh.values()),
            fresh_contract='Canonical logical successor and register effect, full exterior/frame, arbitrary output gap >= 40; 1000 affine-rule fuel.',
            archival_contract='Exact successor frame with original affine gap; 1000 affine-rule fuel.',
            combined_claim='All 46,738,944 recipes fail the exact finite source-50 contract. The 36 fresh domains additionally fail the weaker output-gap contract. The ten archived complete domains were not rerun under the weaker contract.',
            independent_audit='Replays every fresh lazy branch, weighted pruning subtree, and final frontier; does not independently rerun each affine failure.',
            audit_file=audit_path.name, audit_sha256=sha(audit_path),
            archival_result_file=archived_path.name, archival_result_sha256=sha(archived_path),
            audit_repair='State 215 initially had an incomplete journal tail (10,810 lines versus 11,089 reported nodes). The entire domain was rerun; the replacement 11,089-line journal passed the independent audit. This repeated domain contributes no additional unique coverage.'),
        uniform_deletion_contracts=dict(
            eligible_deleted_states=221, targets_per_deleted_state=251,
            distinct_recipes_per_contract=55471, runs=uniform,
            overlap_note='These are the same 55,471 concrete uniform recipes under five different sufficient contracts; counts must not be added as unique recipes.'),
        protected_box_mixed_rows=dict(
            recipes=box['recipes_checked'], baseline_finite_samples=box['baseline_samples'],
            literal_sample_executions=box['samples_checked'], finite_sample_survivors=len(box['survivors']),
            conditional_exact_runtime_survivors=0, conditional_gap_runtime_survivors=0,
            caveat='The altered Box routines were sampled, not proved for arbitrary registers. Their conditional affine screen nevertheless yielded no survivor.'),
        across_family_overlap='The full-action, uniform-fold, and mixed-row families may intersect. No overall unique recipe total across these families is asserted.'
    )
    path = HERE / 'scope_summary.json'
    path.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({k: output['two_incoming_full_action'][k]
                      for k in ('fresh_audited_recipe_count', 'additional_distinct_recipes',
                                'combined_distinct_recipes', 'fresh_evaluated_lazy_nodes',
                                'fresh_completed_affine_diagnostics')}))


if __name__ == '__main__':
    main()
