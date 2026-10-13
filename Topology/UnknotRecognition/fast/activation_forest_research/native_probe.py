"""Review report 115 on authenticated native cores, without changing runtime.

The first two modes freeze a lower forest before selecting a dual forest.
The third selects against all columns, then uses the maintained deferred
lower-forest theorem. All successes are replayed from geometric source charts.
This is a core-only audit, not a whole-cut or knot decision.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT/'fast'), str(ROOT/'reports/115')]
from activation_forest import solve, verify_obstruction
from activation_forest.closure import Activation
from integration.records_adapter import from_native_records, native_proposal
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
from fastunknot.core_three_handle_reduction import reduce_core_three_handles
from fastunknot.core_three_handle_reduction_verify import replay_core_three_handles
from fastunknot.core_handlebody import select_core_forest, core_handlebody_certificate
from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate


def cases():
    answer = [c for name in ('corpus.json', 'three_handle_corpus.json')
              for c in json.loads((ROOT/'fast/marked_parallelity_research'/name).read_text())['cases']]
    added = json.loads((ROOT/'fast/signed_annulus_research/corpus.json').read_text())
    return answer + added['cases'] + added['refusals']


def instance(geometry, forest, records):
    counts = {}
    forbidden = set(forest)
    for row in geometry['core']['handles2']:
        counts[row['id']] = dict(Counter(flag['handle'] for flag in row['cycle']
                                        if flag['dimension'] == 1 and flag['handle'] not in forbidden))
    return from_native_records(counts, [h['id'] for h in geometry['core']['handles3']], records)[0]


def main():
    out = Path(sys.argv[1])
    report = dict(scope=__doc__, passed=False, records=[],
                  caps=dict(max_b=20, max_transitions=100000, rounds=8), seed=11520261012,
                  source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                    for folder in ('fast/fastunknot', 'reports/115/activation_forest', 'reports/115/integration')
                    for p in sorted((ROOT/folder).glob('*.py'))})
    for case in cases():
        parallel = normal_cut_parallelity(case['triangulation'], case['coordinates'], record_certificate=True)
        assert parallel['status'] == 'COMPLETE'
        assert verify_normal_cut_parallelity(case['triangulation'], case['coordinates'], parallel['certificate'])
        geometry = parallel['geometry']
        three = [h['id'] for h in geometry['core']['handles3']]
        row = dict(id=case['id'], three_handles=len(three), modes=[])
        for mode in ('source', 'max_passages', 'deferred'):
            forest = select_core_forest(geometry['core'], strategy='source' if mode == 'deferred' else mode)
            incumbent, proof = reduce_core_three_handles(geometry, strategy='max_weight', lower_forest=forest)
            assert replay_core_three_handles(geometry, proof) == incumbent
            before = core_handlebody_certificate(incumbent['core'], forest=None if mode == 'deferred' else forest,
                                                 defer_forest=mode == 'deferred')
            inst = instance(geometry, [] if mode == 'deferred' else forest, proof['dual_endpoints'])
            activation = Activation(inst)
            answer = solve(inst, seed=report['seed'], max_b=20, max_transitions=100000, try_incumbent=True)
            trial = dict(mode=mode, rows=inst.m, columns=inst.columns, b=activation.b,
                         q=len(activation.mandatory), rank=inst.vertices-1,
                         before=before['status'], status=answer['status'], route=answer.get('route'),
                         reason=answer.get('reason'), stats=answer['stats'], input_sha256=inst.digest())
            if answer['status'] == 'SUCCESS':
                proposal = native_proposal(inst, answer['certificate'], three, proof['dual_endpoints'])
                reduced = replay_core_three_handles(geometry, proposal)
                assert reduced is not None
                after = core_handlebody_certificate(reduced['core'], forest=None if mode == 'deferred' else forest,
                                                    defer_forest=mode == 'deferred')
                assert after['status'] == 'COMPLETE', (case['id'], mode, after)
                assert verify_core_handlebody_certificate(reduced['core'], after['certificate'])
                trial.update(replayed=True, tree=answer['certificate']['tree'], core=after['certificate'],
                             reduction=proposal, local_certificate=answer['certificate'])
            elif answer['status'] == 'BLOCKED_EXACT':
                assert verify_obstruction(inst, answer['obstruction'])
                trial.update(obstruction=answer['obstruction'], obstruction_replayed=True)
            row['modes'].append(trial)
        report['records'].append(row)
        print(len(report['records']), row['id'], [(x['mode'], x['b'], x['before'], x['status']) for x in row['modes']], flush=True)
        out.write_text(json.dumps(report, indent=2)+'\n')
    report.update(passed=True, cases=len(report['records']))
    out.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
