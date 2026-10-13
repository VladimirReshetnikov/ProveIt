"""Deterministic source relabelling search for missed fixed-forest core proofs.

Source preparation is used during search; each saved positive is subsequently
authenticated with the full parallelity certificate and both core checkers.
No time in this search is reported as a benchmark.
"""
import hashlib
import json
from pathlib import Path
import random
import sys
from native_probe import (ROOT, cases, instance, solve, native_proposal,
                         select_core_forest, core_handlebody_certificate,
                         reduce_core_three_handles, replay_core_three_handles,
                         verify_core_handlebody_certificate, normal_cut_parallelity,
                         verify_normal_cut_parallelity)
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from tests.test_normal_components import relabel


def main():
    out = Path(sys.argv[1])
    rng = random.Random(115260012)
    wanted = ('interior_loop/empty', 'interior_loop/boundary_link',
              'nested_1_4_4/empty', 'nested_1_4_6/empty',
              'pilot/finite_trefoil_interior/0', 'finite_figureEight_interior/vertex134')
    report = dict(seed=115260012, passed=False, records=[], hits=[],
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for case in (c for c in cases() if c['id'] in wanted):
        for i in range(30):
            raw, coords = relabel(case['triangulation'], case['coordinates'], rng)
            source = _prepare(raw, lambda: None)
            geometry = _parallelity_geometry(source, _coordinates(source, coords, lambda: None), lambda: None)
            for mode in ('source', 'max_passages', 'deferred'):
                forest = select_core_forest(geometry['core'], strategy='source' if mode == 'deferred' else mode)
                old, proof = reduce_core_three_handles(geometry, strategy='max_weight', lower_forest=forest)
                before = core_handlebody_certificate(old['core'], forest=None if mode == 'deferred' else forest,
                                                     defer_forest=mode == 'deferred')
                row = dict(id=case['id'], relabelling=i, mode=mode, before=before['status'])
                if before['status'] != 'COMPLETE':
                    inst = instance(geometry, [] if mode == 'deferred' else forest, proof['dual_endpoints'])
                    answer = solve(inst, seed=115260012, max_b=20, max_transitions=100000)
                    row.update(after=answer['status'], route=answer.get('route'), reason=answer.get('reason'))
                    if answer['status'] == 'SUCCESS':
                        parallel = normal_cut_parallelity(raw, coords, record_certificate=True)
                        assert verify_normal_cut_parallelity(raw, coords, parallel['certificate'])
                        assert parallel['geometry'] == geometry
                        proposal = native_proposal(inst, answer['certificate'],
                            [h['id'] for h in geometry['core']['handles3']], proof['dual_endpoints'])
                        reduced = replay_core_three_handles(geometry, proposal)
                        assert reduced is not None
                        after = core_handlebody_certificate(reduced['core'], forest=None if mode == 'deferred' else forest,
                                                            defer_forest=mode == 'deferred')
                        assert after['status'] == 'COMPLETE'
                        assert verify_core_handlebody_certificate(reduced['core'], after['certificate'])
                        report['hits'].append(dict(row, triangulation=raw, coordinates=coords, core=after['certificate'],
                                                   reduction=proposal, local=answer))
                report['records'].append(row)
            print(case['id'], i, 'hits', len(report['hits']), flush=True)
            out.write_text(json.dumps(report, indent=2)+'\n')
    report['passed'] = True
    out.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
