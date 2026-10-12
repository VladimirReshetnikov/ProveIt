"""Separate report 110 review on authenticated bare native cores.

No production imports or checkers are changed. This measures abstract optimal
residuals after the fixed maximum-weight top reduction, before any lower forest.
It does not execute passive geometric transport or certify a residual manifold.
"""
from collections import Counter
from itertools import combinations
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'fast'))
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_parallelity_reference import _reference_parallelity
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.core_three_handle_reduction import reduce_core_three_handles
from fastunknot.core_three_handle_reduction_verify import replay_core_three_handles
from normal_orbit_research.seeds import sources


def peel(rows, live):
    """Direct column-sum oracle, without the native or delivered leaf queue."""
    live = set(live)
    columns = {c for r in live for c in rows[r]}
    while live:
        owner = None
        for c in sorted(columns):
            if sum(rows[r].get(c, 0) for r in live) == 1:
                owner = next(r for r in live if rows[r].get(c, 0)); break
        if owner is None:
            break
        live.remove(owner)
    return live


def main():
    pins = sources(); counts = Counter(); records = []
    report_dir = ROOT / 'reports/110'
    with tempfile.TemporaryDirectory(prefix='pivot-width-native-') as temp:
        shutil.copytree(report_dir / 'pivotwidth', Path(temp) / 'pivotwidth')
        sys.path.insert(0, temp)
        from pivotwidth.core import Instance, min_fill_decomposition
        from pivotwidth.preprocess import peel_then_optimize
        from pivotwidth.verify import replay
        cases = [c for name in ('corpus.json', 'three_handle_corpus.json') for c in
                 json.loads((ROOT / 'fast/marked_parallelity_research' / name).read_text())['cases']]
        for case in cases:
            prepared = _prepare(case['triangulation'], lambda: None)
            normal = _coordinates(prepared, case['coordinates'], lambda: None)
            geometry = _parallelity_geometry(prepared, normal, lambda: None)
            assert geometry == _reference_parallelity(prepared, normal, lambda: None)
            reduced, top_proof = reduce_core_three_handles(geometry, strategy='max_weight')
            assert replay_core_three_handles(geometry, top_proof) == reduced
            core = reduced['core']
            columns = [h['id'] for h in core['handles1']]
            rows = [dict(Counter(f['handle'] for f in h['cycle'] if f['dimension'] == 1))
                    for h in core['handles2']]
            matrix = [[row.get(c, 0) for c in columns] for row in rows]
            inst = Instance.from_dense(matrix, columns=len(columns))
            live = sorted(peel(rows, range(len(rows))))
            rec = dict(id=case['id'], rows=len(rows), columns=len(columns),
                       prepeeled=len(rows)-len(live), residual_rows=len(live))
            if live:
                cc = sorted({c for r in live for c in rows[r]})
                residual = Instance.from_dense([[rows[r].get(c, 0) for c in cc] for r in live])
                decomp = min_fill_decomposition(residual); decomp.validate(residual)
                rec['heuristic_residual_width'] = decomp.width
                if decomp.width > 5:
                    counts['width_refusal'] += 1; rec['status'] = 'WIDTH_REFUSAL'
                    records.append(rec); continue
            plan = peel_then_optimize(inst, state_limit=25000)
            checked = replay(matrix, [1]*len(rows), plan, columns=len(columns))
            assert checked['valid']
            rec.update(status='MATRIX_PLAN', plan=plan)
            counts['matrix_plans'] += 1
            if not live:
                assert plan['deferred_weight'] == 0 and plan['stats']['peak_states'] == 0
                counts['full_prepeeling'] += 1
            else:
                # Exhaust every smaller deferred set directly, independently of DP.
                assert len(live) <= 20
                optimum = None; trials = 0
                for k in range(len(live)+1):
                    for deferred in combinations(live, k):
                        trials += 1
                        if not peel(rows, set(live)-set(deferred)):
                            optimum = k; break
                    if optimum is not None: break
                assert optimum == plan['deferred_weight']
                rec.update(exhaustive_optimum=optimum, exhaustive_subsets=trials,
                           source_row_ids=[h['id'] for h in core['handles2']],
                           source_column_ids=columns, matrix=matrix,
                           top_certificate=top_proof)
                counts['nonzero_residual_optima'] += 1
                print({k:v for k,v in rec.items() if k not in ('plan','matrix','top_certificate')}, flush=True)
            records.append(rec)
    assert sources() == pins
    result = dict(scope=__doc__, native_source_sha256=pins,
                  driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  delivered_source_sha256={str(p.relative_to(report_dir)):hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in sorted((report_dir/'pivotwidth').glob('*.py'))},
                  limits=dict(max_residual_width=5, state_limit=25000, max_exhaustive_rows=20),
                  counts=dict(counts), cases=records)
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
    print(dict(counts), flush=True)


if __name__ == '__main__': main()
