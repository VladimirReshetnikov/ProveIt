"""Exhaustive finite audits, independently computed from the proved calculus."""
import json
import platform
import sys
import time
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from cancellation import column_cancellation_plan, verify_peeling_certificate, replay_positive, deferred_plan
from reference.native_planner_excerpt import capped_cancellation_plan
from scripts.oracles import sparse, pivot, max_pivots, permanent_one_minor, stopping_subsets


def run():
    started = time.perf_counter()
    records = []
    for m, n, alphabet in [(0, 0, 3), (1, 3, 3), (2, 2, 3), (2, 3, 3),
                            (2, 4, 3), (3, 2, 3), (3, 3, 3), (3, 4, 2)]:
        total = success = 0
        for entries in product(range(alphabet), repeat=m*n):
            a = tuple(tuple(entries[r*n:(r+1)*n]) for r in range(m))
            counts = sparse(a)
            plan = column_cancellation_plan(counts)
            won = not plan['remaining_rows']
            exhaustive = max_pivots(a) == m
            minor = permanent_one_minor(a)
            baseline = capped_cancellation_plan(counts)
            assert won == exhaustive == minor == (not baseline['remaining_rows']), a
            if won:
                assert baseline['stats']['entry_updates'] == 0, a
            cert = dict(schema='positive-column-peeling-v1',
                        cancellations=plan['cancellations'], remaining_rows=plan['remaining_rows'])
            assert verify_peeling_certificate(counts, cert), a
            assert replay_positive(counts, plan['cancellations']) is not None, a
            sets = stopping_subsets(a)
            union = set().union(*(set(s) for s in sets))
            assert union == set(plan['remaining_rows']), a
            total += 1
            success += won
        records.append(dict(rows=m, columns=n, alphabet=alphabet,
                            matrices=total, full_success=success))
        print(records[-1], flush=True)
    # Explicit invariant: every stopping set survives every eligible first pivot.
    invariant_cases = 0
    for entries in product(range(3), repeat=6):
        a = (entries[:3], entries[3:])
        for selected in stopping_subsets(a):
            for r in range(2):
                for c in range(3):
                    if a[r][c] != 1:
                        continue
                    b = pivot(a, r, c)
                    remaining = [i for i in selected if i != r]
                    assert remaining, (a, selected, r, c)
                    mapping = {old: new for new, old in enumerate(i for i in range(2) if i != r)}
                    selected_b = [mapping[i] for i in remaining]
                    assert all(sum(b[i][j] for i in selected_b) != 1 for j in range(2))
                    invariant_cases += 1
    # Maximum partial length = rows - minimum deferral; compare exact DFS.
    deferred_cases = 0
    for m, n, alphabet in [(2, 3, 3), (3, 3, 2)]:
        for entries in product(range(alphabet), repeat=m*n):
            a = tuple(tuple(entries[r*n:(r+1)*n]) for r in range(m))
            result = deferred_plan(sparse(a), m)
            assert result['status'] == 'FOUND'
            assert m-len(result['deferred_rows']) == max_pivots(a), a
            assert result['residual'] == replay_positive(sparse(a), result['cancellations']), a
            deferred_cases += 1
    report = dict(status='PASS', python=sys.version, platform=platform.platform(),
                  exhaustive=records, matrices=sum(r['matrices'] for r in records),
                  stopping_invariance_cases=invariant_cases, optimal_deferral_cases=deferred_cases,
                  dfs_cache=str(max_pivots.cache_info()), elapsed_seconds=time.perf_counter()-started,
                  native_full_knot_benchmarks='NOT_RUN',
                  comparison_scope='transcribed pinned native planner functions; matrix kernels only')
    (ROOT/'results'/'exhaustive_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    run()
