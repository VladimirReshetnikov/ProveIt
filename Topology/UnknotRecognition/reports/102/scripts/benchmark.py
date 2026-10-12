"""Paired matrix-kernel measurements, not end-to-end knot recognition."""
import csv
import hashlib
from datetime import datetime, timezone
import json
import platform
import statistics
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from cancellation import column_cancellation_plan, verify_peeling_certificate
from reference.native_planner_excerpt import capped_cancellation_plan, leaf_cancellation_plan


def old_pipeline(counts):
    result = leaf_cancellation_plan(counts)
    return capped_cancellation_plan(counts) if result['remaining_rows'] else result


def proposed_pipeline(counts):
    result = leaf_cancellation_plan(counts)
    return column_cancellation_plan(counts) if result['remaining_rows'] else result


def new_query(counts):
    plan = column_cancellation_plan(counts)
    certificate = dict(schema='positive-column-peeling-v1',
                       cancellations=plan['cancellations'], remaining_rows=plan['remaining_rows'])
    assert verify_peeling_certificate(counts, certificate)
    # Include portable evidence serialization; statistics are deliberately excluded.
    evidence = json.dumps(certificate, sort_keys=True, separators=(',', ':'))
    return plan, len(evidence.encode())


def measure(fn, source, repeats, loops):
    samples = []
    for _ in range(repeats):
        start = time.perf_counter_ns()
        for __ in range(loops):
            result = fn(source)
        samples.append((time.perf_counter_ns()-start) / (1e6*loops))
    return samples


def run():
    cases = []
    for m in [1, 8, 64, 256, 1024]:
        cases.append(('private_plus_common', m, {r: {r: 1, m: 1} for r in range(m)}))
    for m in [1, 64, 1024]:
        cases.append(('identity', m, {r: {r: 1} for r in range(m)}))
    for m in [8, 64, 256]:
        cases.append(('cycle_stopping', m, {r: {r: 1, (r+1) % m: 1} for r in range(m)}))
    cases.append(('unit_column', 1, {0: {0: 1}}))
    records = []
    for name, size, counts in cases:
        old, new = old_pipeline(counts), column_cancellation_plan(counts)
        assert bool(old['remaining_rows']) == bool(new['remaining_rows'])
        loops = 100 if size <= 8 else 1
        # Interleave arms within each round to reduce drift. Retain every sample.
        samples = {'old_producer': [], 'new_producer': [], 'new_query': [], 'proposed_producer': []}
        arms = [('old_producer', old_pipeline), ('new_producer', column_cancellation_plan),
                ('new_query', new_query), ('proposed_producer', proposed_pipeline)]
        for round_no in range(7):
            order = arms if round_no % 2 == 0 else list(reversed(arms))
            for key, fn in order:
                samples[key] += measure(fn, counts, 1, loops)
        medians = {key: statistics.median(values) for key, values in samples.items()}
        record = dict(family=name, rows=size, nonzeros=sum(map(len, counts.values())),
                      full_success=not new['remaining_rows'], samples_ms=samples,
                      median_ms=medians,
                      producer_speedup=medians['old_producer']/medians['new_producer'],
                      proposed_speedup=medians['old_producer']/medians['proposed_producer'],
                      proof_bytes=new_query(counts)[1], old_stats=old['stats'], new_stats=new['stats'])
        records.append(record)
        print(name, size, medians, record['producer_speedup'], flush=True)
    source_hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                     for folder in ['cancellation', 'reference']
                     for p in (ROOT/folder).glob('*.py')}
    data = dict(source_sha256=source_hashes, recorded_utc=datetime.now(timezone.utc).isoformat(), scope='matrix producers and new independently verified/serialized matrix query',
                caveat='NO source geometry extraction, NO native full knot benchmark',
                python=sys.version, platform=platform.platform(), rounds=7,
                timer='perf_counter_ns', records=records)
    (ROOT/'results'/'benchmarks.json').write_text(json.dumps(data, indent=2)+'\n')
    with (ROOT/'results'/'benchmarks.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['family','rows','nonzeros','old_producer_ms','new_producer_ms',
                         'new_verified_serialized_query_ms','producer_speedup','proof_bytes',
                         'proposed_producer_ms','proposed_speedup'])
        for r in records:
            d = r['median_ms']
            writer.writerow([r['family'],r['rows'],r['nonzeros'],d['old_producer'],
                             d['new_producer'],d['new_query'],r['producer_speedup'],r['proof_bytes'],
                             d['proposed_producer'],r['proposed_speedup']])
    tex = [r'\begin{tabular}{lrrrrr}', r'\toprule',
           r'Family & $m$ & Old prod. & Proposed & New query & Ratio\\', r'\midrule']
    for r in records:
        d = r['median_ms']
        label = {'private_plus_common':'Private + common', 'identity':'Identity',
                 'cycle_stopping':'Stopping cycle', 'unit_column':'Single unit'}[r['family']]
        tex.append(f"{label} & {r['rows']} & {d['old_producer']:.4f} & {d['proposed_producer']:.4f} & "
                   f"{d['new_query']:.4f} & {r['proposed_speedup']:.2f}$\\times$\\\\")
    tex += [r'\bottomrule', r'\end{tabular}']
    (ROOT/'article'/'benchmark_table.tex').write_text('\n'.join(tex)+'\n')
    highlight = next(r for r in records if r['family']=='private_plus_common' and r['rows']==1024)
    med = highlight['median_ms']
    macros = (f"\\newcommand{{\\BenchOld}}{{{med['old_producer']:.3f}}}\n"
              f"\\newcommand{{\\BenchProposed}}{{{med['proposed_producer']:.3f}}}\n"
              f"\\newcommand{{\\BenchRatio}}{{{highlight['proposed_speedup']:.0f}}}\n")
    (ROOT/'article'/'benchmark_macros.tex').write_text(macros)



if __name__ == '__main__':
    run()
