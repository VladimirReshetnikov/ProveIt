"""Paired source-core benchmark for repeated scanning and the rooted queue.

Run with --output PATH. Regina constructs genuine triangulations by interior
1-4 moves. Source geometry is constructed and independently authenticated once
per case, outside scheduler timers. Both schedules are independently replayed.
The separate source-incidence and combined-stage timings expose common costs;
none of these measurements is a whole-unknot-recognizer benchmark.
"""

import argparse
from datetime import datetime, timezone
import gc
import hashlib
import json
import math
from pathlib import Path
import platform
import random
import statistics
import sys
import time


FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))

from fastunknot.core_top_reduction import rooted_top_plan, source_core_top_incidence
from fastunknot.core_top_reduction_verify import replay_core_top_reduction
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
from normal_orbit_research.fixtures import (
    export_triangulation, layered_torus, regina_triangulation,
)


def diagnostic_repeated_scan(three_count, contacts):
    """Faithful full-scan loop from synthesis/data/core-three-handle-probe.py.

    Its compact contact lists omit exterior endpoints and preserve duplicates.
    The final output normalization is done by callers, outside this timer.
    The queue includes its own survivor output, so this omission favors scan.
    """
    alive = set(range(three_count))
    remaining = set(contacts)
    moves = []
    while alive:
        choices = [(e, [v for v in contacts[e] if v in alive]) for e in sorted(remaining)]
        choices = [(e, v[0]) for e, v in choices if len(v) == 1]
        if not choices:
            raise ArithmeticError('the source diagnostic scan unexpectedly stalled')
        e, v = choices[0]
        remaining.remove(e)
        alive.remove(v)
        moves.append(dict(two_handle=e, three_handle=v))
    return moves, remaining


def compact_contacts(incidence):
    return {h['id']: [v for v in h['ends'] if v is not None]
            for h in incidence['two_handles']}


def normalize_scan(result):
    moves, remaining = result
    return ([[m['two_handle'], m['three_handle']] for m in moves], sorted(remaining))


def proof_for(incidence, moves, remaining):
    return dict(schema='normal-core-top-reduction-v1',
                input_sha256=incidence['input_sha256'], moves=moves,
                surviving_two_handles=remaining)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                     separators=(',', ':')).encode()).hexdigest()


def time_batch(call, iterations):
    enabled = gc.isenabled()
    gc.disable()
    try:
        started = time.perf_counter_ns()
        for _ in range(iterations):
            result = call()
        elapsed = time.perf_counter_ns() - started
    finally:
        if enabled:
            gc.enable()
    return elapsed / iterations, elapsed, result


def calibrated_iterations(call, target_ns):
    # Two untimed warmups and a small pilot. Calibration is not a sample.
    call()
    call()
    per_call, _, _ = time_batch(call, 3)
    return max(1, min(2048, math.ceil(target_ns / max(1, per_call))))


def summary(values):
    quartiles = statistics.quantiles(values, n=4, method='inclusive')
    return dict(median_ns=statistics.median(values), q1_ns=quartiles[0],
                q3_ns=quartiles[2], minimum_ns=min(values), maximum_ns=max(values))


def paired_samples(left, right, samples, randomizer, target_ns):
    calls = {'left': left, 'right': right}
    batches = {label: calibrated_iterations(call, target_ns) for label, call in calls.items()}
    records = []
    for sample in range(samples):
        order = ['left', 'right']
        randomizer.shuffle(order)
        measured = {}
        for label in order:
            per_call, elapsed, _ = time_batch(calls[label], batches[label])
            measured[label] = dict(per_call_ns=per_call, batch_ns=elapsed)
        records.append(dict(sample=sample, order=order, **measured))
    left_values = [r['left']['per_call_ns'] for r in records]
    right_values = [r['right']['per_call_ns'] for r in records]
    return dict(iterations_per_batch=batches, raw_samples=records,
                left=summary(left_values), right=summary(right_values),
                median_of_paired_ratios=statistics.median(a/b for a, b in zip(left_values, right_values)),
                ratio_of_medians=statistics.median(left_values)/statistics.median(right_values))


def source_case(interior_vertices):
    """Create a genuine solid torus with nested interior source vertices."""
    raw, _ = layered_torus(1)
    triangulation = regina_triangulation(raw)
    operations = []
    for _ in range(interior_vertices):
        tetrahedron = min(triangulation.tetrahedra(), key=lambda t:
            (sum(t.vertex(v).isBoundary() for v in range(4)), t.index()))
        operations.append(tetrahedron.index())
        if not triangulation.pachner(tetrahedron):
            raise ArithmeticError('an interior 1-4 move failed')
    return triangulation, operations


def benchmark_case(q, args, randomizer):
    start = time.perf_counter_ns()
    triangulation, operations = source_case(q)
    raw = export_triangulation(triangulation)
    rows = [[0]*7 for _ in raw['tetrahedra']]
    constructed = time.perf_counter_ns()
    parallelity = normal_cut_parallelity(raw, rows, record_certificate=True)
    assert parallelity['status'] == 'COMPLETE'
    geometry = parallelity['geometry']
    assert verify_normal_cut_parallelity(raw, rows, parallelity['certificate'])
    authenticated = time.perf_counter_ns()
    incidence = source_core_top_incidence(raw, rows, geometry)
    packet_hash = digest(incidence)
    geometry_hash = digest(geometry)
    contacts = compact_contacts(incidence)
    three_count = len(incidence['three_handles'])
    two_count = len(incidence['two_handles'])
    assert three_count == q
    assert len(raw['tetrahedra']) == 1+3*q
    assert two_count == 4*q

    old_call = lambda: diagnostic_repeated_scan(three_count, contacts)
    new_call = lambda: rooted_top_plan(incidence)
    old_moves, old_remaining = normalize_scan(old_call())
    new_moves, new_remaining, queue_stats = new_call()
    old_proof = proof_for(incidence, old_moves, old_remaining)
    new_proof = proof_for(incidence, new_moves, new_remaining)
    replay_started = time.perf_counter_ns()
    assert replay_core_top_reduction(raw, rows, geometry, old_proof) is not None
    old_replay_ns = time.perf_counter_ns()-replay_started
    replay_started = time.perf_counter_ns()
    assert replay_core_top_reduction(raw, rows, geometry, new_proof) is not None
    new_replay_ns = time.perf_counter_ns()-replay_started

    # Count the old loop's exact work without instrumenting its timing path.
    endpoint_total = sum(len(value) for value in contacts.values())
    edge_total = two_count
    old_endpoint_tests = old_row_visits = 0
    for edge, _ in old_moves:
        old_row_visits += edge_total
        old_endpoint_tests += endpoint_total
        edge_total -= 1
        endpoint_total -= len(contacts[edge])
    assert old_row_visits == q*two_count-q*(q-1)//2
    assert queue_stats['incidence_visits'] <= 2*two_count
    queue_endpoint_bound = (4*two_count + 2*queue_stats['queue_pops'] +
                            2*queue_stats['incidence_visits'])

    gc.collect()
    target_ns = args.target_ms*1_000_000
    scheduler = paired_samples(old_call, new_call, args.samples, randomizer, target_ns)
    # Identical queue calls with independently calibrated batches are an A/A
    # control for order effects and short-call measurement noise.
    aa = paired_samples(new_call, new_call, args.samples, randomizer, target_ns)

    reconstruct = lambda: source_core_top_incidence(raw, rows, geometry)
    source_batch = calibrated_iterations(reconstruct, target_ns)
    source_samples = []
    for _ in range(args.stage_samples):
        per_call, elapsed, _ = time_batch(reconstruct, source_batch)
        source_samples.append(dict(per_call_ns=per_call, batch_ns=elapsed))

    def common_plus_scan():
        packet = reconstruct()
        return diagnostic_repeated_scan(len(packet['three_handles']), compact_contacts(packet))

    def common_plus_queue():
        return rooted_top_plan(reconstruct())

    combined = paired_samples(common_plus_scan, common_plus_queue,
                               args.stage_samples, randomizer, target_ns)
    assert digest(incidence) == packet_hash
    assert digest(geometry) == geometry_hash
    return dict(interior_vertices=q, tetrahedra=len(raw['tetrahedra']),
        core_handle_counts=[len(geometry['core'][f'handles{i}']) for i in range(4)],
        source_triangulation=raw, normal_coordinates=rows,
        source_sha256=digest(raw), geometry_sha256=geometry_hash,
        endpoint_packet_sha256=packet_hash, source_move_tetrahedra=operations,
        source_construction_ns=constructed-start,
        parallelity_construction_and_independent_authentication_ns=authenticated-constructed,
        source_geometry_authenticated=True,
        proof_replays=dict(scan=True, queue=True, scan_ns=old_replay_ns, queue_ns=new_replay_ns),
        scan_proof=old_proof, queue_proof=new_proof,
        moves_identical=old_moves == new_moves,
        survivors_identical=old_remaining == new_remaining,
        work_counts=dict(scan_row_visits=old_row_visits,
            scan_endpoint_membership_tests=old_endpoint_tests,
            scan_row_formula='q*m - q*(q-1)/2 = (7*q*q+q)/2',
            queue=queue_stats, queue_endpoint_inspections_upper_bound=queue_endpoint_bound,
            queue_bound_formula='4*m + 2*queue_pops + 2*incidence_visits'),
        scheduler=dict(left_label='faithful repeated scan', right_label='rooted queue', **scheduler),
        aa_control=dict(left_label='rooted queue A', right_label='rooted queue B', **aa),
        shared_incidence_reconstruction=dict(iterations_per_batch=source_batch,
            raw_samples=source_samples,
            **summary([r['per_call_ns'] for r in source_samples])),
        source_incidence_plus_schedule=dict(left_label='common source incidence + scan',
            right_label='common source incidence + queue', **combined))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--sizes', type=int, nargs='+', default=[1, 4, 16, 64, 128, 256])
    parser.add_argument('--samples', type=int, default=9)
    parser.add_argument('--stage-samples', type=int, default=5)
    parser.add_argument('--target-ms', type=float, default=5.0)
    parser.add_argument('--seed', type=int, default=2610122349)
    args = parser.parse_args()
    if (min(args.sizes) < 1 or min(args.samples, args.stage_samples) < 3 or
            args.target_ms <= 0):
        parser.error('positive sizes/target and at least three samples are required')
    import regina
    sources = [Path(__file__), FAST/'fastunknot/core_top_reduction.py',
               FAST/'fastunknot/core_top_reduction_verify.py',
               FAST/'fastunknot/normal_parallelity.py',
               FAST/'fastunknot/normal_parallelity_verify.py',
               FAST/'fastunknot/normal_parallelity_geometry.py',
               FAST/'fastunknot/normal_parallelity_reference.py',
               FAST/'fastunknot/normal_surface_geometry.py',
               FAST/'normal_orbit_research/fixtures.py',
               FAST.parent/'synthesis/data/core-three-handle-probe.py']
    hashes = {str(path.relative_to(FAST.parent)): hashlib.sha256(path.read_bytes()).hexdigest()
              for path in sources}
    randomizer = random.Random(args.seed)
    report = dict(schema='core-top-scheduler-benchmark-v1',
        started_utc=datetime.now(timezone.utc).isoformat(), python=sys.version,
        platform=platform.platform(), regina=regina.versionString(),
        seed=args.seed, samples=args.samples, stage_samples=args.stage_samples,
        target_batch_ms=args.target_ms, clock='time.perf_counter_ns',
        gc_policy='disabled only inside timed batches; restored after each batch',
        source_sha256=hashes,
        scope='Local 2/3 scheduler and shared source-incidence stage only; no full recognizer speed claim.',
        methods=dict(source='q 1-4 moves, choosing least (boundary corner count, tetrahedron ID)',
            ordering='independently randomized order within every timed pair',
            batching='per-method pilot calibration; at most 2048 calls per batch',
            geometry='constructed and independently source-authenticated once per case, outside timings',
            scan='original full sorted scan and full candidate-list filtering; exterior endpoints omitted',
            normalization='scan output normalization excluded; queue survivor output and counters included',
            combined='both rebuild the same source endpoint packet; scan then drops exterior markers',
            limitations='shared-host Python timings; geometric construction, source-proof authentication and terminal recognition excluded'),
        cases=[])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for q in args.sizes:
        record = benchmark_case(q, args, randomizer)
        report['cases'].append(record)
        args.output.write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps(dict(q=q, tetrahedra=record['tetrahedra'],
            scan_ns=record['scheduler']['left']['median_ns'],
            queue_ns=record['scheduler']['right']['median_ns'],
            scheduler_ratio=record['scheduler']['ratio_of_medians'],
            aa_ratio=record['aa_control']['ratio_of_medians'],
            combined_ratio=record['source_incidence_plus_schedule']['ratio_of_medians'],
            scan_endpoint_tests=record['work_counts']['scan_endpoint_membership_tests'],
            queue_incidence_visits=record['work_counts']['queue']['incidence_visits'])), flush=True)
    report['finished_utc'] = datetime.now(timezone.utc).isoformat()
    report['totals'] = dict(cases=len(report['cases']),
                            independent_top_replays=2*len(report['cases']),
                            authenticated_source_geometries=len(report['cases']))
    args.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
