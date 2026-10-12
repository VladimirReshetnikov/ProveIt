"""Paired shuffled benchmarks; generation and complete positive queries separated."""
import bootstrap
from itertools import combinations
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import statistics
import time

from fastunknot.normal_weight_clusters import (
    prepare_clusters, enumerate_cluster_candidates, cluster_defect_search,
)
from fastunknot.normal_weight_defect import (
    _one_vertex_data, _build_subspace, _initial_stats, weight_subspace_rays,
    one_edge_defect_search,
)
from fastunknot.normal_surface_geometry import _coordinates
from fastunknot.normal_vertex_gate import verify_vertex_disc_certificate
from fastunknot.normal_disk_kernel import verify_normal_disk_count_certificate
from normal_orbit_research.weight_defect import layered_obstruction


def flat(rows):
    return tuple(x for row in rows for x in row)


def brute_candidates(raw, maximum=2):
    prepared, baseline = _one_vertex_data(raw, lambda: None)
    stats = _initial_stats()
    seen = set()
    accepted = {}
    edges = tuple(sorted(baseline))
    for size in range(maximum+1):
        for support in combinations(edges, size):
            subspace = _build_subspace(prepared, baseline, support, lambda: None)
            for rows in weight_subspace_rays(subspace, stats=stats, seen=seen):
                data = _coordinates(prepared, rows, lambda: None)
                delta = [data['weights'][e]-baseline[e] for e in edges]
                if (all(value >= 0 and value % 2 == 0 for value in delta)
                        and sum(value > 0 for value in delta) <= maximum):
                    accepted[flat(rows)] = rows
    return dict(status='COMPLETE', coordinates=list(accepted.values()), stats=stats)


def measure(name, arms, fixtures, rounds, rng):
    output = []
    for fixture, raw in fixtures:
        print(name, fixture, 'warmup', flush=True)
        warm = {arm: fn(raw) for arm, fn in arms.items()}
        if name == 'complete_radius_two':
            expected = {flat(x) for x in warm['all_supports']['coordinates']}
            assert expected == {flat(x) for x in warm['clusters']['coordinates']}
        else:
            assert all(r['status'] == 'DISC_FOUND' for r in warm.values())
            assert warm['one_edge']['coordinates'] == warm['clusters']['coordinates']
            assert verify_vertex_disc_certificate(raw, warm['clusters']['coordinates'],
                                                 warm['clusters']['certificate'])
            assert verify_normal_disk_count_certificate(raw, warm['one_edge']['coordinates'],
                                                        warm['one_edge']['certificate'])
        samples = {arm: [] for arm in arms}
        for round_number in range(rounds):
            order = list(arms)
            rng.shuffle(order)
            for arm in order:
                started = time.perf_counter()
                result = arms[arm](raw)
                samples[arm].append(time.perf_counter()-started)
                assert result['status'] == warm[arm]['status']
                assert result['stats'] == warm[arm]['stats']
            print(name, fixture, 'round', round_number+1, flush=True)
        output.append(dict(fixture=fixture, tetrahedra=len(raw['tetrahedra']),
            samples=samples, medians={arm: statistics.median(x) for arm, x in samples.items()},
            ranges={arm: [min(x), max(x)] for arm, x in samples.items()},
            stats={arm: x['stats'] for arm, x in warm.items()},
            candidate_count=(len(warm['clusters']['coordinates'])
                if name == 'complete_radius_two' else None),
            source_sha256=sha256(json.dumps(raw,sort_keys=True).encode()).hexdigest()))
    return output


if __name__ == '__main__':
    rng = random.Random(261012243)
    layered = [('layered_'+str(layers+8), layered_obstruction(layers)[0])
               for layers in (0, 8, 16, 32)]
    disconnected = json.loads((bootstrap.HERE/'artifacts/disconnected_disc.json').read_text())
    radius_two = measure('complete_radius_two', dict(
        all_supports=brute_candidates,
        clusters=lambda raw: enumerate_cluster_candidates(raw, max_defect=2, max_components=2)),
        layered + [('disconnected_15', disconnected['triangulation'])], 5, rng)
    positive = measure('positive_radius_one', dict(
        one_edge=one_edge_defect_search,
        clusters=lambda raw: cluster_defect_search(raw, max_defect=1, max_components=1)),
        layered, 7, rng)
    files = [Path(__file__), bootstrap.HERE/'fastunknot/normal_weight_clusters.py',
             bootstrap.HERE/'fastunknot/normal_vertex_gate.py',
             bootstrap.INCOMING/'repro/Topology/UnknotRecognition/fast/fastunknot/normal_weight_defect.py']
    result = dict(python=platform.python_version(), platform=platform.platform(),
        rounds=dict(complete_radius_two=5, positive_radius_one=7),
        warmups_per_arm_and_fixture=1, seed=261012243,
        complete_radius_two=radius_two, positive_radius_one=positive,
        files={str(path):sha256(path.read_bytes()).hexdigest() for path in files},
        scope='Complete radius-two candidate generation includes exact source/cocycle '
              'preparation, reconstruction and unsigned-defect filtering. It excludes '
              'vertex topology gates. Positive radius-one queries include their own '
              'different native component versus polynomial rank gate and independent replay. '
              'Warmup equality checks are outside timed blocks. No asymptotic law is fitted.')
    (bootstrap.HERE/'artifacts/benchmark.json').write_text(json.dumps(result,indent=2)+'\n')
    for name, entries in [('enumeration',radius_two),('positive',positive)]:
        for entry in entries:
            print(name,entry['fixture'],entry['medians'],flush=True)
