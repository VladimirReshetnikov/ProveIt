#!/usr/bin/env python3
"""Exact normal-component and ray-certificate audit with optional Regina oracle."""

import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import platform
import random
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_packed_components import normal_packed_component_census
from fastunknot.normal_packed_verify import verify_normal_packed_certificate
from fastunknot.normal_ray_blocks import normal_ray_block_disk_count
from fastunknot.normal_ray_blocks_verify import verify_normal_ray_block_disk_certificate
from fastunknot.normal_support import compile_support
from normal_orbit_research.fixtures import (
    regina_triangulation, regina_surface, export_surface, layered_torus,
)

SEED = 2610091201


def digest(value):
    return hashlib.sha256(json.dumps(json_safe(value), sort_keys=True,
                                      separators=(',', ':')).encode()).hexdigest()


def source_hashes():
    files = sorted((ROOT/'fastunknot').glob('normal_*support*.py'))
    files += sorted((ROOT/'fastunknot').glob('normal_*packed*.py'))
    files += sorted((ROOT/'fastunknot').glob('normal_ray_blocks*.py'))
    files += [Path(__file__), Path(__file__).with_name('source_corpus.json')]
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}


def coordinate_histogram(answer):
    return Counter({tuple(v for row in item['coordinates'] for v in row): item['multiplicity']
                    for item in answer['component_histogram']})


def compatible(left, right):
    return all(sum(bool(a+b) for a, b in zip(l[4:], r[4:])) <= 1
               for l, r in zip(left, right))


def examples(record, rng):
    seen = set()
    vectors = record['vertices']
    candidates = [('zero', [[0]*7 for _ in vectors[0]])]
    candidates += [('vertex-'+str(i), v) for i, v in enumerate(vectors)]
    pairs = [(i, j) for i in range(len(vectors)) for j in range(i, len(vectors))
             if compatible(vectors[i], vectors[j])]
    rng.shuffle(pairs)
    for i, j in pairs[:12]:
        for a, b in ((1, 1), (2, 3)):
            value = [[a*x+b*y for x, y in zip(l, r)] for l, r in zip(vectors[i], vectors[j])]
            candidates.append((f'mix-{i}-{j}-{a}-{b}', value))
    for name, vector in candidates:
        key = tuple(v for row in vector for v in row)
        if key not in seen:
            seen.add(key)
            yield name, vector


def run(args):
    if args.regina_path:
        sys.path.insert(0, str(args.regina_path.resolve()))
    oracle = None
    if args.regina:
        import regina
        oracle = regina
    sources = source_hashes()
    records = json.loads(Path(__file__).with_name('source_corpus.json').read_text())['records']
    rng = random.Random(SEED)
    rows, samples = [], []
    histogram = Counter()
    replays = comparisons = geometric_oracles = 0
    start = time.perf_counter()
    for record in records:
        raw = record['triangulation']
        tri = regina_triangulation(raw) if oracle else None
        for name, vector in examples(record, rng):
            old = normal_component_census(raw, vector, mode='coordinates')
            packed = normal_packed_component_census(raw, vector, record_certificate=True)
            direct = normal_packed_component_census(raw, vector, encoding='vector', record_certificate=True)
            expected = coordinate_histogram(old)
            assert coordinate_histogram(packed) == expected == coordinate_histogram(direct)
            assert packed['compressing_disk_components'] == old['compressing_disk_components']
            assert verify_normal_packed_certificate(raw, vector, packed['certificate'])
            assert verify_normal_packed_certificate(raw, vector, direct['certificate'])
            for key in ('input_weight_runs', 'maximum_weight_runs', 'translation_pushes',
                        'reflection_pushes', 'emitted_weight_runs', 'replay_events'):
                assert packed['stats'][key] == direct['stats'][key], (record['id'], name, key)
            ray = normal_ray_block_disk_count(raw, vector, record_certificate=True)
            assert ray['status'] == 'COMPLETE'
            assert ray['compressing_disk_components'] == old['compressing_disk_components']
            assert verify_normal_ray_block_disk_certificate(raw, vector, ray['certificate'])
            replays += 3
            comparisons += 3
            regina_count = None
            if oracle:
                components = regina_surface(tri, vector).components()
                actual = Counter(tuple(v for row in export_surface(c) for v in row) for c in components)
                assert actual == expected, (record['id'], name, 'Regina coordinates')
                regina_count = sum(c.isCompressingDisc(True) for c in components)
                assert regina_count == ray['compressing_disk_components']
                geometric_oracles += 1
            dimension = packed['projection_dimension']
            types = len(expected)
            prepared = _prepare(raw, lambda: None)
            by_vertex = {}
            for t, line in enumerate(vector):
                for v in range(4):
                    root = prepared['vertex_roots'][4*t+v]
                    by_vertex.setdefault(root, []).append(line[v])
            anchors = sum(min(values) > 0 for values in by_vertex.values())
            assert types <= 2*dimension-anchors, (record['id'], name, 'profile bound')
            if oracle and all(c.isTwoSided() for c in components):
                assert types <= dimension
            summary = dict(id=record['id']+'/'+name, input_sha256=digest(vector),
                tetrahedra=len(vector), support_size=packed['support_size'], nullity=dimension,
                retained_slot_bits=packed['packed_bits'], old_weight_dimension=old['weight_dimension'],
                component_types=types, supported_vertex_links=anchors,
                components=old['components'], discs=old['compressing_disk_components'],
                ray_stats=ray['stats'], regina_discs=regina_count,
                packed_proof_sha256=digest(packed['certificate']))
            rows.append(summary)
            histogram[dimension] += 1
            if len(samples) < 10 and (not samples or dimension != samples[-1]['nullity']):
                samples.append(dict(id=summary['id'], nullity=dimension, triangulation=raw,
                    coordinates=vector, packed_certificate=packed['certificate'],
                    ray_certificate=ray['certificate']))
        print(record['id'], 'checked', len(rows), 'cases', flush=True)
    # Certificate mutations span source binding, numerical claims, topology,
    # packing and rank; every altered evidence object must be rejected.
    raw, vector = layered_torus(8)
    proof = normal_packed_component_census(raw, vector, record_certificate=True)['certificate']
    mutations = []
    for key in ('rank', 'nullity', 'denominator'):
        bad = deepcopy(proof); bad['support_kernel'][key] += 1; mutations.append(bad)
    for index in range(min(20, len(proof['support_kernel']['numerators']))):
        bad = deepcopy(proof); bad['support_kernel']['numerators'][index][0] += 1; mutations.append(bad)
    for key in ('components', 'compressing_disk_components'):
        bad = deepcopy(proof); bad['summary'][key] += 1; mutations.append(bad)
    bad = deepcopy(proof); bad['weighted_orbits']['histogram'][0]['weight'][0] += 1; mutations.append(bad)
    bad = deepcopy(proof); bad['input_sha256'] = '0'*64; mutations.append(bad)
    for bad in mutations:
        assert not verify_normal_packed_certificate(raw, vector, bad)
    assert source_hashes() == sources, 'source changed during audit'
    result = dict(schema='support-certificate-audit-v1', seed=SEED, source_sha256=sources,
        python=sys.version, platform=platform.platform(), regina_version=oracle.versionString() if oracle else None,
        cases=len(rows), triangulations=len(records), producer_comparisons=comparisons,
        certificate_replays=replays, regina_oracles=geometric_oracles,
        rejected_mutations=len(mutations), dimension_histogram=dict(sorted(histogram.items())),
        all_equal=True, seconds=time.perf_counter()-start, rows=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(result), indent=2)+'\n')
    args.output.with_name('sample_certificates.json').write_text(json.dumps(json_safe(samples), indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('rows', 'source_sha256')}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--regina', action='store_true')
    parser.add_argument('--regina-path', type=Path)
    run(parser.parse_args())
