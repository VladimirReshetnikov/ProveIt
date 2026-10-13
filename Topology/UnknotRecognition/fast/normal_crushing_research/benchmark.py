"""Whole positive queries: adaptive native discovery, standard ablation, crushing.

All arms include exterior construction, shelling, source replay, search,
independent positive replay and serialization. Only diagram objects are prepared
outside the timer. These positive fixtures support no negative runtime claim.
"""
import argparse
from hashlib import sha256
from itertools import product
import json
import platform
from pathlib import Path
from random import Random
from statistics import median
import sys
from time import perf_counter_ns

from fastunknot.diagram import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.diagram_exterior_verify import verify_diagram_exterior
from fastunknot.boundary_shellings import shell_boundary
from fastunknot.boundary_shellings_verify import verify_boundary_shellings
from fastunknot.normal_sector import build_sector_kernel, _discover_in_kernel
from fastunknot.normal_sector_verify import verify_sector_witness
from fastunknot.normal_crushing_search import recognize_by_crushing
from .fixtures import ROOT


def fixed_source_disc_query(diagram, *, adaptive):
    """Uncapped full standard-sector traversal, stopping at a certified disc.

    The principal adaptive arm retains existing matching and Q-corner preludes.
    Disabling them is a labelled ablation. Exhaustion is returned only as a
    supplied-ray-family result; all measured fixtures produce positive verdicts.
    """
    source = Diagram.from_pd(diagram.pd)
    initial = diagram_exterior(source)
    assert verify_diagram_exterior(source, initial)
    result = shell_boundary(initial)
    shelling = {key: result[key] for key in ('triangulation', 'moves')}
    current = shelling['triangulation']
    assert verify_boundary_shellings(initial, current, shelling['moves'])
    stats = dict(initial_tetrahedra=len(initial['tetrahedra']),
                 shelled_tetrahedra=len(current['tetrahedra']), sectors_attempted=0,
                 bases_attempted=0, positive_euler_rays=0)
    for assignment in product(range(3), repeat=len(current['tetrahedra'])):
        kernel = build_sector_kernel(current, list(enumerate(assignment)))
        result = _discover_in_kernel(kernel, phase='standard', corner_first=adaptive,
                                     matching_first=adaptive)
        stats['sectors_attempted'] += 1
        stats['bases_attempted'] += result['stats']['bases_attempted']
        stats['positive_euler_rays'] += result['stats']['positive_euler_rays']
        assert result['status'] != 'INCONCLUSIVE'
        if result['status'] != 'DISC_FOUND':
            continue
        certificate = dict(input_pd=[list(row) for row in source.pd],
            source_triangulation=initial, shelling=shelling, disc=result['certificate'])
        # Repeat full positive provenance as the crushing driver's final
        # independent recognition replay does after constructing its steps.
        assert verify_diagram_exterior(source, initial)
        assert verify_boundary_shellings(initial, current, shelling['moves'])
        assert verify_sector_witness(current, certificate['disc'])
        return dict(status='UNKNOT', certificate=certificate, stats=stats)
    return dict(status='NO_VERTEX_DISC', stats=stats)


def query(diagram, arm):
    if arm in ('crushing', 'crushing_canonical'):
        result = recognize_by_crushing(diagram, max_sectors=None, max_bases=None,
            max_crushes=None, sector_order='canonical' if arm == 'crushing_canonical' else 'diversified')
    else:
        result = fixed_source_disc_query(diagram, adaptive=arm == 'adaptive')
    assert result['status'] == 'UNKNOT', result
    encoded = json.dumps(result, sort_keys=True, separators=(',', ':'))
    return result['stats'], len(encoded), sha256(encoded.encode()).hexdigest()


def source_hashes():
    names = ('normal_crushing', 'normal_crushing_verify', 'normal_crushing_chain',
             'normal_crushing_search', 'normal_sector', 'normal_sector_verify',
             'normal_disk_kernel', 'normal_surface_geometry', 'source_kernel',
             'source_kernel_verify', 'diagram_exterior', 'diagram_exterior_verify',
             'boundary_shellings', 'boundary_shellings_verify')
    paths = [ROOT/'fast/fastunknot'/f'{name}.py' for name in names]
    paths.extend(sorted(Path(__file__).parent.glob('*.py')))
    return {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest() for p in paths}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--pairs', type=int, default=9)
    parser.add_argument('--aa', type=int, default=3)
    parser.add_argument('--batch', type=int, default=3)
    args = parser.parse_args()
    if min(args.pairs, args.aa, args.batch) < 1:
        parser.error('pairs, aa and batch must be positive')
    cases = [('circle', Diagram.from_pd([])), ('negative_curl', Diagram.from_braid(2, [-1]))]
    arms = ('adaptive', 'standard_ablation', 'crushing', 'crushing_canonical')
    rng = Random(11720261012)
    output = dict(passed=False, source_sha256=source_hashes(), pairs=args.pairs, aa=args.aa,
        batch=args.batch, seed=11720261012, python=sys.version, platform=platform.platform(),
        scope='two positive complete queries including construction, shelling, replay and serialization; adaptive is principal baseline; direct standard is an ablation',
        records=[])
    target = Path(args.output)
    def save():
        target.write_text(json.dumps(output, indent=2)+'\n')
    def sample(diagram, arm):
        start = perf_counter_ns()
        previous = None
        for _ in range(args.batch):
            stats, size, digest = query(diagram, arm)
            assert previous in (None, digest), 'batch outputs differ'
            previous = digest
        return dict(ns=(perf_counter_ns()-start)/args.batch, stats=stats, result_bytes=size,
                    output_sha256=digest)
    for name, diagram in cases:
        record = dict(id=name, input_pd=[list(row) for row in diagram.pd], samples=[], aa_samples=[])
        warm = {arm:query(diagram, arm)[2] for arm in arms}
        record['warmup_sha256'] = warm
        for _ in range(args.pairs):
            order = list(arms); rng.shuffle(order)
            values = {arm: sample(diagram, arm) for arm in order}
            assert all(values[arm]['output_sha256'] == warm[arm] for arm in arms)
            record['samples'].append(dict(order=order, results=values))
        for _ in range(args.aa):
            order = ['A', 'B']; rng.shuffle(order)
            values = {label: sample(diagram, 'adaptive') for label in order}
            assert all(v['output_sha256'] == warm['adaptive'] for v in values.values())
            record['aa_samples'].append(dict(order=order, results=values))
        record['median_ns'] = {arm: median(p['results'][arm]['ns'] for p in record['samples']) for arm in arms}
        record['paired_adaptive_over_crushing'] = median(
            p['results']['adaptive']['ns']/p['results']['crushing']['ns'] for p in record['samples'])
        record['paired_ablation_over_crushing'] = median(
            p['results']['standard_ablation']['ns']/p['results']['crushing']['ns'] for p in record['samples'])
        record['paired_canonical_over_crushing'] = median(
            p['results']['crushing_canonical']['ns']/p['results']['crushing']['ns'] for p in record['samples'])
        record['aa_ratio'] = median(p['results']['A']['ns']/p['results']['B']['ns'] for p in record['aa_samples'])
        output['records'].append(record)
        save()
        print(name, record['median_ns'], 'adaptive/crushing', record['paired_adaptive_over_crushing'], flush=True)
    assert output['source_sha256'] == source_hashes(), 'benchmarked source changed during the run'
    output['passed'] = True
    save()


if __name__ == '__main__':
    main()
