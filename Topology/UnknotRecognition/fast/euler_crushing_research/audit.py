"""Fresh Regina standard-vertex audit of LP positivity and full-source crushing.

Run from fast/: python -B -m euler_crushing_research.audit --output PATH
Regina is required only for this research oracle, never for native replay.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import regina

from fastunknot.integer_codec import json_safe
from fastunknot.normal_euler import decide_sector_euler
from fastunknot.normal_euler_verify import verify_sector_euler_certificate
from fastunknot.normal_sector import build_sector_kernel, sector_rays
from fastunknot.normal_sector_verify import verify_sector_exhaustion
from fastunknot.normal_surface_geometry import _coordinates
from fastunknot.positive_ray import extract_positive_ray
from fastunknot.normal_crushing import crush_normal_ray
from fastunknot.normal_crushing_verify import verify_normal_crushing
from normal_crushing_research.fixtures import regina_triangulation, coordinates
from normal_crushing_research.oracle import inspect, support_rank
from .fixtures import ROOT, cases, nonextreme_control


def source_hashes():
    modules = ('exact_lp', 'normal_euler', 'normal_euler_verify', 'positive_ray',
               'source_kernel', 'source_kernel_verify', 'port_subspace',
               'normal_sector', 'normal_sector_verify', 'sector_euler',
               'normal_surface_geometry', 'integer_codec',
               'normal_crushing', 'normal_crushing_verify')
    paths = [ROOT/'fast/fastunknot'/f'{name}.py' for name in modules]
    paths.extend(sorted(Path(__file__).parent.glob('*.py')))
    paths.extend(ROOT/'fast'/relative for relative in (
        'projective_port_research/native.py', 'projective_port_research/common.py',
        'sector_envelope_research/fixtures.py', 'normal_orbit_research/fixtures.py',
        'normal_crushing_research/fixtures.py', 'normal_crushing_research/oracle.py'))
    return {str(path.relative_to(ROOT)): sha256(path.read_bytes()).hexdigest() for path in paths}


def digest(source):
    return sha256(json.dumps(source, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def fresh_standard_vertices(source):
    """Enumerate the original standard cone; do not use native Q parameters."""
    triangulation = regina_triangulation(source)
    assert triangulation.isValid() and triangulation.isOrientable()
    surfaces = regina.NormalSurfaces(triangulation, regina.NormalCoords.Standard,
                                     regina.NormalList.Vertex)
    vertices = []
    for i, surface in enumerate(surfaces):
        rows = coordinates(surface, triangulation)
        vertices.append(dict(index=i, coordinates=rows,
            euler_characteristic=int(str(surface.eulerChar())),
            vertex_link=surface.isVertexLinking(), connected=surface.isConnected(),
            quad_support=[[t, q] for t, row in enumerate(rows) for q in range(3) if row[4+q]]))
    return dict(triangulation=source, standard_vertex_count=len(vertices), vertices=vertices)


def target_vertices(oracle, support):
    allowed = set(map(tuple, support))
    return [vertex['index'] for vertex in oracle['vertices']
            if vertex['euler_characteristic'] > 0 and not vertex['vertex_link']
            and vertex['quad_support']
            and all(tuple(q) in allowed for q in vertex['quad_support'])]


def verified_crush(source, rows):
    oracle = inspect(source, rows)
    assert oracle['eligible'] and oracle['support_nullity'] == 1
    result = crush_normal_ray(source, rows)
    assert result['status'] == 'COMPLETE'
    proof = result['certificate']
    assert verify_normal_crushing(source, proof)
    for actual, reference in (('triangulation', 'quotient'), ('components', 'components'),
                              ('torus_component', 'torus_component'), ('successor', 'successor')):
        assert proof[actual] == oracle[reference], (actual, source, rows)
    return dict(native=result, regina=oracle)


def corner_query(source, support):
    """Q search stops at its first positive; negatives retain full-scope replay."""
    kernel = build_sector_kernel(source, support)
    stats = dict(kernel.stats)
    transcript = []
    for rows in sector_rays(kernel, phase='quadrilateral', stats=stats):
        chi = _coordinates(kernel.prepared, rows, lambda: None)['euler_characteristic']
        transcript.append(dict(quadrilaterals=[rows[t][4+q] for t, q in kernel.support],
                               euler_characteristic=chi))
        if chi > 0:
            return dict(status='POSITIVE_EULER', coordinates=rows, stats=stats,
                        examined_rays=transcript, crushing=verified_crush(source, rows))
    certificate = dict(schema='normal-sector-exhaustion-v1', source_sha256=digest(source),
        allowed_types=[list(x) for x in kernel.support], phase='quadrilateral',
        status='NO_POSITIVE_EULER', rays=transcript)
    assert verify_sector_exhaustion(source, certificate)
    return dict(status='NO_POSITIVE_EULER', stats=stats, certificate=certificate)


def compare_case(case, oracle):
    source, support = case['triangulation'], case['support']
    targets = target_vertices(oracle, support)
    expected = bool(targets)
    corner = corner_query(source, support)
    assert (corner['status'] == 'POSITIVE_EULER') == expected, case['id']
    results = {}
    for strategy in ('anchors', 'envelope'):
        result = decide_sector_euler(source, support, strategy=strategy)
        assert result['status'] in ('POSITIVE_EULER', 'NO_POSITIVE_EULER'), case['id']
        assert verify_sector_euler_certificate(source, result['certificate']), case['id']
        assert (result['status'] == 'POSITIVE_EULER') == expected, case['id']
        record = dict(result=result)
        if expected:
            extracted = extract_positive_ray(source, result['coordinates'])
            record.update(extraction=extracted,
                          crushing=verified_crush(source, extracted['coordinates']))
        results[strategy] = record
    return dict(**case, source_sha256=digest(source), oracle_positive=expected,
                oracle_positive_vertex_indices=targets, corner=corner, results=results)


def control_record():
    control = nonextreme_control()
    source, rows = control['triangulation'], control['coordinates']
    source_regina = regina_triangulation(source)
    surface = regina.NormalSurface(source_regina, regina.NormalCoords.Standard,
                                  [x for row in rows for x in row])
    size, rank, divisor = support_rank(source_regina, rows)
    assert size-rank == 2 and divisor == 1 and surface.eulerChar() == 1
    try:
        crush_normal_ray(source, rows)
    except ValueError as error:
        rejected = str(error)
    else:
        raise AssertionError('nonextreme control was accepted without support extraction')
    extraction = extract_positive_ray(source, rows)
    assert extraction['stats']['descent_steps'] == 1
    return dict(**control, input_regina=dict(positive_support=size, exact_support_rank=rank,
                support_nullity=size-rank, divisor=divisor,
                euler_characteristic=int(str(surface.eulerChar())),
                connected=surface.isConnected(), vertex_link=surface.isVertexLinking()),
                direct_crushing_rejection=rejected, extraction=extraction,
                crushing=verified_crush(source, extraction['coordinates']))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    output = dict(passed=False, regina=regina.versionString(), source_sha256=source_hashes(),
        scope='supplied finite solid-torus sectors, not knot-diagram provenance or a complexity bound',
        standard_vertex_oracles={}, records=[], nonextreme_control=None)
    path = Path(args.output)
    def save():
        path.write_text(json.dumps(json_safe(output), indent=2)+'\n')
    counts = Counter()
    for case in cases():
        key = digest(case['triangulation'])
        if key not in output['standard_vertex_oracles']:
            output['standard_vertex_oracles'][key] = fresh_standard_vertices(case['triangulation'])
        record = compare_case(case, output['standard_vertex_oracles'][key])
        output['records'].append(record)
        counts['positive' if record['oracle_positive'] else 'negative'] += 1
        counts['lp_positive' if record['oracle_positive'] else 'lp_negative'] += 2
        counts['labelled_quotient_comparisons'] += 3 if record['oracle_positive'] else 0
        save()
        print(case['id'], record['corner']['status'],
              {strategy:record['results'][strategy]['result']['stats']['lp_pivots']
               for strategy in ('anchors', 'envelope')}, flush=True)
    output['nonextreme_control'] = control_record()
    counts['labelled_quotient_comparisons'] += 1
    output.update(counts=dict(counts), unique_sources=len(output['standard_vertex_oracles']),
                  original_standard_vertices=sum(value['standard_vertex_count']
                      for value in output['standard_vertex_oracles'].values()))
    assert output['source_sha256'] == source_hashes(), 'audited source changed during the run'
    output['passed'] = True
    save()
    print(json.dumps(dict(passed=True, counts=counts, unique_sources=output['unique_sources'],
                         original_standard_vertices=output['original_standard_vertices'], output=str(path))))


if __name__ == '__main__':
    main()
