"""Native sector comparisons, preserving independent geometric replay."""
from itertools import product
import sys

from .common import (Source, Prepared, IntrinsicPrepared, compile_two_block,
                     matching, euler, extreme_witness, verify_vector, save, source_hashes)
from experiments.oracle import all_rays, positive
from fastunknot.normal_sector import build_sector_kernel, sector_rays
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.normal_disk_kernel import normal_compressing_disk_count, verify_normal_disk_count_certificate
from sector_envelope_research.fixtures import capped_fibonacci


def anchors(prepared):
    groups = {}
    for corner, root in enumerate(prepared['vertex_roots']):
        t, v = divmod(corner, 4)
        groups.setdefault(root, []).append(7*t+v)
    return tuple(product(*groups.values()))


def sector_source(tri, support):
    source = matching(tri)
    allowed = {7*t+4+q for t, q in support}
    zeros = tuple(7*t+4+q for t in range(len(tri['tetrahedra'])) for q in range(3)
                  if 7*t+4+q not in allowed)
    eq = source.equations+tuple(tuple(int(j==z) for j in range(source.n)) for z in zeros)
    return Source(source.n, eq, source.conflicts), zeros


def checked_candidate(tri, prepared, source, cost, x, zeros):
    w = extreme_witness(source, x, cost)
    x = w['coordinates']
    assert verify_vector(source.n, source.equations, source.conflicts, cost, x,
                         zeros=zeros, extreme=True)
    rows = [list(x[i:i+7]) for i in range(0, len(x), 7)]
    analysed = _coordinates(prepared, rows, lambda: None)
    assert analysed['euler_characteristic'] == sum(a*b for a, b in zip(cost, x))
    packet = normal_compressing_disk_count(tri, rows, record_certificate=True)
    assert packet['status'] == 'COMPLETE'
    assert verify_normal_disk_count_certificate(tri, rows, packet['certificate'])
    return dict(coordinates=x, disk_certificate=packet['certificate'],
                contains_compressing_disk=packet['contains_compressing_disk'])


def workload(tri, support, arm):
    """Full supplied-sector Euler query batch, including positive geometry replay.

    No timings exclude preparation. Seven anchor queries on the two-tet
    fixture each kill all vertex links. Native standard enumeration therefore
    has the same positive-query contract as the report-backed atlases.
    """
    prepared = _prepare(tri, lambda: None)
    source, forbidden = sector_source(tri, support)
    cost = euler(tri)
    query_zeros = anchors(prepared)
    stats = {}
    if arm == 'native':
        kernel = build_sector_kernel(tri, support)
        rays = [tuple(v for row in rows for v in row) for rows in sector_rays(kernel, stats=stats)]
        atlas = compilation = None
        stats = dict(stats, matching_nullity=len(kernel.basis))
    else:
        compilation = compile_two_block(source, range(source.n-7))
        atlas = (IntrinsicPrepared if arm=='intrinsic' else Prepared)(compilation.blocks, ray_method='zeros')
        stats = dict((atlas.prepared if arm=='intrinsic' else atlas).stats)
        stats['port_dimension'] = compilation.blocks[0].d
        if arm == 'intrinsic':
            stats.update(intrinsic_dimension=atlas.reduction.dimension,
                         local_nullities=atlas.reduction.original_nullities,
                         restricted_nullities=atlas.reduction.restricted_nullities)
    answers = []
    for zz in query_zeros:
        if arm == 'native':
            x = positive(rays, cost, zz)
        else:
            c, master, zeros = compilation.query(cost, zz)
            result = atlas.solve(c, master=master, zeros=zeros)
            x = compilation.reconstruct(result['vectors']) if result['status']=='POSITIVE' else None
        certificate = checked_candidate(tri, prepared, source, cost, x, zz) if x is not None else None
        answers.append(dict(zeros=zz, positive=x is not None, certificate=certificate))
    return dict(stats=stats, answers=answers, forbidden=forbidden)


def cases():
    # Exhaust all 16 compatible supports of the two-tetrahedron source.
    tri = capped_fibonacci(1)['triangulation']
    result = [dict(id='two_tet_'+str(i), triangulation=tri,
                   support=tuple((t, q) for t, q in enumerate(types) if q>=0))
              for i, types in enumerate(product((-1, 0, 1, 2), repeat=2))]
    # Low-nullity longer regions, without enumerating all their sectors.
    for n in (2, 4):
        for cap in range(3):
            f = capped_fibonacci(n, cap)
            result.append(dict(id=f'capped_{n}_{cap}', triangulation=f['triangulation'],
                               support=f['allowed_types']))
    return result


def main():
    report = dict(passed=False, source_sha256=source_hashes(), records=[],
                  scope='supplied finite solid-torus triangulations; no knot-diagram provenance')
    full_rays = {}
    for case in cases():
        tri = case['triangulation']
        results = {arm:workload(tri, case['support'], arm) for arm in ('native', 'delivered', 'intrinsic')}
        target = [a['positive'] for a in results['native']['answers']]
        for result in results.values():
            assert [a['positive'] for a in result['answers']] == target
        independent = False
        if len(tri['tetrahedra']) == 2:
            if not full_rays:
                source = matching(tri)
                full_rays['two'] = all_rays(source.n, source.equations, source.conflicts)
            expected = [bool(positive(full_rays['two'], euler(tri),
                            tuple(a['zeros'])+tuple(results['native']['forbidden'])))
                        for a in results['native']['answers']]
            assert expected == target
            independent = True
        report['records'].append(dict(**case, results=results, independent_source_oracle=independent))
        save(sys.argv[1], report)
        print(case['id'], sum(target), '/', len(target),
              'dimension', results['intrinsic']['stats']['intrinsic_dimension'], flush=True)
    report['passed'] = True
    save(sys.argv[1], report)


if __name__ == '__main__':
    main()
