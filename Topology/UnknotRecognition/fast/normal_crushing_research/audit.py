"""Compare maintained crushing and replay against independently enumerated fixtures.

Run from fast/: python -B -m normal_crushing_research.audit --output PATH
Regina is an oracle and fixture discovery dependency, not a maintained verifier dependency.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import regina

from fastunknot.normal_crushing import crush_normal_ray
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_crushing_chain import make_crushing_chain, verify_crushing_chain
from fastunknot.normal_disk_kernel import normal_compressing_disk_count, verify_normal_disk_count_certificate
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from fastunknot.diagram_exterior_verify import verify_diagram_exterior
from fastunknot.boundary_shellings_verify import verify_boundary_shellings
from .fixtures import (ROOT, RETAINED, retained_cases, expanded_cases,
    isolated_cycle_case, one_tetrahedron_cases, diagram_cases, regina_triangulation)
from .oracle import inspect


def source_hashes():
    modules = ('normal_crushing', 'normal_crushing_verify', 'normal_crushing_chain',
               'normal_surface_geometry', 'normal_surface_orbits', 'normal_surface_verify',
               'normal_disk_kernel', 'source_kernel', 'source_kernel_verify', 'port_subspace',
               'diagram_exterior', 'diagram_exterior_verify', 'boundary_shellings',
               'boundary_shellings_verify')
    paths = [ROOT/'fast/fastunknot'/f'{name}.py' for name in modules]
    paths.extend(sorted(Path(__file__).parent.glob('*.py')))
    paths.append(RETAINED)
    return {str(path.relative_to(ROOT)): sha256(path.read_bytes()).hexdigest() for path in paths}


def compare(case):
    source, rows = case['source'], case['coordinates']
    oracle = inspect(source, rows)
    result = dict(case, oracle=oracle)
    if not oracle['eligible']:
        try:
            crush_normal_ray(source, rows)
        except ValueError as error:
            result.update(status='REJECTED', reason=str(error))
            return result
        raise AssertionError('producer accepted a nonprimitive, nonextreme or nonprogress input')
    native = crush_normal_ray(source, rows)
    assert native['status'] == 'COMPLETE'
    packet = native['certificate']
    assert verify_normal_crushing(source, packet)
    assert packet['triangulation'] == oracle['quotient'], case['id']
    assert packet['components'] == oracle['components'], case['id']
    assert packet['torus_component'] == oracle['torus_component'], case['id']
    assert packet['successor'] == oracle['successor'], case['id']
    assert native['successor'] == packet['successor']
    assert len(packet['triangulation']['tetrahedra']) < len(source['tetrahedra'])
    result.update(status='COMPLETE', native=native)
    return result


def disappeared_torus_details(source, rows):
    """Distinguish cutting a trivial-boundary disc from destructive flattening."""
    tri = regina_triangulation(source)
    surface = regina.NormalSurface(tri, regina.NormalCoords.Standard,
                                  [x for row in rows for x in row])
    detail = dict(source_is_solid_torus=tri.isSolidTorus(), source_isosig=tri.isoSig(),
        connected=surface.isConnected(), orientable=surface.isOrientable(),
        euler=int(str(surface.eulerChar())), boundary_components=surface.countBoundaries(),
        compressing_disc=surface.isCompressingDisc(), cut_components=[], crush_components=[],
        native_disc_methods={})
    for name, quotient in (('cut_components', surface.cutAlong()),
                           ('crush_components', surface.crush())):
        detail[name] = [dict(tetrahedra=c.size(), boundary_euler=[int(b.eulerChar())
            for b in c.boundaryComponents()], is_ball=c.isBall(), is_solid_torus=c.isSolidTorus())
            for c in quotient.triangulateComponents()]
    for unit in (False, True):
        result = normal_compressing_disk_count(source, rows, unit_ray=unit, record_certificate=True)
        assert result['status'] == 'COMPLETE' and result['compressing_disk_components'] == 0
        assert verify_normal_disk_count_certificate(source, rows, result['certificate'])
        detail['native_disc_methods'][str(unit)] = result
    topology = normal_surface_topology(source, rows, record_certificate=True)
    assert topology['status'] == 'COMPLETE'
    assert verify_normal_surface_certificate(source, rows, topology['certificate'])
    detail['native_topology'] = topology
    assert not detail['compressing_disc'] and detail['connected'] and detail['euler'] == 1
    assert sorted((c['is_ball'], c['is_solid_torus']) for c in detail['cut_components']) == [(False, True), (True, False)]
    assert [(c['is_ball'], c['is_solid_torus']) for c in detail['crush_components']] == [(True, False)]
    return detail


def diagram_audit():
    diagram, original, shelling, cases = diagram_cases()
    assert verify_diagram_exterior(diagram, original)
    assert verify_boundary_shellings(original, shelling['triangulation'], shelling['moves'])
    results = []
    for name, sequence in cases:
        current = shelling['triangulation']
        comparisons = []
        for i, rows in enumerate(sequence):
            comparison = compare(dict(id=f'{name}_{i}', source=current, coordinates=rows))
            assert comparison['status'] == 'COMPLETE'
            comparisons.append(comparison)
            current = comparison['native']['successor']
        chain = make_crushing_chain(diagram, sequence, shelling=shelling)
        assert chain['status'] == 'UNKNOT' and verify_crushing_chain(diagram, chain)
        assert current is None
        results.append(dict(id=name, comparisons=comparisons, certificate=chain))
    detail = disappeared_torus_details(shelling['triangulation'], cases[0][1][0])
    return dict(input_pd=[], source_tetrahedra=len(original['tetrahedra']),
                shelled_tetrahedra=len(shelling['triangulation']['tetrahedra']),
                cases=results, flattening_side_effect=detail)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    output = dict(passed=False, regina=regina.versionString(), source_sha256=source_hashes(),
        scope='exact supplied-ray quotient comparison plus two source-authenticated diagram chains; no surface-search complexity claim',
        retained=[], expanded=[], isolated_cycle=None, one_tetrahedron=[], diagram=None)
    path = Path(args.output)
    def save():
        path.write_text(json.dumps(output, indent=2)+'\n')
    counts = Counter()
    for case in retained_cases():
        assert verify_normal_disk_count_certificate(case['source'], case['coordinates'], case['disc_certificate'])
        result = compare(case)
        assert result['status'] == 'COMPLETE'
        output['retained'].append(result)
        counts['accepted' if case['accepted'] else 'rejected'] += 1
        if case['accepted']:
            counts['accepted_nonempty' if result['oracle']['quotient']['tetrahedra'] else 'accepted_empty'] += 1
        else:
            assert result['native']['successor'] is not None
    assert dict(counts) == dict(rejected=9, accepted=9, accepted_nonempty=3, accepted_empty=6)
    output['retained_counts'] = dict(counts)
    save()
    totals, eligibility = Counter(), Counter()
    for case in expanded_cases():
        result = compare(case)
        totals[case['kind']] += 1
        eligibility[result['status']] += 1
        output['expanded'].append(result)
    assert dict(totals) == dict(disc_nonlink=171, disc_link=2, sphere_link=2)
    assert any(any(not c['boundary_euler'] for c in r['oracle']['components']) for r in output['expanded'])
    assert any(len(r['oracle']['components']) > 1 for r in output['expanded'])
    output.update(expanded_counts=dict(totals), expanded_eligibility=dict(eligibility))
    output['isolated_cycle'] = compare(isolated_cycle_case())
    assert output['isolated_cycle']['status'] == 'COMPLETE'
    assert [len(c) for c in output['isolated_cycle']['oracle']['isolated_cycles']] == [6]
    output['one_tetrahedron'] = [compare(case) for case in one_tetrahedron_cases()]
    assert sorted((r['vertex_link'], r['status']) for r in output['one_tetrahedron']) == [(False, 'COMPLETE'), (True, 'REJECTED')]
    save()
    output['diagram'] = diagram_audit()
    assert output['source_sha256'] == source_hashes(), 'audited source changed during the run'
    output['passed'] = True
    save()
    print(json.dumps(dict(passed=True, retained=counts, expanded=totals,
        expanded_eligibility=eligibility, source_authenticated_chains=2, output=str(path))))


if __name__ == '__main__':
    main()
