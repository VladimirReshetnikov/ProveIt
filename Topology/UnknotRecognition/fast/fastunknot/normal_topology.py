"""Compressed connected-topology spectrum for a supplied normal surface.

The output groups components by homeomorphism type and retains arbitrary-size
binary multiplicities. It does not identify component normal vectors, decide
whether boundary circles are essential, or search for a normal surface.
"""

from .normal_surface_geometry import _prepare, _coordinates, _arc_system, _fingerprint
from .normal_disk_kernel import canonical_disk_core
from .normal_topology_geometry import (
    topology_weight_system, vertex_link_totals, spectrum_summary,
)
from .orbit_transversal import orbit_transversal
from .weighted_orbits import weighted_orbit_histogram
from .topology_spectrum import recover_topology_spectrum, scale_core_spectrum


def normal_topology_spectrum(triangulation, coordinates, *, reduce_core=True,
                             max_cycles=None, periodic_rule='fine_wilf',
                             check=lambda: None, record_certificate=False):
    """Compute every connected topological type with two orbit-weight entries.

    One shared cycle allowance covers the boundary, surface and double-surface
    orbit discoveries. Validation, weight replay and certificate verification
    are controlled by the cooperative callback instead of that cycle counter.
    A depleted allowance emits no spectrum, summary, or certificate.

    ``reduce_core`` peels vertex links and divides by quadrilateral content.
    Recovery treats one-sided components through paired orientation covers.
    """
    if type(reduce_core) is not bool or type(record_certificate) is not bool:
        raise ValueError('reduce_core and record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    if periodic_rule not in ('fine_wilf', 'aht'):
        raise ValueError('unknown periodic rule')
    check()
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    source_digest = _fingerprint(triangulation, analysed, check) if record_certificate else None
    if reduce_core:
        divisor, core, links = canonical_disk_core(prepared, analysed, check)
        query = _coordinates(prepared, core, check)
        link_disks, link_spheres = vertex_link_totals(prepared, links, check)
    else:
        divisor, core, links = 1, analysed['rows'], []
        query, link_disks, link_spheres = analysed, 0, 0
    stats = dict(orbit_cycles=0, queries=0, weight_dimension=2,
                 input_coordinate_bits=analysed['maximum_coordinate_bits'],
                 query_coordinate_bits=query['maximum_coordinate_bits'])

    def remaining():
        return None if max_cycles is None else max_cycles - stats['orbit_cycles']

    def incomplete(stage):
        check()
        return dict(status='INCONCLUSIVE', reason='shared orbit-cycle allowance exhausted',
                    stage=stage, reduced_core=reduce_core, stats=stats)

    query_proof = None
    if reduce_core and not divisor:
        core_rows = []
    else:
        boundary_size, boundary_pairs = _arc_system(prepared, query,
                                                    boundary=True, check=check)
        boundary = orbit_transversal(boundary_size, boundary_pairs, max_cycles=remaining(),
            periodic_rule=periodic_rule, check=check, record_certificate=True)
        stats['queries'] += 1
        stats['orbit_cycles'] += boundary['stats']['orbit_cycles']
        stats['boundary'] = boundary['stats']
        if boundary['status'] != 'COMPLETE':
            return incomplete('boundary')
        transversal = boundary
        marks = transversal['representative_intervals']
        stats['boundary_transversal_intervals'] = len(marks)
        stats['boundary_transversal'] = transversal.get('stats', {})
        histograms, proofs = [], []
        for scale in (1, 2):
            check()
            system = topology_weight_system(prepared, query, marks, scale=scale, check=check)
            result = weighted_orbit_histogram(system['size'], system['pairings'],
                system['weights'], dimension=2, max_cycles=remaining(),
                periodic_rule=periodic_rule, check=check,
                record_certificate=record_certificate)
            stats['queries'] += 1
            stats['orbit_cycles'] += result['stats']['orbit_cycles']
            stats['surface' if scale == 1 else 'double'] = result['stats']
            if result['status'] != 'COMPLETE':
                return incomplete('surface' if scale == 1 else 'double')
            histograms.append(result['histogram'])
            if record_certificate:
                proofs.append(result['certificate'])
        core_rows = recover_topology_spectrum(*histograms, check=check)
        if record_certificate:
            query_proof = dict(boundary_transversal=transversal['certificate'],
                               surface=proofs[0], double=proofs[1],
                               topology_spectrum=core_rows)
    rows = scale_core_spectrum(core_rows, divisor,
        vertex_link_disks=link_disks, vertex_link_spheres=link_spheres, check=check)
    summary = spectrum_summary(rows, check)
    if summary['euler_characteristic'] != analysed['euler_characteristic']:
        raise ArithmeticError('reconstructed Euler sum differs from source')
    result = dict(status='COMPLETE', reduced_core=reduce_core, weight_dimension=2,
        tetrahedra=len(analysed['rows']), normal_disks=analysed['normal_disks'],
        normal_points=sum(analysed['weights'].values()),
        boundary_normal_arcs=analysed['boundary_arcs'], stats=stats, **summary,
        trust='homeomorphism types of components of this supplied normal vector; '
              'boundary essentiality and knot-diagram provenance are separate')
    if record_certificate:
        result['certificate'] = dict(schema='normal-topology-spectrum-v1',
            input_sha256=source_digest, reduced_core=reduce_core,
            coordinate_divisor=divisor, vertex_links=links,
            core_coordinates=core, query=query_proof, summary=summary)
    check()
    return result


def _main():
    import argparse
    import json
    from pathlib import Path
    import sys
    import time
    from .integer_codec import json_safe

    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    census = commands.add_parser('census', help='compute a compressed topology spectrum')
    census.add_argument('input', help='JSON with triangulation and coordinates')
    census.add_argument('--direct', action='store_true', help='disable coordinate core reduction')
    census.add_argument('--certificate', action='store_true')
    census.add_argument('--max-cycles', type=int)
    census.add_argument('--timeout', type=float)
    census.add_argument('--periodic-rule', choices=('fine_wilf', 'aht'), default='fine_wilf')
    replay = commands.add_parser('verify', help='check a source-bound certificate')
    replay.add_argument('input')
    replay.add_argument('certificate', help='certificate JSON or a complete census result')
    replay.add_argument('--timeout', type=float)
    for command in (census, replay):
        command.add_argument('-o', '--output')
    args = parser.parse_args()
    if args.timeout is not None and args.timeout < 0:
        parser.error('--timeout must be nonnegative')
    source = json.loads(Path(args.input).read_text())
    deadline = None if args.timeout is None else time.monotonic() + args.timeout

    def check():
        if deadline is not None and time.monotonic() >= deadline:
            raise TimeoutError('wall-clock allowance exhausted')

    try:
        if args.command == 'census':
            answer = normal_topology_spectrum(source['triangulation'], source['coordinates'],
                reduce_core=not args.direct, max_cycles=args.max_cycles,
                periodic_rule=args.periodic_rule, check=check,
                record_certificate=args.certificate)
        else:
            from .normal_topology_verify import verify_normal_topology_spectrum
            proof = json.loads(Path(args.certificate).read_text())
            if type(proof) is dict and 'certificate' in proof:
                proof = proof['certificate']
            answer = dict(valid=verify_normal_topology_spectrum(source['triangulation'],
                            source['coordinates'], proof, check=check))
    except TimeoutError as error:
        answer = dict(status='INCONCLUSIVE', reason=str(error))
    text = json.dumps(json_safe(answer), indent=2) + '\n'
    if args.output:
        Path(args.output).write_text(text)
    else:
        sys.stdout.write(text)


if __name__ == '__main__':
    _main()
