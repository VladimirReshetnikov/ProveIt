"""A checked 3--2 move that splits one coherent disc into a disc and two spheres."""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from fastunknot.cocycle_transport import transport_cocycle
from fastunknot.cocycle_transport_verify import verify_cocycle_transport
from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_component_verify import verify_normal_component_certificate
from fastunknot.pachner23 import pachner_23
from fastunknot.pachner32 import pachner_32
from normal_orbit_research.fixtures import interior_vertex_torus


def splitting_example():
    original, _ = interior_vertex_torus()
    seed, prepared = _rank_one_cocycle_seed_details(original)
    # An integral vertex coboundary preserves the primitive generator class.
    heights = [[x+(-5 if prepared['vertex_roots'][4*t+i] == 0 else 0)
                for i,x in enumerate(row)] for t,row in enumerate(seed['heights'])]
    up = pachner_23(original, 2, 1)
    forward = transport_cocycle(original, heights, up['triangulation'], up['certificate'])
    down = pachner_32(up['triangulation'], 2, [0,1])
    reverse = transport_cocycle(up['triangulation'], forward['heights'],
                               down['triangulation'], down['certificate'])
    assert verify_cocycle_transport(up['triangulation'], forward['heights'],
                                   down['triangulation'], reverse['certificate'])
    before = normal_component_census(up['triangulation'], forward['coordinates'],
                                    mode='summary', record_certificate=True)
    after = normal_component_census(down['triangulation'], reverse['coordinates'],
                                   mode='summary', record_certificate=True)
    assert verify_normal_component_certificate(up['triangulation'], forward['coordinates'],
                                               before['certificate'])
    assert verify_normal_component_certificate(down['triangulation'], reverse['coordinates'],
                                               after['certificate'])
    assert before['components'] == 1 and before['euler_characteristic'] == 1
    assert after['components'] == 3 and after['euler_characteristic'] == 5
    assert before['compressing_disk_components'] == after['compressing_disk_components'] == 1
    assert reverse['certificate']['euler_jump'] == 4
    assert reverse['certificate']['normal_disc_jump'] == -5
    return dict(initial_triangulation=original, primitive_seed=seed,
        vertex_potential=dict(vertex=0, value=-5), initial_heights=heights,
        preparation=dict(triangulation=up['triangulation'], transport=forward['certificate']),
        collapse=dict(triangulation=down['triangulation'], transport=reverse['certificate']),
        before_census=before, after_census=after)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = splitting_example()
    result['driver_sha256'] = sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('verified: one disc -> one disc plus two spheres')


if __name__ == '__main__':
    main()
