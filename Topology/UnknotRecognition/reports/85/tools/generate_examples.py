#!/usr/bin/env python3
"""Regenerate the five small source-bound proof packets in this archive."""

import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
FAST = ROOT / 'runtime' / 'fast'
sys.path.insert(0, str(FAST))

from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from fastunknot.parallelity_boundary_words_verify import verify_parallelity_boundary_words
from fastunknot.sector_blocks import certify_sector_block_rays
from fastunknot.sector_blocks_verify import verify_block_ray_certificate
from normal_orbit_research.fixtures import layered_torus
from sector_block_research.fixtures import capped_bipyramid_chain


def save(name, item):
    path = ROOT / 'examples' / name
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(json_safe(item), indent=2) + '\n')
    print(json.dumps(dict(file=name, bytes=path.stat().st_size)))


def main():
    for t, multiplicity, name in (
        (4, 1, 'layered_t4_primitive_census.json'),
        (1, 1 << 128, 'layered_t1_binary_census.json'),
    ):
        source, primitive = layered_torus(t)
        coordinates = [[multiplicity * value for value in row] for row in primitive]
        answer = normal_cut_handlebodies(source, coordinates, record_certificate=True)
        assert answer['status'] == 'COMPLETE'
        assert verify_normal_cut_handlebodies(source, coordinates, answer['certificate'])
        assert answer['census']['ball_components'] == multiplicity
        save(name, dict(
            description='Exact census for the cut along parallel meridians of a layered solid torus.',
            triangulation=source, coordinates=coordinates,
            certificate=answer['certificate']))

    bank = json.loads((FAST / 'marked_parallelity_research' / 'corpus.json').read_text())['cases']
    item = next(case for case in bank if case['id'] == 'pilot/fibonacci_lst_02/0')
    source, coordinates = item['triangulation'], item['coordinates']
    answer = normal_parallelity_boundary_words(source, coordinates, record_certificate=True)
    assert answer['status'] == 'COMPLETE'
    assert verify_parallelity_boundary_words(source, coordinates, answer['certificate'])
    assert any(component['kind'] == 'circle'
               for component in answer['skeleton']['attachment_components'])
    save('annular_interface_obstruction.json', dict(
        description='An actual full marked boundary circle: the disk-only census must refuse it.',
        source_case=item['id'], triangulation=source, coordinates=coordinates,
        certificate=answer['certificate']))

    fixture = capped_bipyramid_chain(2)
    source, support = fixture['triangulation'], fixture['allowed_types']
    for phase, count in (('quadrilateral', 4), ('standard', 5)):
        answer = certify_sector_block_rays(source, support, phase=phase)
        assert answer['status'] == 'COMPLETE'
        assert len(answer['rays']) == count
        assert verify_block_ray_certificate(source, answer['certificate'])
        save('bipyramid_b2_' + phase + '_rays.json', dict(
            description='Complete supplied-sector ray set; the standard set requires a mixed ray.',
            triangulation=source, allowed_types=support,
            expected_ray_count=count, certificate=answer['certificate']))


if __name__ == '__main__':
    main()
