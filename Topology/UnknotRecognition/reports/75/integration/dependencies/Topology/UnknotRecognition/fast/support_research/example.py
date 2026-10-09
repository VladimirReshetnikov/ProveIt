#!/usr/bin/env python3
"""The article's 128-tetrahedron, 5001-bit multiplicity example."""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from normal_orbit_research.fixtures import layered_torus
from fastunknot.normal_ray_blocks import normal_ray_block_disk_count
from fastunknot.normal_ray_blocks_verify import verify_normal_ray_block_disk_certificate


def main():
    triangulation, primitive = layered_torus(128)
    multiplicity = (1 << 5000) + 1
    source = [[multiplicity * x for x in row] for row in primitive]
    answer = normal_ray_block_disk_count(triangulation, source,
                                         max_cycles=0, record_certificate=True)
    assert answer['status'] == 'COMPLETE'
    assert answer['compressing_disk_components'] == multiplicity
    assert answer['stats']['orbit_cycles'] == 0
    assert verify_normal_ray_block_disk_certificate(triangulation, source,
                                                    answer['certificate'])
    return dict(status='PASS', tetrahedra=128, multiplicity_bits=multiplicity.bit_length(),
                peeling_steps=len(answer['certificate']['blocks'][0]['support_certificate']['steps']),
                orbit_cycles=0, count_equals_source_multiplicity=True)


if __name__ == '__main__':
    print(json.dumps(main(), indent=2))
