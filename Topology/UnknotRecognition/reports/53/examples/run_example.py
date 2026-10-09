#!/usr/bin/env python3
"""Generate source-bound examples using only the native Python kernel."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'code/fast'))
from normal_orbit_research.fixtures import layered_torus
from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_component_verify import verify_normal_component_certificate
from fastunknot.normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate,
)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT/'reproduced/examples')
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    tri, disk = layered_torus(4)
    vector = [[2*value for value in row] for row in disk]
    answer = normal_component_census(tri, vector, record_certificate=True)
    assert answer['compressing_disk_components'] == 2
    assert verify_normal_component_certificate(tri, vector, answer['certificate'])
    payload = dict(triangulation=tri, coordinates=vector, answer=answer)
    (args.output_dir/'two_meridians.json').write_text(
        json.dumps(json_safe(payload), indent=2)+'\n')
    tri, disk = layered_torus(16)
    factor = 1 << 1024
    vector = [[factor*value+(factor+1 if j < 4 else 0)
        for j, value in enumerate(row)] for row in disk]
    answer = normal_compressing_disk_count(tri, vector, record_certificate=True)
    assert answer['compressing_disk_components'] == factor
    assert answer['core_coordinate_bits'] == 11
    assert verify_normal_disk_count_certificate(tri, vector, answer['certificate'])
    payload = dict(triangulation=tri, coordinates=vector, answer=answer)
    (args.output_dir/'large_gcd_one_core.json').write_text(
        json.dumps(json_safe(payload), indent=2)+'\n')
    print(json.dumps(dict(two_meridians_verified=True, large_core_verified=True,
        large_disc_count_equals_2_power_1024=True,
        large_input_bits=answer['input_coordinate_bits'],
        core_bits=answer['core_coordinate_bits'], output=str(args.output_dir)), indent=2))

if __name__ == '__main__':
    main()
