#!/usr/bin/env python3
"""A dependency-free demonstration of extracting components and replaying proof."""
import argparse
import json
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits', type=int, default=128)
    args = parser.parse_args()
    if args.bits < 0:
        parser.error('--bits must be nonnegative')
    root = Path(__file__).resolve().parents[1]
    sys.path.insert(0, str(root / 'code/fast'))
    from normal_orbit_research.fixtures import layered_torus
    from fastunknot.normal_components import normal_component_inventory, verify_normal_component_certificate
    from fastunknot.integer_codec import json_safe
    triangulation, meridian = layered_torus(8)
    k = 1 << args.bits
    vertex_link = [[1, 1, 1, 1, 0, 0, 0] for _ in meridian]
    coordinates = [[k*x + (k+1)*y for x, y in zip(a, b)]
                   for a, b in zip(meridian, vertex_link)]
    result = normal_component_inventory(triangulation, coordinates, record_certificate=True)
    if result['status'] != 'COMPLETE':
        raise AssertionError('unlimited demonstration did not complete')
    verified = verify_normal_component_certificate(triangulation, coordinates, result['certificate'])
    if not verified or result['components'] != 2*k+1 or result['distinct_vectors'] != 2 or result['compressing_disk_components'] != k:
        raise AssertionError('demonstration result failed its exact checks')
    summary = {'status': result['status'], 'verified': verified, 'power_exponent': args.bits,
               'components': result['components'], 'distinct_vectors': result['distinct_vectors'],
               'compressing_disk_components': result['compressing_disk_components'],
               'profiles': result['profiles'], 'stats': result['stats'], 'scope': result['trust']}
    print(json.dumps(json_safe(summary), indent=2))


if __name__ == '__main__':
    main()
