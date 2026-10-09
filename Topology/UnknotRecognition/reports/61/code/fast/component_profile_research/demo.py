"""Small, dependency-free demonstration of normal-component certificates.

From the fast/ directory run:
    python -m component_profile_research.demo

This uses the hand-built layered solid torus, without importing Regina.
All printed large counts are represented by bit lengths and exact equality
checks; no huge decimal integer or expanded component list is printed.
"""

from argparse import ArgumentParser
import json
from math import gcd
from pathlib import Path

from fastunknot.integer_codec import json_safe
from fastunknot.normal_component_profile import (
    normal_component_profile, verify_normal_component_profile,
)
from normal_orbit_research.fixtures import layered_torus


def _checked_profile(triangulation, coordinates):
    result = normal_component_profile(
        triangulation, coordinates, record_certificate=True)
    if result['status'] != 'COMPLETE':
        raise AssertionError('The demonstration query did not complete')
    certificate = result['certificate']
    verified = verify_normal_component_profile(
        triangulation, coordinates, certificate)
    transport = json.dumps(json_safe(certificate), sort_keys=True)
    transport_verified = verify_normal_component_profile(
        triangulation, coordinates, json.loads(transport))
    if not verified or not transport_verified:
        raise AssertionError('A demonstration certificate did not verify')
    return result, {
        'certificate_verified': verified,
        'json_roundtrip_verified': transport_verified,
        'certificate_json_bytes': len(transport.encode('utf-8')),
    }


def run_demo():
    """Return small JSON-safe summaries of two exactly checked queries."""
    triangulation, meridian = layered_torus(1)
    vertex_link = [[1, 1, 1, 1, 0, 0, 0]]
    mixed = [[a + b for a, b in zip(left, right)]
             for left, right in zip(meridian, vertex_link)]
    coordinate_gcd = gcd(*(value for row in mixed for value in row))
    result, verification = _checked_profile(triangulation, mixed)
    observed = (result['components'], result['disk_components'],
                result['compressing_disk_components'])
    if coordinate_gcd != 1 or observed != (2, 2, 1):
        raise AssertionError('Unexpected meridian-plus-vertex-link profile')
    mixed_summary = {
        'coordinate_gcd': coordinate_gcd,
        'components': result['components'],
        'disk_components': result['disk_components'],
        'compressing_disk_components': result['compressing_disk_components'],
        'profile_group_count': len(result['groups']),
        'groups': [{key: group[key] for key in (
            'multiplicity', 'euler_characteristic', 'normal_disks',
            'boundary_vertices', 'boundary_class_mod2',
            'is_disk', 'is_compressing_disk',
        )} for group in result['groups']],
        **verification,
    }

    exponent = 5000
    multiplicity = 1 << exponent
    parallel = [[multiplicity * value for value in row] for row in meridian]
    result, verification = _checked_profile(triangulation, parallel)
    counts_match = all(result[key] == multiplicity for key in (
        'components', 'disk_components', 'compressing_disk_components'))
    if not counts_match or len(result['groups']) != 1:
        raise AssertionError('Unexpected compressed parallel-disk profile')
    parallel_summary = {
        'multiplicity_power_of_two': exponent,
        'components_bit_length': result['components'].bit_length(),
        'disk_components_bit_length': result['disk_components'].bit_length(),
        'compressing_disk_components_bit_length':
            result['compressing_disk_components'].bit_length(),
        'counts_equal_requested_multiplicity': counts_match,
        'profile_group_count': len(result['groups']),
        **verification,
    }
    return {
        'schema': 'normal-component-profile-demo-v1',
        'fixture': 'hand-built one-tetrahedron layered solid torus',
        'regina_required': False,
        'meridian_plus_vertex_link': mixed_summary,
        'huge_parallel_meridians': parallel_summary,
        'scope': (
            'Claims concern components of the supplied normal surfaces. '
            'No knot-diagram provenance is asserted. A negative component '
            'query does not prove boundary incompressibility.'),
    }


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        help='also save the small demonstration summary as JSON')
    args = parser.parse_args()
    encoded = json.dumps(run_demo(), indent=2, sort_keys=True) + '\n'
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
