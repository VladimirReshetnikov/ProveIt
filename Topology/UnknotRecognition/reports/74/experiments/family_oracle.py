"""Closed-form capped Fibonacci rays and an independent topology audit."""

import argparse
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]


def fibonacci_values(n):
    values = [0, 1]
    for _ in range(n):
        values.append(values[-2]+values[-1])
    return values


def canonical_family(n, x, y):
    if any(type(i) is not int for i in (n, x, y)) or n < 1 or x < 0 or y < 0:
        raise ValueError('positive size and nonnegative integral parameters required')
    f = fibonacci_values(n+2)
    a, b = f[n+1], f[n+2]
    h = max(0, y-a*x)
    rows = [[f[n-i+1]*x+h, f[n-i+1]*x+h, h, h, 0, 0, f[n-i]*x]
            for i in range(n)]
    rows.append([a*x+h-y, b*x+h, 0, h, 0, y, 0])
    return rows, h


def standard_rays(n):
    a = fibonacci_values(n+2)[n+1]
    return [canonical_family(n, x, y)[0] for x, y in ((1, 0), (1, a), (0, 1))]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--code-root', type=Path, default=ROOT/'code')
    parser.add_argument('--output', type=Path, default=ROOT/'results/family_oracle.json')
    args = parser.parse_args()
    sys.path.insert(0, str(args.code_root.resolve()))
    from fastunknot.normal_sector import build_sector_kernel, sector_rays
    from fastunknot.sector_envelope import sector_envelope_rays
    from fastunknot.normal_surface_components import normal_component_census
    from fastunknot.normal_component_verify import verify_normal_component_certificate
    from sector_envelope_research.fixtures import capped_fibonacci, ray_digest
    result = dict(schema='capped-fibonacci-formula-audit-v1', ray_checks=[], topology_checks=[])
    for n in (1, 2, 3, 4, 8, 16, 32, 64, 128):
        fixture = capped_fibonacci(n, 1)
        kernel = build_sector_kernel(fixture['triangulation'], fixture['allowed_types'])
        expected = standard_rays(n)
        actual = list(sector_envelope_rays(kernel))
        assert ray_digest(expected) == ray_digest(actual)
        stats = {}
        if n <= 8:
            old = list(sector_rays(kernel, method='arrangement', stats=stats))
            assert ray_digest(old) == ray_digest(expected)
            assert stats['hyperplanes'] == n+3
            assert stats['positive_directions'] == n+2
            assert stats['nonextreme_directions'] == n-1
        result['ray_checks'].append(dict(n=n, ray_sha256=ray_digest(expected), old_stats=stats))
    for n in (1, 2, 4, 8):
        fixture = capped_fibonacci(n, 1)
        a = fibonacci_values(n+2)[n+1]
        pairs = {(x, y) for x in range(4) for y in range(5)}
        pairs.update((x, max(0, a*x+delta)) for x in range(4) for delta in (-1, 0, 1))
        pairs.discard((0, 0))
        for x, y in sorted(pairs):
            rows, h = canonical_family(n, x, y)
            answer = normal_component_census(fixture['triangulation'], rows,
                                            record_certificate=True)
            assert answer['status'] == 'COMPLETE'
            assert answer['components'] == x+h
            assert answer['compressing_disk_components'] == x
            assert verify_normal_component_certificate(fixture['triangulation'], rows,
                                                       answer['certificate'])
            result['topology_checks'].append(dict(n=n, x=x, y=y, h=h,
                components=answer['components'], essential_discs=answer['compressing_disk_components']))
    result['counts'] = dict(ray_families=len(result['ray_checks']),
                           topology_vectors=len(result['topology_checks']))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('COMPLETE', result['counts'])


if __name__ == '__main__':
    main()
