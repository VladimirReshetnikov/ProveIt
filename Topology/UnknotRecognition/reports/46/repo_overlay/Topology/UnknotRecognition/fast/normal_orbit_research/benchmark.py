"""Reproduce encoded normal-surface topology and explicit-expansion controls.

Run from fast/: python3 -B normal_orbit_research/benchmark.py --output PATH
The prior layered-torus constructor is reused with its MIT-0 provenance;
normal_surface_topology validates every resulting face pairing and vector.
"""
import argparse
import hashlib
import json
import platform
from pathlib import Path
import random
from statistics import median
import sys
from time import perf_counter

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from fastunknot.normal_surface_orbits import normal_arc_pairings, normal_surface_topology
from normal_orbit_research.fixtures import layered_torus


def literal_count(n, pairs):
    parent, sizes = list(range(n)), [1] * n
    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v
    for p in pairs:
        for i in range(p.width):
            a, b = find(p.a + i), find(p.d - i if p.reverse else p.c + i)
            if a != b:
                if sizes[a] < sizes[b]:
                    a, b = b, a
                parent[b], sizes[a] = a, sizes[a] + sizes[b]
    return len({find(v) for v in range(n)})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True)
    parser.add_argument('--rounds', type=int, default=3)
    parser.add_argument('--explicit-cap', type=int, default=1000000)
    args = parser.parse_args()
    rng = random.Random(261008121)
    data = dict(python=sys.version, platform=platform.platform(), seed=261008121,
                rounds=args.rounds, warmups=1, explicit_cap=args.explicit_cap,
                baseline_commit='58ee11a97d5fd7f21647c57eefaf3ecc007931d6',
                scope='supplied layered-solid-torus normal surfaces, not whole-knot recognition',
                cases=[], scaling=[])
    for count in (4, 8, 12, 16, 20, 32, 64, 128):
        raw, coords = layered_torus(count)
        timings, outputs = {}, {}
        arms = ['aht', 'fine_wilf', 'fine_wilf_AA']
        for round_index in range(-1, args.rounds):
            order = list(arms)
            rng.shuffle(order)
            for arm in order:
                start = perf_counter()
                result = normal_surface_topology(raw, coords,
                    periodic_rule='aht' if arm == 'aht' else 'fine_wilf')
                elapsed = perf_counter() - start
                if not result['compressing_disk'] or result['components'] != 1:
                    raise AssertionError('layered meridian failed native validation')
                if round_index >= 0:
                    timings.setdefault(arm, []).append(elapsed)
                outputs[arm] = result
        n, pairs = normal_arc_pairings(raw, coords)
        explicit = dict(points=n, attempted=n <= args.explicit_cap,
                        scope='connectivity query only; encoded arms include all topology')
        if n <= args.explicit_cap:
            start = perf_counter()
            value = literal_count(n, pairs)
            explicit.update(seconds=perf_counter() - start, components=value)
            if value != 1:
                raise AssertionError('literal arc graph disagrees')
        else:
            explicit['reason'] = 'declared explicit point cap; no timing or timeout inferred'
        data['cases'].append(dict(tetrahedra=count, timings=timings,
            medians={arm: median(values) for arm, values in timings.items()},
            result=outputs['fine_wilf'], aht_cycles=outputs['aht']['cycles'], explicit=explicit))
        print('tetrahedra',count,'disks',outputs['fine_wilf']['normal_disks'],
              'ms',round(1000*median(timings['fine_wilf']),3),flush=True)
    raw, coords = layered_torus(3)
    for bits in (0, 32, 128, 500, 2000):
        scale = 1 << bits
        scaled = [[scale * value for value in row] for row in coords]
        start = perf_counter()
        result = normal_surface_topology(raw, scaled)
        elapsed = perf_counter() - start
        if result['components'] != scale or result['orientable_components'] != scale:
            raise AssertionError('parallel-component multiplicity disagrees')
        data['scaling'].append(dict(scale_bits=bits+1, seconds=elapsed,
                                   components_hex=hex(result['components']),
                                   cycles=result['cycles']))
    root = Path(__file__).resolve().parents[1]
    data['source_sha256'] = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in [root/'fastunknot/normal_surface_orbits.py',
                  root/'fastunknot/interval_orbits.py', Path(__file__).resolve(),
                  root/'normal_orbit_research/fixtures.py']}
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(data, indent=2)+'\n')


if __name__ == '__main__':
    main()
