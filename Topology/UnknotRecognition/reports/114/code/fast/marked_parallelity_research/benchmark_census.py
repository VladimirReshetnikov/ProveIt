"""Paired whole-cut timings and separate binary-capacity measurements.

Both paths start from the same face pairings and standard normal coordinates.
The native time includes certificate production and independent replay. The
Regina path constructs the explicit cut and recognises every component. It is
a comparison of these specific operations, not whole knot recognition.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time

from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_orbit_research.fixtures import layered_torus, regina_surface, regina_triangulation
from normal_orbit_research.seeds import sources


def native(raw, coordinates):
    begin = time.perf_counter()
    result = normal_cut_handlebodies(raw, coordinates, record_certificate=True)
    produced = time.perf_counter()
    assert result['status'] == 'COMPLETE', result
    assert verify_normal_cut_handlebodies(raw, coordinates, result['certificate'])
    end = time.perf_counter()
    return result, dict(produce=produced - begin, replay=end - produced, total=end - begin)


def explicit(raw, coordinates):
    if sum(map(sum, coordinates)) > 50000:
        raise ValueError('explicit oracle expansion cap exceeded')
    begin = time.perf_counter()
    triangulation = regina_triangulation(raw)
    surface = regina_surface(triangulation, coordinates)
    cut = surface.cutAlong()
    histogram = Counter(p.recogniseHandlebody() for p in cut.triangulateComponents())
    end = time.perf_counter()
    return dict(histogram=[dict(genus=g, multiplicity=n)
                           for g, n in sorted(histogram.items())], tetrahedra=cut.size()), end - begin


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True)
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--capacity', action='store_true')
    args = parser.parse_args()
    import regina
    source_pins = sources()
    report = dict(python=sys.version, platform=platform.platform(), regina=regina.versionString(),
                  native_source_sha256=source_pins,
                  rounds=args.rounds, timer='perf_counter', seed=20261012,
                  meaning='Regina explicit cut+component recognition / native production+independent replay',
                  cases=[], capacity=[])
    rng = random.Random(20261012)
    specifications = [(1, 1), (1, 16), (1, 256), (1, 4096),
                      (4, 1), (4, 8), (4, 64), (8, 1), (8, 8), (12, 1)]
    for t, copies in specifications:
        raw, base = layered_torus(t)
        coordinates = [[copies * n for n in row] for row in base]
        expected = [dict(genus=0, multiplicity=copies)]
        reference, _ = explicit(raw, coordinates)
        fresh, _ = native(raw, coordinates)
        assert fresh['census']['histogram'] == reference['histogram'] == expected
        samples = []
        for _ in range(args.rounds):
            order = ['native', 'explicit']
            rng.shuffle(order)
            sample = dict(order=order)
            for name in order:
                if name == 'native':
                    result, timing = native(raw, coordinates)
                    assert result['census']['histogram'] == expected
                    sample['native'] = timing
                else:
                    value, timing = explicit(raw, coordinates)
                    assert value['histogram'] == expected
                    sample['explicit'] = timing
            samples.append(sample)
        aa = []
        for _ in range(3):
            _, a = explicit(raw, coordinates)
            _, b = explicit(raw, coordinates)
            aa.append(a / b)
        data = dict(tetrahedra=t, copies=copies, normal_disks=sum(map(sum, coordinates)),
                    explicit_cut_tetrahedra=reference['tetrahedra'], samples=samples,
                    native_median=statistics.median(x['native']['total'] for x in samples),
                    explicit_median=statistics.median(x['explicit'] for x in samples),
                    median_paired_ratio=statistics.median(x['explicit'] / x['native']['total'] for x in samples),
                    aa_ratios=aa, aa_median=statistics.median(aa))
        report['cases'].append(data)
        print(json.dumps({k: v for k, v in data.items() if k not in ('samples', 'aa_ratios')}), flush=True)
        Path(args.output).write_text(json.dumps(json_safe(report), indent=2) + '\n')
    if args.capacity:
        for t, power in [(1, 16384), (4, 1024), (4, 16384), (8, 16384)]:
            raw, base = layered_torus(t)
            copies = 1 << power
            coordinates = [[copies * n for n in row] for row in base]
            value, timing = native(raw, coordinates)
            assert value['census']['histogram'] == [dict(genus=0, multiplicity=copies)]
            serialized = json.dumps(json_safe(value['certificate']), sort_keys=True).encode()
            data = dict(tetrahedra=t, multiplicity_power=power, timing=timing,
                        certificate_bytes=len(serialized),
                        certificate_sha256=hashlib.sha256(serialized).hexdigest(),
                        ports=len(value['certificate']['boundary']['skeleton']['ports']),
                        interval_attachments=value['certificate']['boundary']['skeleton']['interval_attachments'])
            report['capacity'].append(data)
            print(json.dumps(data), flush=True)
            Path(args.output).write_text(json.dumps(json_safe(report), indent=2) + '\n')
    assert sources() == source_pins, 'native sources changed during benchmark'


if __name__ == '__main__':
    main()
