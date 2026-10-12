"""Paired complete source classification and binary finite-model measurements."""

import argparse
import gc
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time

from unsaturated_bundles import make_certificate, verify_certificate
from unsaturated_bundles.finite import encode
from unsaturated_bundles.native import (
    normal_cut_unsaturated_handlebodies, verify_normal_cut_unsaturated_handlebodies)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--corpus', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--rounds', type=int, default=5)
    args = parser.parse_args()
    from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    from fastunknot.integer_codec import json_safe
    from marked_parallelity_research.audit_census import oracle
    from normal_orbit_research.fixtures import layered_torus
    corpus = json.loads(Path(args.corpus).read_text())
    ids = {'pilot/lst_5_7/0', 'pilot/pachner23_3_5_1/0',
           'pilot/pachner23_5_8_1/0', 'pilot/pachner23_5_8_2/0', 'lst_3_8/mixed'}
    cases = [case for case in corpus['cases'] if case['id'] in ids]
    for t, mult in [(1, 1), (4, 8), (8, 1)]:
        raw, normal = layered_torus(t)
        cases.append(dict(id=f'preserved_layered_{t}_copies_{mult}', triangulation=raw,
                          coordinates=[[mult * n for n in row] for row in normal]))
    rng, rows = random.Random(26101221), []
    for case in cases:
        raw, normal = case['triangulation'], case['coordinates']

        def native():
            out = normal_cut_unsaturated_handlebodies(raw, normal, record_certificate=True)
            assert out['status'] == 'COMPLETE'
            assert verify_normal_cut_unsaturated_handlebodies(raw, normal, out['certificate'])
            return out['census']['histogram']

        def old():
            out = normal_cut_handlebodies(raw, normal, record_certificate=True)
            if out['status'] == 'COMPLETE':
                assert verify_normal_cut_handlebodies(raw, normal, out['certificate'])
            return out

        expected = native()
        legacy = old()
        assert oracle(case)['histogram'] == expected
        samples = []
        for _ in range(args.rounds):
            order = ['native', 'regina', 'old']
            rng.shuffle(order)
            sample = dict(order=order)
            for name in order:
                gc.collect()
                start = time.perf_counter()
                if name == 'native':
                    assert native() == expected
                elif name == 'regina':
                    assert oracle(case)['histogram'] == expected
                else:
                    current = old()
                    assert current['status'] == legacy['status']
                    if current['status'] == 'COMPLETE':
                        assert current['census']['histogram'] == expected
                sample[name] = time.perf_counter() - start
            samples.append(sample)
        row = dict(id=case['id'], old_status=legacy['status'], old_reason=legacy.get('reason'),
            histogram=expected, native_median=statistics.median(s['native'] for s in samples),
            regina_median=statistics.median(s['regina'] for s in samples),
            old_median=statistics.median(s['old'] for s in samples), samples=samples)
        # Ratios comparing differing answers are deliberately not produced.
        if legacy['status'] == 'COMPLETE':
            row['old_over_new_paired_median'] = statistics.median(
                s['old'] / s['native'] for s in samples)
        rows.append(row)
        print(json.dumps({k:v for k,v in row.items() if k != 'samples'}), flush=True)
    binary = []
    for bits in (128, 1024, 4096, 16384):
        g = (1 << bits) + 17
        model = dict(cores=[dict(id=0, genus=0)],
            bases=[dict(id=0, chi=-2*g, boundary=2, orientable=True, multiplicity=1)],
            attachments=[dict(id=0, base=0, core=0, kind='circle')])
        samples = []
        for _ in range(args.rounds):
            start = time.perf_counter()
            out = make_certificate(model)
            assert out['census']['histogram'] == [dict(genus=2*g, multiplicity=1)]
            assert verify_certificate(model, out['certificate'])
            samples.append(time.perf_counter() - start)
        binary.append(dict(genus_bits=g.bit_length(), median=statistics.median(samples),
            input_bytes=len(json.dumps(encode(model), sort_keys=True)),
            certificate_bytes=len(json.dumps(encode(out['certificate']), sort_keys=True)),
            one_handle_count=hex(2*g), samples=samples))
    report = dict(scope='Complete source-cut production+replay and exact explicit-cut oracle',
        caveat='Old INCONCLUSIVE timing has a different outcome and is not a speed baseline',
        python=sys.version, platform=platform.platform(), rounds=args.rounds,
        seed=26101221, cases=rows, binary=binary)
    Path(args.output).write_text(json.dumps(json_safe(report), indent=2) + '\n')


if __name__ == '__main__':
    main()
