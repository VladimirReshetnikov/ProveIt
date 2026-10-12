"""Compressed cover topology versus sheet expansion; NOT knot recognition.

Seven shuffled paired warm rounds. Input construction and result comparisons
are outside timing; each classifier computes all topology from its input.
Marked queries reuse one prepared index and are reported separately.
"""
import argparse
import gc
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
from time import perf_counter

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))
sys.path.insert(0, str(FAST/'tests'))
from fastunknot.integer_codec import json_safe
from fastunknot.surface_cover import CoverIndex, classify_cover
from test_surface_cover import expanded_oracle, compressed_signature


def source(n, maps, *, orientable=True, genus=0):
    return dict(surface=dict(orientable=orientable, genus=genus,
                             boundary_components=len(maps)-(2*genus if orientable else genus)+1),
                sheets=n, monodromy=[dict(sign=s, shift=a) for s,a in maps])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rng = random.Random(2026100824)
    paths = ['fastunknot/surface_cover.py', 'fastunknot/integer_codec.py',
             'tests/test_surface_cover.py', 'cover_research/benchmark.py']
    result = dict(scope=__doc__, python=platform.python_version(),
                  rounds=7, seed=2026100824, gc='enabled; collect before each batch',
                  source_sha256={p:hashlib.sha256((FAST/p).read_bytes()).hexdigest() for p in paths},
                  topology=[], marked_queries=[])
    def save():
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    for bits in (4,8,12,16):
        n = 1 << bits
        for name, raw in [('annulus',source(n,[(1,1)])),
                          ('mobius_reflection',source(n,[(-1,0)],orientable=False,genus=1)),
                          ('three_types',source(n,[(1,4),(-1,0),(-1,0)],genus=1))]:
            expected = expanded_oracle(raw)[0]
            assert compressed_signature(classify_cover(raw)) == expected
            arms = dict(compressed=lambda:classify_cover(raw), control=lambda:classify_cover(raw),
                        expanded=lambda:expanded_oracle(raw))
            samples = []
            for _ in range(7):
                order = list(arms); rng.shuffle(order)
                sample = dict(order=order, seconds={})
                for arm in order:
                    repeats = 1 if arm == 'expanded' else 32
                    gc.collect()
                    start = perf_counter()
                    values = [arms[arm]() for _ in range(repeats)]
                    sample['seconds'][arm] = (perf_counter()-start)/repeats
                    for value in values:
                        actual = value[0] if arm == 'expanded' else compressed_signature(value)
                        assert actual == expected
                samples.append(sample)
            row = dict(name=name,sheets=n,families=len(classify_cover(raw)['families']),
                       repetitions=dict(compressed=32,control=32,expanded=1), samples=samples,
                       compressed_seconds=statistics.median(s['seconds']['compressed'] for s in samples),
                       expanded_over_compressed=statistics.median(
                           s['seconds']['expanded']/s['seconds']['compressed'] for s in samples),
                       control_over_compressed=statistics.median(
                           s['seconds']['control']/s['seconds']['compressed'] for s in samples))
            result['topology'].append(row)
            save()
            print(name,n,round(row['expanded_over_compressed'],3),flush=True)
    for bits in (32,1024,16384):
        d = 1 << (bits//2)
        n, m = 1 << bits, 1 << (bits-bits//2)
        raw = source(n,[(1,d),(-1,0)])
        start = perf_counter(); index = CoverIndex(raw); preparation = perf_counter()-start
        for count in (2,32,512):
            marks = tuple(((1 if j%2 == 0 else -1) + d*(j*m//count)) % n for j in range(count))
            moved = tuple((x+(2 if x%d == 1 else -2)) % n for x in marks)
            expected = index.marked_signature(1, marks)
            assert expected == index.marked_signature(3, moved)
            samples=[]
            for _ in range(7):
                order=['query','control'];rng.shuffle(order)
                sample=dict(order=order,seconds={})
                for arm in order:
                    gc.collect()
                    start=perf_counter()
                    values=[index.marked_signature(1, marks) for _ in range(16)]
                    sample['seconds'][arm]=(perf_counter()-start)/16
                    assert all(value==expected for value in values)
                samples.append(sample)
            row=dict(sheet_exponent=bits, marks=count, preparation_seconds=preparation,
                     signature_json_bytes=len(json.dumps(json_safe(expected)).encode()),
                     repetitions=16,samples=samples,
                     query_seconds=statistics.median(s['seconds']['query'] for s in samples),
                     control_over_query=statistics.median(
                         s['seconds']['control']/s['seconds']['query'] for s in samples))
            result['marked_queries'].append(row);save()
            print('marks',bits,count,row['query_seconds'],flush=True)


if __name__ == '__main__':
    main()
