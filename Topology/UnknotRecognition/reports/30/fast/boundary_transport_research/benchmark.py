"""Reproducible compressed-query timings and a literal cyclic-cover baseline."""

from collections import deque
import argparse
import json
from math import gcd
from pathlib import Path
import platform
from statistics import median
import time

from bootstrap import enable_fast
enable_fast()
from fastunknot.boundary_transport import BoundaryTransportIndex
from audit import example


def literal_cycle_scan(n, shifts, constraints):
    # Materialize each peripheral permutation's orbit labels independently.
    labels = []
    for shift in shifts:
        current_labels = [-1]*n
        for root in range(n):
            if current_labels[root] != -1:
                continue
            x = root
            while current_labels[x] == -1:
                current_labels[x] = root
                x = (x+shift) % n
        labels.append(current_labels)
    return sum(all(labels[boundary][(x+a) % n] == labels[boundary][y]
                   for boundary,x,y in constraints)
               for a in range(n))


def median_query(index, constraints, expected, repetitions=11):
    times = []
    last = None
    for _ in range(repetitions):
        start = time.perf_counter()
        last = index.transports(0,0,boundary_pairs=constraints)
        times.append(time.perf_counter()-start)
        assert last['isomorphism_count'] == expected
    return median(times),last


def benchmark():
    result = {'python': platform.python_version(), 'platform': platform.platform(),
              'timing_clock': 'perf_counter',
              'timing_scope': 'prepared query; parsing/classification excluded',
              'literal_scaling': [], 'binary_scaling': [], 'paired_scaling': []}
    for bits in (8,12,16,20):
        n = 1 << bits
        a,b = 1 << (bits//3),1 << (2*bits//3)
        shifts = [1,a,b]
        constraints = [(1,0,17),(2,0,17)]
        index = BoundaryTransportIndex(example(n,[(1,s) for s in shifts]))
        exact = n//b
        compressed_seconds,answer = median_query(index,constraints,exact)
        start = time.perf_counter()
        literal = literal_cycle_scan(n,shifts,constraints)
        literal_seconds = time.perf_counter()-start
        assert literal == exact
        result['literal_scaling'].append({'sheets':n,'sheet_bits':n.bit_length(),
            'constraints':len(constraints),'isomorphism_count':exact,
            'progressions':len(answer['root_progressions']),
            'compressed_median_seconds':compressed_seconds,
            'literal_seconds':literal_seconds,
            'speedup_ratio':literal_seconds/compressed_seconds})
    for exponent in (16,128,1024,4096,12000):
        a,b,c = 2**exponent,3**exponent,5**exponent
        n = a*b*c
        raw = example(n,[(1,1),(1,a),(1,b)])
        start = time.perf_counter()
        polls = 0
        def check():
            nonlocal polls
            polls += 1
        index = BoundaryTransportIndex(raw,check=check)
        preparation_seconds = time.perf_counter()-start
        constraints = [(1,0,17),(2,0,17)]
        median_seconds,answer = median_query(index,constraints,c)
        polls = 0
        index.transports(0,0,boundary_pairs=constraints)
        result['binary_scaling'].append({'exponent':exponent,'sheet_bits':n.bit_length(),
            'constraints':2,'isomorphism_count_bits':c.bit_length(),
            'progressions':len(answer['root_progressions']),
            'preparation_seconds':preparation_seconds,
            'query_median_seconds':median_seconds,'query_poll_count':polls})
    for bits in (32,256,2048,8192,24000):
        d,m = 1 << bits,(1 << bits)+1
        index = BoundaryTransportIndex(example(d*m,[(1,d),(-1,0)]))
        times = []
        for _ in range(11):
            start = time.perf_counter()
            answer = index.transports(1,3,boundary_pairs=[(1,1,3)])
            times.append(time.perf_counter()-start)
            assert answer['isomorphism_count'] == 2
        result['paired_scaling'].append({'sheet_bits':(d*m).bit_length(),
            'constraints':1,'isomorphism_count':2,
            'progressions':len(answer['root_progressions']),
            'query_median_seconds':median(times)})
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',default=str(Path(__file__).with_name('benchmark-results.json')))
    args = parser.parse_args()
    result = benchmark()
    text = json.dumps(result,indent=2,sort_keys=True)+'\n'
    Path(args.output).write_text(text)
    print(text,end='')
