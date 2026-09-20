#!/usr/bin/env python3
"""Produce a certified lower-bound sample, never infer equality from closeness.
Intervals have denominator 2**precision. Only pairwise disjoint intervals
are retained; an overlap is conservatively discarded, not declared equal.
The binary certificate is independently replayable with verify_certificate.py.
"""
from __future__ import annotations
import argparse, gc, json, math, struct, time
from pathlib import Path
ROOT = 0xffffffff
RECORD = struct.Struct('<BII')

def generate(max_n: int, precision: int, out: Path) -> None:
    if not 1 <= max_n <= 254 or precision < 32:
        raise ValueError('Require 1 <= max_n <= 254 and precision >= 32.')
    out.mkdir(parents=True, exist_ok=True)
    Q = 1 << precision
    low, high = [Q], [Q]
    births = [[] for _ in range(max_n + 1)]
    births[1] = [0]
    ordered = [0]
    counts = [0, 1]
    started = time.monotonic()
    with (out / 'digit_sample.bin').open('wb') as f:
        f.write(b'A158415D')
        f.write(struct.pack('<II', precision, max_n))
        f.write(RECORD.pack(1, ROOT, ROOT))
        for n in range(2, max_n + 1):
            candidates = []
            for a in births[n - 1]:
                l = math.isqrt(low[a] << precision)
                v = high[a] << precision
                u = math.isqrt(v)
                u += u * u < v
                candidates.append((l, u, a, ROOT))
            for i in range(1, (n - 1) // 2 + 1):
                j = n - 1 - i
                if i == j:
                    bjs = births[j]
                    for ai, a in enumerate(births[i]):
                        la, ua = low[a], high[a]
                        for b in bjs[ai:]:
                            candidates.append((la + low[b], ua + high[b], a, b))
                else:
                    for a in births[i]:
                        la, ua = low[a], high[a]
                        for b in births[j]:
                            candidates.append((la + low[b], ua + high[b], a, b))
            candidates.sort()
            pointer = 0
            previous_new_upper = -1
            new = births[n]
            for l, u, a, b in candidates:
                while pointer < len(ordered) and high[ordered[pointer]] < l:
                    pointer += 1
                if pointer < len(ordered) and low[ordered[pointer]] <= u:
                    continue
                if l <= previous_new_upper:
                    continue
                idx = len(low)
                low.append(l)
                high.append(u)
                new.append(idx)
                previous_new_upper = u
                f.write(RECORD.pack(n, a, b))
            ordered = ordered + new
            ordered.sort(key=low.__getitem__)
            counts.append(len(low))
            f.flush()
            print(n, len(new), len(low), 'candidates', len(candidates),
                  'seconds', round(time.monotonic() - started, 2), flush=True)
            del candidates
            gc.collect()
    metadata = {
        'sequence': 'A158415', 'max_n': max_n, 'precision_bits': precision,
        'sample_counts_at_most_n': counts[1:],
        'birth_counts_by_assigned_cost': [len(x) for x in births[1:]],
        'number_of_records': len(low),
        'certificate_type': 'distinct values with explicit expression costs',
        'not_claimed': 'completeness or exact minimum expression costs',
    }
    (out / 'certificate_metadata.json').write_text(json.dumps(metadata, indent=2)+'\n')

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--max-n', type=int, default=28)
    p.add_argument('--precision', type=int, default=256)
    p.add_argument('--output', type=Path, default=Path('data'))
    args = p.parse_args()
    generate(args.max_n, args.precision, args.output)
