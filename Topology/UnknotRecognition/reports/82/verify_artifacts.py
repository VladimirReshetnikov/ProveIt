#!/usr/bin/env python3
"""Verify the original delivery's hashes, exact case count, and timing summaries.

Run this before regenerating data or the PDF: regenerated artifacts naturally
have different hashes. MIT-0.
"""
from pathlib import Path
import hashlib
import json
import math
import statistics
import sys
ROOT = Path(__file__).resolve().parent

def close(a, b):
    return math.isclose(a,b,rel_tol=1e-12,abs_tol=1e-12)

def main():
    manifest = ROOT/'SHA256SUMS'
    count = 0
    for line in manifest.read_text().splitlines():
        expected, name = line.split('  ',1)
        path = ROOT/name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(f'Content hash mismatch: {name}')
        count += 1
    validation = json.loads((ROOT/'data/validation.json').read_text())
    for table in ('source_sha256','evidence_sha256'):
        for name, expected in validation[table].items():
            if hashlib.sha256((ROOT/name).read_bytes()).hexdigest() != expected:
                raise ValueError(f'Evidence/source hash mismatch: {name}')
    exhaustive = sum(sum(math.factorial(p)//(math.factorial(p-2*j)*math.factorial(j))
                         for j in range(p//2+1)) for p in range(1,9))
    if exhaustive != 7688:
        raise ArithmeticError('Signed partial-pairing count changed')
    data = json.loads((ROOT/'data/benchmark.json').read_text())
    for row in data['cases']:
        values = row['samples_ns']
        if len(values) != data['rounds'] or row['warmup_ns']['round'] != -1:
            raise ValueError('Incomplete timing rounds')
        expected = {
            'kernel_median_ms':statistics.median(x['kernel'] for x in values)/1e6,
            'literal_median_ms':statistics.median(x['literal'] for x in values)/1e6,
            'paired_ratio':statistics.median(x['literal']/x['kernel'] for x in values),
            'aa_control_ratio':statistics.median(x['literal']/x['literal_control'] for x in values)
        }
        if any(not close(row[k],v) for k,v in expected.items()):
            raise ValueError('Timing summary disagrees with raw samples')
        if row['physical_boundary_edges'] != 16*(row['gap_length']+1) or row['kernel_edges'] != 32:
            raise ValueError('Incorrect boundary size')
        if row['signature'] != [[-6,4,True]]:
            raise ValueError('Unexpected benchmark topology')
    for row in data['huge_compiler']:
        if not close(row['median_ms'],statistics.median(row['samples_ns'])/1e6):
            raise ValueError('Binary benchmark median mismatch')
        if (row['ports'],row['kernel_edges'],row['orbit_count_calls'],row['maximum_extra_pairings']) != (12,24,113,23):
            raise ValueError('Binary benchmark invariant mismatch')
    print(f'PASS: {count} content hashes; source/evidence pins; {exhaustive} pairing count; all raw timing summaries.')
    print('This checks delivery integrity and arithmetic, not native source geometry or an unknot-recognition theorem.')

if __name__ == '__main__':
    try:
        main()
    except (OSError,ValueError,KeyError,ArithmeticError) as exc:
        print(f'FAIL: {exc}',file=sys.stderr)
        sys.exit(1)
