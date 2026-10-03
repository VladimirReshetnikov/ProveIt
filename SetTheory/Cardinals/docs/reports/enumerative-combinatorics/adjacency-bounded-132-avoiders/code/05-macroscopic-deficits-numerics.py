"""Exact integer counts; floating point is used only for displayed ratios.

Use --section bulk or --section moments to regenerate the two CSVs separately.
The default regenerates both. Moderate-size numerical agreement is not an
asymptotic proof and does not provide a convergence-rate certificate.
"""
from __future__ import annotations

import argparse
import csv
import gc
import json
import math
from pathlib import Path
from model import Counter, catalans

ROOT = Path(__file__).resolve().parents[1]


def profile(x: float) -> float:
    if not 0 < x < 0.5:
        return 0.0
    return 3 / math.sqrt(math.pi) * (1-2*x) / math.sqrt(x*(1-x))


def exact_total(n: int, m: int) -> int:
    counter = Counter(n, m)
    result = counter.count()
    counter.T.cache_clear()
    return result


def write_rows(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)


def bulk() -> int:
    cases = [(n,d) for n in (40,80,160)
             for d in (n//5,3*n//10,2*n//5)] + [(320,96)]
    rows = []
    for n,d in cases:
        count, catalan = exact_total(n,n-d), catalans(n)[n]
        rows.append(dict(n=n,d=d,m=n-d,count=str(count),catalan=str(catalan),
                         scaled_probability=math.sqrt(n)*(count/catalan),
                         profile=profile(d/n)))
        gc.collect()
    write_rows(ROOT/'data/bulk_counts.csv',rows)
    return len(rows)


def moments() -> int:
    rows = []
    for n in (20,40,80):
        counts = [0]
        for m in range(1,n):
            counts.append(exact_total(n,m))
            gc.collect()
        catalan = catalans(n)[n]
        mean_numerator = sum(counts)
        second_numerator = sum((2*(n-m)-1)*counts[m] for m in range(1,n))
        rows.append(dict(
            n=n,mean_numerator=str(mean_numerator),
            second_numerator=str(second_numerator),catalan=str(catalan),
            scaled_mean=(mean_numerator/catalan)/math.sqrt(n),
            scaled_second=(second_numerator/catalan)/(n**1.5),
            mean_limit=3/math.sqrt(math.pi),
            second_limit=3/math.sqrt(math.pi)*(1-math.pi/4)))
    write_rows(ROOT/'data/moment_counts.csv',rows)
    return len(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--section', choices=('all','bulk','moments'),default='all')
    args = parser.parse_args()
    result = {}
    if args.section in ('all','bulk'):
        result['bulk_cases'] = bulk()
    if args.section in ('all','moments'):
        result['moment_cases'] = moments()
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
