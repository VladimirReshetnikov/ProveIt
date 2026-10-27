#!/usr/bin/env python3
"""Exact abstract mode counts, with finite cases that can favor the old basis.

This models enumeration inventories, not complete SAT runtimes.
"""
from pathlib import Path
import csv
import io
import json
from pivot21_validation import weight, vf


def old_weight(b):
    return 1 + b + 2*vf(b)


def count_series(max_budget, colors, weights):
    """Return coefficients through max_budget-1 of product (1-x^w)^(-colors)."""
    dp = [0]*max_budget
    dp[0] = 1
    b = 0
    while weights(b) < max_budget:
        w = weights(b)
        for _ in range(colors):
            for p in range(w, max_budget):
                dp[p] += dp[p-w]
        b += 1
    totals = [0]
    running = 0
    for value in dp:
        running += value
        totals.append(running)
    return totals


def main():
    budgets = (16, 32, 64, 128, 256, 512, 1024)
    rows = []
    for colors in (1, 2, 4):
        old = count_series(max(budgets), colors, old_weight)
        new = count_series(max(budgets), colors, weight)
        for p in budgets:
            rows.append({'precision_budget': p, 'families': colors,
                         'old_tuple_count': str(old[p]),
                         'new_tuple_count': str(new[p]),
                         'smaller_inventory': 'new' if new[p] < old[p] else
                                              'old' if old[p] < new[p] else 'equal'})
    out = Path(__file__).resolve().parents[1] / 'results'
    out.mkdir(exist_ok=True)
    payload = {'scope': 'exact finite abstract inventories, not solver benchmarks',
               'strict_budget': True,
               'example_b4': {'old_weight': old_weight(4), 'new_weight': weight(4)},
               'rows': rows}
    (out/'mode_counts.json').write_text(json.dumps(payload, indent=2)+'\n')
    buffer = io.StringIO()
    writer = csv.DictWriter(buffer, fieldnames=list(rows[0]))
    writer.writeheader()
    writer.writerows(rows)
    (out/'mode_counts.csv').write_text(buffer.getvalue())
    print(json.dumps({'cases': len(rows), 'strict_budget': True,
                      'new_smaller': sum(x['smaller_inventory']=='new' for x in rows),
                      'old_smaller': sum(x['smaller_inventory']=='old' for x in rows),
                      'equal': sum(x['smaller_inventory']=='equal' for x in rows)}, indent=2))


if __name__ == '__main__':
    main()
