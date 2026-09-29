#!/usr/bin/env python3
"""Reproduce article tables from recorded recurrence output.

Run verify_exact.py and diagnostics.py first. These tables are floating-point
comparisons of exact or positive-recursion coefficients, not certified bounds.
"""
from __future__ import annotations
import csv, json, math
from pathlib import Path
import numpy as np
from diagnostics import bare_saddle, finite_core_saddle
ROOT = Path(__file__).resolve().parents[1]

def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)

def main() -> None:
    data = ROOT/'data'
    cutoff_rows, inverse_rows, agreements = [], [], []
    for p in (2, 3):
        logs = np.load(data/f'log_coefficients_p{p}.npz')['log_u']
        n = len(logs)-1
        for M in range(1, 5):
            cs = finite_core_saddle(n, p, M)
            cutoff_rows.append({'p':p, 'n':n, 'M':M,
                'ratio':math.exp(float(logs[n])-cs['log_approx']),
                'saddle_action':cs['j'], 'saddle_q':cs['q'],
                'saddle_residual':cs['residual']})
        max_error = 0.0
        with (data/f'exact_p{p}.csv').open() as stream:
            for row in csv.DictReader(stream):
                n = int(row['n']); b = int(row['n_factorial_times_u_n'])
                c = int(row['n_factorial_times_v_n'])
                if n < len(logs):
                    max_error = max(max_error,
                        abs(math.log(b)-math.lgamma(n+1)-float(logs[n])))
                if n in (20, 50, 100, 200, 300):
                    bs = bare_saddle(n,p)
                    conjectured_log_abs = bs['logS']-2*bs['k']/bs['j']**(p-1)
                    inverse_rows.append({'p':p,'n':n,'minus_v_over_u':-c/b,
                        'inverse_over_conjectured_extension':
                            (-1 if c > 0 else 1)*math.exp(math.log(abs(c))-
                             math.lgamma(n+1)-conjectured_log_abs),
                        'status_of_extension':('quadratic extension conjectural' if p == 2 else
                           'leading equivalence proved; refined correction not proved')})
        agreements.append({'p':p,'max_absolute_log_discrepancy':max_error})
    write_csv(data/'core_cutoff_table.csv', cutoff_rows)
    write_csv(data/'inverse_diagnostics.csv', inverse_rows)
    (data/'cross_checks.json').write_text(json.dumps(agreements,indent=2)+'\n')
    with (data/'table_cutoff.tex').open('w') as stream:
        for row in cutoff_rows:
            stream.write(f"{row['p']} & {row['M']} & {row['ratio']:.9f} & "
                         f"{row['saddle_action']:.5f} \\\\\n")
    with (data/'table_inverse.tex').open('w') as stream:
        for row in inverse_rows:
            if row['n'] in (50,100,200,300):
                stream.write(f"{row['p']} & {row['n']} & {row['minus_v_over_u']:.9f} & "
                             f"{row['inverse_over_conjectured_extension']:.6f} \\\\\n")
    print(json.dumps({'cutoff_rows':cutoff_rows,'inverse_rows':inverse_rows,
                      'cross_checks':agreements},indent=2))

if __name__ == '__main__': main()
