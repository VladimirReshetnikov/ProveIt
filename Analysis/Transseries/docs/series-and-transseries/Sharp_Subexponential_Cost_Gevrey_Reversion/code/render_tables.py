#!/usr/bin/env python3
"""Regenerate the supplied LaTeX table fragments from diagnostic CSV files."""
from __future__ import annotations
import argparse
import csv
from pathlib import Path

def main() -> None:
    root=Path(__file__).resolve().parents[1]
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',type=Path,default=root/'data'/'recorded')
    p.add_argument('--output',type=Path,default=root/'data')
    args=p.parse_args(); args.output.mkdir(parents=True,exist_ok=True)
    with (args.input/'diagnostics.csv').open(newline='',encoding='utf-8') as f:
        rows=list(csv.DictReader(f))
    lines=[]
    for r in rows:
        if r['nu']=='0' and r['n'] in ('320','1280'):
            fields=[f"{float(r['s']):g}",r['n']]
            fields += [f"{float(r[k]):.6f}" for k in
                       ('log_R','log_R_over_n_power','log_R_minus_n_power')]
            lines.append(' & '.join(fields)+r' \\')
    if len(lines)!=10:
        raise ValueError('Expected ten rows for the main article table.')
    (args.output/'diagnostic_table.tex').write_text(
        '\n'.join(lines)+'\n\\bottomrule\n',encoding='utf-8')
    with (args.input/'crossover.csv').open(newline='',encoding='utf-8') as f:
        rows=list(csv.DictReader(f))
    lines=[]
    for r in rows:
        if r['n']=='1280':
            fields=[f"{float(r['tau']):g}"]
            fields += [f"{float(r[k]):.6f}" for k in ('s','R','predicted_limit')]
            lines.append(' & '.join(fields)+r' \\')
    if len(lines)!=5:
        raise ValueError('Expected five crossover rows.')
    (args.output/'crossover_table.tex').write_text(
        '\n'.join(lines)+'\n\\bottomrule\n',encoding='utf-8')

if __name__=='__main__':
    main()
