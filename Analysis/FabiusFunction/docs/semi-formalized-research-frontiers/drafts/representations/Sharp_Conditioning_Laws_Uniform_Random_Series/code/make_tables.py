#!/usr/bin/env python3
"""Regenerate the two small LaTeX table fragments from delivered CSVs."""
import csv
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
with (ROOT/'data'/'simplex_comparison.csv').open() as handle:
    rows = list(csv.DictReader(handle))
with (ROOT/'data'/'simplex_rows.tex').open('w') as handle:
    for row in rows:
        if float(row['alpha']) == 0.5:
            line = (f"{row['n']} & {row['k']} & {float(row['tv']):.7f} & "
                    f"{float(row['kl']):.7f} & " + r"$0.1660641\,/\,0.0965736$ \\")
            handle.write(line+'\n')
    handle.write('\\bottomrule\n')
with (ROOT/'data'/'geometric_experiments.csv').open() as handle:
    rows = list(csv.DictReader(handle))
with (ROOT/'data'/'geometric_rows.tex').open('w') as handle:
    for row in rows:
        line = (f"{row['n']} & {int(row['accepted']):,} & {float(row['slack_mean']):.4f} & "
                f"{float(row['slack_mean_se']):.4f} & {float(row['bridge_variance_half']):.4f} & "
                f"{float(row['boundary_mean']):.4f} " + r"\\")
        handle.write(line+'\n')
    handle.write('\\bottomrule\n')
