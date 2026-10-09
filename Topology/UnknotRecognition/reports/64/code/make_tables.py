"""Render article tables from retained JSON, without rerunning experiments."""
from pathlib import Path
import csv
import json
ROOT = Path(__file__).resolve().parents[1]
results = ROOT/'results'
audit = json.loads((results/'audit.json').read_text())
bench = json.loads((results/'benchmark.json').read_text())
lines = []
for f in bench['fixtures']:
    s = f['summary']
    lines.append(f"{f['r']} & {f['input_rows']:,} & {s['cut']['kept_rows']:,} & {s['exterior']['kept_rows']:,} & {f['queries']:,} & {1000*s['full']['total_seconds']:.2f} & {1000*s['exterior']['total_seconds']:.2f} & {f['paired_full_over_total']['exterior']:.2f} \\\\")
(results/'benchmark_table.tex').write_text('\n'.join(lines)+'\n')
with (results/'benchmark_summary.csv').open('w', newline='') as out:
    writer = csv.writer(out)
    writer.writerow(['fixture','r','input_rows','cut_kept','exterior_kept','queries','full_total_ms','exterior_total_ms','paired_full_over_exterior'])
    for f in bench['fixtures']:
        s=f['summary']
        writer.writerow([f['name'],f['r'],f['input_rows'],s['cut']['kept_rows'],s['exterior']['kept_rows'],f['queries'],1000*s['full']['total_seconds'],1000*s['exterior']['total_seconds'],f['paired_full_over_total']['exterior']])
lines = []
for f in audit['rank_table']:
    lines.append(f"{f['r']} & {f['partitions']} & {f['disc_matrix_rank']} & {f['cut_kept']} & " + ', '.join(map(str,f['grade_ranks'])) + r' \\')
(results/'rank_table.tex').write_text('\n'.join(lines)+'\n')
print('Rebuilt tables from existing JSON.')
