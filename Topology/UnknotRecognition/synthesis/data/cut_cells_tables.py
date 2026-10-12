"""Generate complete labelled-cut representation tables from saved paired runs."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
record = json.loads((ROOT/'data/cut-cells-benchmark.json').read_text())
rows = []
for name in sorted(record['summary'], key=lambda n: (int(n.split('_')[1]), int(n.split('_')[-1]))):
    t, n = int(name.split('_')[1]), int(name.split('_')[-1]); s = record['summary'][name]
    label = 'copy' if n == 1 else 'copies'
    rows.append(f"$T={t}$, {n:,} {label} & {1000*s['median_seconds']['regina']:.3f} & "
                f"{1000*s['median_seconds']['native']:.3f} & {s['paired_regina_over_native']:.3f} & {s['identical_control']:.3f}")
text = ('\\begin{center}\n\\small\n\\begin{tabular}{@{}lrrrr@{}}\n\\toprule\n'
        'Source & Regina ms & Native ms & Ratio & A/A \\\\\n\\midrule\n'+
        '\n'.join(row+' \\\\' for row in rows)+'\n\\bottomrule\n\\end{tabular}\n\\end{center}\n')
(ROOT/'tables/cut_cells.tex').write_text(text)
