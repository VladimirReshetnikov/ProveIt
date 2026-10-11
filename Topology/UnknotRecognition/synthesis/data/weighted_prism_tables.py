"""Regenerate the paired contraction and port-encoding tables from saved samples."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def table(header, rows):
    return ('\\begin{center}\n\\small\n\\begin{tabular}{@{}lrrrr@{}}\n\\toprule\n' +
            header + ' \\\\\n\\midrule\n' + '\n'.join(row + ' \\\\' for row in rows) +
            '\n\\bottomrule\n\\end{tabular}\n\\end{center}\n')


sweep = json.loads((ROOT/'data/weighted-sweep-benchmark.json').read_text())
rows = []
for name, summary in sweep['summary'].items():
    details = sweep['details'][name]
    if name.startswith('local_'):
        label = f"{details['runs']:,} runs, " + ('many gaps' if details['gaps'] else 'no gaps')
    else:
        label = f"Complete query, $T={details['tetrahedra']}$"
    rows.append(f"{label} & {1000*summary['median_seconds']['sorted']:.3f} & "
                f"{1000*summary['median_seconds']['sweep']:.3f} & "
                f"{summary['paired_sorted_over_sweep']:.3f} & {summary['paired_identical_control']:.3f}")
(ROOT/'tables/weighted_sweep.tex').write_text(table('Task & Sorted ms & Sweep ms & Ratio & A/A', rows))

encoding = json.loads((ROOT/'data/prism-port-encoding-benchmark.json').read_text())
rows = []
for name, summary in encoding['summary'].items():
    details = encoding['details'][name]
    label = f"$T={details['tetrahedra']}$, $P={details['ports']}$"
    if details['maximum_coordinate_bits'] > 100:
        label += ', 501-bit copies'
    rows.append(f"{label} & {1000*summary['median_seconds']['vector']:.3f} & "
                f"{1000*summary['median_seconds']['auto']:.3f} & "
                f"{summary['paired_vector_over_auto']:.3f} & {summary['paired_identical_control']:.3f}")
(ROOT/'tables/prism_port_encoding.tex').write_text(table('Source & Vector ms & Auto ms & Ratio & A/A', rows))
