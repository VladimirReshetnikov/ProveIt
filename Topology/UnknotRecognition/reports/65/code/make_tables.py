"""Regenerate manuscript tables from retained JSON; does not rerun timings."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]

def main() -> None:
    a = json.loads((ROOT / 'results/audit.json').read_text())
    b = json.loads((ROOT / 'results/benchmark.json').read_text())
    if [z['width'] for z in b['measurements']] != [6, 7, 8] or b['repeats'] != 3:
        raise ValueError('The manuscript tables require the default widths 6,7,8 and three repeats.')
    rows = []
    for z in b['measurements']:
        rows.append(f"{z['width']} & {z['initial_candidates']:,} & {2**(z['width']-1):,} & "
                    f"{z['median_exact']:.5f} & {z['median_representative']:.5f} & "
                    f"{z['ratio_exact_over_representative']:.2f}\\\\")
    (ROOT / 'results/benchmark_table.tex').write_text(r'\begin{tabular}{rrrrrr}\toprule' + '\n' + r'$r$ & Initial states & Reduced states & Exact (s) & Reduced (s) & Ratio\\\midrule' + '\n' + '\n'.join(rows) + '\n' + r'\bottomrule\end{tabular}' + '\n')
    rows = []
    for z in b['measurements']:
        rows.append(f"{z['width']} & {z['exact_stats']['transition_attempts']:,} & "
                    f"{z['representative_stats']['transition_attempts']:,} & {z['optimum']} & "
                    f"{z['witness_replay']['triangle_count']}\\\\")
    (ROOT / 'results/work_table.tex').write_text(r'\begin{tabular}{rrrrr}\toprule' + '\n' + r'$r$ & Exact transitions & Reduced transitions & Optimum cost & Replay triangles\\\midrule' + '\n' + '\n'.join(rows) + '\n' + r'\bottomrule\end{tabular}' + '\n')
    c = b['no_reuse_control']
    ratios = [z['ratio_exact_over_representative'] for z in b['measurements']]
    (ROOT / 'results/measurements.tex').write_text(
        f"\\newcommand{{\\MinBenchRatio}}{{{min(ratios):.2f}}}\n"
        f"\\newcommand{{\\MaxBenchRatio}}{{{max(ratios):.2f}}}\n"
        f"\\newcommand{{\\WidthEightRatio}}{{{ratios[2]:.2f}}}\n"
        f"\\newcommand{{\\ControlExact}}{{{c['exact_seconds']:.5f}}}\n"
        f"\\newcommand{{\\ControlReduced}}{{{c['representative_seconds']:.5f}}}\n"
        f"\\newcommand{{\\ControlSlowdown}}{{{c['representative_seconds']/c['exact_seconds']:.2f}}}\n")

if __name__ == '__main__':
    main()
