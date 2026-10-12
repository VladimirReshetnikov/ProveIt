#!/usr/bin/env python3
"""Regenerate the article's tables from completed benchmark samples. MIT-0."""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent

def main():
    data = json.loads((ROOT/'data/benchmark.json').read_text())
    rows = [r'\begin{table}[htbp]\centering\small',
            r'\begin{tabular}{@{}rrrrrr@{}}\toprule',
            r'Gap $\ell$ & Physical edges & Kernel ms & Literal ms & Paired ratio & A/A \\\midrule']
    for r in data['cases']:
        rows.append(f"{r['gap_length']:,} & {r['physical_boundary_edges']:,} & "
                    f"{r['kernel_median_ms']:.3f} & {r['literal_median_ms']:.3f} & "
                    f"{r['paired_ratio']:.3f} & {r['aa_control_ratio']:.3f} \\\\")
    rows += [r'\bottomrule\end{tabular}',
             r'\caption{Complete local gluing query: a fixed 32-edge kernel versus literal boundary expansion. All seven paired rounds are retained; no native recognizer comparison is made.}',
             r'\label{tab:benchmark}\end{table}']
    (ROOT/'article/benchmark_table.tex').write_text('\n'.join(rows)+'\n')
    rows = [r'\begin{table}[htbp]\centering\small',
            r'\begin{tabular}{@{}rrrrr@{}}\toprule',
            r'Gap bits & Universe bits & Count calls & Output edges & Median ms \\\midrule']
    for r in data['huge_compiler']:
        rows.append(f"{r['gap_length_bits']:,} & {r['universe_bits']:,} & "
                    f"{r['orbit_count_calls']} & {r['kernel_edges']} & {r['median_ms']:.3f} \\\\")
    rows += [r'\bottomrule\end{tabular}',
             r'\caption{Compiler timing with exact analytic block-count oracles, not general AHT. Twelve ports are fixed throughout.}',
             r'\label{tab:binary}\end{table}']
    (ROOT/'article/binary_table.tex').write_text('\n'.join(rows)+'\n')

if __name__ == '__main__':
    main()
