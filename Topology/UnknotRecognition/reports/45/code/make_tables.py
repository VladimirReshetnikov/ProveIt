import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
B=json.loads((ROOT/'data/benchmark_results.json').read_text())
T=json.loads((ROOT/'data/test_summary.json').read_text())
rows=[]
for x in B['paired_kernel']:
    med=x['median_seconds']
    rows.append(f"{x['steps']} & {x['power_bits']} & {x['nodes']} & {x['expanded_length']:,} & "
                f"{1000*med['compressed']:.3f} & {1000*med['literal_whitehead']:.3f} & "
                f"{x['ratio_literal_over_compressed']:.1f}\\\\")
(ROOT/'docs/kernel_table.tex').write_text(r'\begin{tabular}{rrrrrrr}'+'\n'+r'\toprule'+'\n'+r'Fib. steps & Power bits & Nodes & Length & Width (ms) & Literal (ms) & Ratio \\'+'\n'+r'\midrule'+'\n'+'\n'.join(rows)+'\n'+r'\bottomrule'+'\n'+r'\end{tabular}'+'\n')
rows=[]
for x in B['large_kernel']:
    rows.append(f"{x['nodes']:,} & {x['expanded_length_bits']:,} & {1000*x['median_seconds']:.3f}\\\\")
(ROOT/'docs/large_table.tex').write_text(r'\begin{tabular}{rrr}'+'\n'+r'\toprule'+'\n'+r'Grammar nodes & Expanded length bits & Median query and replay (ms) \\'+'\n'+r'\midrule'+'\n'+'\n'.join(rows)+'\n'+r'\bottomrule'+'\n'+r'\end{tabular}'+'\n')
rows=[]
for x in B['parallel_contraction']:
    rows.append(f"{x['initial_rank']} & {x['initial_nodes']} & {x['depth']} & {x['final_nodes']} & {1000*x['seconds']:.2f}\\\\")
(ROOT/'docs/contraction_table.tex').write_text(r'\begin{tabular}{rrrrr}'+'\n'+r'\toprule'+'\n'+r'Initial rank & Initial nodes & Rounds & Final nodes & Run time (ms) \\'+'\n'+r'\midrule'+'\n'+'\n'.join(rows)+'\n'+r'\bottomrule'+'\n'+r'\end{tabular}'+'\n')
