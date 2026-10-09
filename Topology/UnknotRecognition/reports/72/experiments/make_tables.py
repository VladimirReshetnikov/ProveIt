"""Regenerate the manuscript tables from executed audits, never from estimates."""
import json
from pathlib import Path

a = json.loads(Path('results/audit.json').read_text())
b = json.loads(Path('results/benchmark.json').read_text())
lines = [r'\begin{tabular}{rrrr}', r'\toprule', r'$r$ & Decorated states & Checked pairs & Binary rank\\', r'\midrule']
for row in a['uncharged']:
    lines.append(f"{row['r']} & {row['states']:,} & {row['pairs']:,} & {row['rank']:,}\\\\")
lines += [r'\bottomrule', r'\end{tabular}']
Path('results/algebra_table.tex').write_text('\n'.join(lines)+'\n')
lines = [r'\begin{tabular}{lrrrrr}', r'\toprule', r'Workload & Exact (ms) & Basis (ms) & Ratio & A/A ratio\\', r'\midrule']
# Five columns; no undocumented rounding or timings from the abandoned pilot.
lines[0] = r'\begin{tabular}{lrrrr}'
for row in b['cases']:
    lines.append(f"{row['name']} & {1000*row['median_seconds']['exact']:.3f} & {1000*row['median_seconds']['basis']:.3f} & {row['speedup_exact_over_basis']:.2f} & {row['aa_ratio']:.2f}\\\\")
lines += [r'\bottomrule', r'\end{tabular}']
Path('results/timing_table.tex').write_text('\n'.join(lines)+'\n')
lines = [r'\begin{tabular}{lrrrr}', r'\toprule', r'Workload & Exact transitions & Basis transitions & Exact peak & Basis peak\\', r'\midrule']
for row in b['cases']:
    e, r = row['stats']['exact'], row['stats']['basis']
    lines.append(f"{row['name']} & {e['transitions']:,} & {r['transitions']:,} & {e['peak_retained']:,} & {r['peak_retained']:,}\\\\")
lines += [r'\bottomrule', r'\end{tabular}']
Path('results/state_table.tex').write_text('\n'.join(lines)+'\n')
byname = {row['name']: row for row in b['cases']}
wide = [byname['width-'+str(w)] for w in (3,4,5)]
macros = {
    'WideMinSpeedup': f"{min(x['speedup_exact_over_basis'] for x in wide):.2f}",
    'WideMaxSpeedup': f"{max(x['speedup_exact_over_basis'] for x in wide):.2f}",
    'WThreeRatio': f"{byname['width-3']['speedup_exact_over_basis']:.2f}",
    'WFourRatio': f"{byname['width-4']['speedup_exact_over_basis']:.2f}",
    'WFiveRatio': f"{byname['width-5']['speedup_exact_over_basis']:.2f}",
    'NoResetExactMS': f"{1000*byname['no-reset-control']['median_seconds']['exact']:.3f}",
    'NoResetBasisMS': f"{1000*byname['no-reset-control']['median_seconds']['basis']:.3f}",
    'RuntimePython': a['python'].split()[0],
}
Path('results/measurement_macros.tex').write_text('\n'.join('\\newcommand{\\'+key+'}{'+value+'}' for key,value in macros.items())+'\n')
