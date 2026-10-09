"""Generate paper tables only from retained experiment outputs."""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT/'results'/'benchmarks.json').read_text())
lines = [r'\begin{table}[htbp]', r'\centering\small',
         r'\begin{tabular}{rrrrrr}', r'\toprule',
         r'$b$ & Length bits & Bisection trials & Descent trials & Bisection (ms) & Descent (ms)\\',
         r'\midrule']
for row in data['threshold']:
    b, length = row['delay_exponent'], row['expanded_length_bits']
    trials = row['last_outputs']
    med = row['median_ns']
    lines.append(f"{b} & {length} & {trials['prefix_bisection']['trials']} & {trials['descent']['trials']} & "
                 f"{med['prefix_bisection']/1e6:.3f} & {med['descent']/1e6:.5f}\\\\")
lines += [r'\bottomrule', r'\end{tabular}',
          r'\caption{First threshold in $(I^{2^b}A)^{2^b}$. Seven shuffled batched rounds; '
          r'times are median per-query costs. These are algebra-kernel measurements, not knot timings.}',
          r'\label{tab:threshold}', r'\end{table}']
(ROOT/'paper'/'threshold_table.tex').write_text('\n'.join(lines)+'\n')
lines = [r'\begin{table}[htbp]', r'\centering\small',
         r'\begin{tabular}{rrrrrr}', r'\toprule',
         r'Atoms $m$ & Grammar nodes & Length bits & Events & State trials & Time (ms)\\',
         r'\midrule']
for row in data['height']:
    lines.append(f"{row['atoms']} & {row['grammar_nodes']} & {row['expanded_length_bits']} & "
                 f"{row['sharp_event_bound']} & {row['last_outputs']['events']['trials']} & "
                 f"{row['median_ns']['events']/1e6:.4f}\\\\")
lines += [r'\bottomrule', r'\end{tabular}',
          r'\caption{Complete event histories on the sharp-height family, with $2^{2048}$ '
          r'empty instructions between effective operations and an outer $2^{4096}$ repetition.}',
          r'\label{tab:history}', r'\end{table}']
(ROOT/'paper'/'history_table.tex').write_text('\n'.join(lines)+'\n')
print('Generated paper tables from results/benchmarks.json')
