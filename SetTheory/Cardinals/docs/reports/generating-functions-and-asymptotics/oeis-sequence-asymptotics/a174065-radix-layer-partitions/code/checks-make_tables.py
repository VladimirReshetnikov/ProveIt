"""Generate the article's numeric tables from replayed JSON check results."""
from pathlib import Path
import json
from decimal import Decimal
import argparse
p=argparse.ArgumentParser();p.add_argument('--data',type=Path,default=Path(__file__).parent);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
counts=json.loads((a.data/'coefficient-checks.json').read_text())
inverse=json.loads((a.data/'inverse-checks.json').read_text())
def sci(x):
 d=Decimal(x)
 if not d:return '$0$'
 e=d.adjusted();m=d.scaleb(-e)
 return '$'+f'{m:.3f}'+r'\times10^{'+str(e)+'}$'
lines=[r'\begin{table}[htbp]',r'\centering\small',r'\setlength{\tabcolsep}{4pt}',r'\begin{tabular}{@{}rrccccc@{}}',r'\toprule',r'$b$ & $n$ & Order $0$ & Order $1$ & Order $2$ & Order $3$ & Order $4$ \\',r'\midrule']
for b in ['4','8']:
 for row in counts[b]['checks']:
  if row['n'] in [400,2500,10000]:
   lines.append(b+' & '+str(row['n'])+' & '+' & '.join(sci(x) for x in row['relative_errors_orders_0_to_4'])+r' \\')
lines += [r'\bottomrule',r'\end{tabular}',r'\caption{Relative errors in the shifted coefficient expansion. Decimal values are high-precision checks, not certified error bounds.}',r'\label{tab:counts}',r'\end{table}',r'\begin{table}[htbp]',r'\centering',r'\begin{tabular}{@{}rcc@{}}',r'\toprule',r'$b$ & Order $4$ inverse error & Inverse error omitting $P$ \\',r'\midrule']
for b in ['4','8']:
 row=next(r for r in inverse[b] if r['n']==10000)
 lines.append(b+' & '+sci(row['inverse_index_errors_orders_0_to_4'][4])+' & '+sci(row['inverse_error_ignoring_periodic_factor_order4'])+r' \\')
lines += [r'\bottomrule',r'\end{tabular}',r'\caption{Continuous inverse index error at the exact target $y=a_b(10000)$, measured as approximate root minus $10000$. The final column sets $P$ and its derivatives to zero at the same truncation order.}',r'\label{tab:inverse}',r'\end{table}',r'\noindent The direct reciprocity check uses 90 decimal working precision and seven $(b,t)$ pairs with $b\in\{2,3,4,8,16\}$. Its largest observed absolute residual in \eqref{eq:reciprocitylog} is below $2.3\times10^{-91}$. These computations use direct positive-real products on both sides and a separately summed Fourier series.']
a.output.write_text('\n'.join(lines)+'\n')
