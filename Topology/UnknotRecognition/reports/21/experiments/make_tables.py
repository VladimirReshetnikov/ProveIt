"""Generate the article's numerical macros and tables from recorded results."""
from common import *
import json,re

b=json.loads((ROOT/'results'/'benchmarks.json').read_text())
g=json.loads((ROOT/'results'/'geometry_validation.json').read_text())
grids=json.loads((ROOT/'results'/'descending_grids.json').read_text())['cases']
log=(ROOT/'results'/'unit_tests.txt').read_text()
tests=int(re.search(r'Ran (\d+) tests',log).group(1))
assert log.rstrip().endswith('OK')
best=max(b['matrix_cases'],key=lambda c:c['speedup'])
sparse=next(c for c in b['matrix_cases'] if c['parameters'].get('sparse'))
macros=dict(DenseSpeedup=f"{best['speedup']:.2f}",SparseSlowdown=f"{1/sparse['speedup']:.2f}",
            UnitTests=str(tests),GeometryAccepted=str(g['accepted']),GeometryDeclined=str(g['declined']),
            SmoothingChecks=f"{g['smoothing_checks']:,}",BenchmarkRepeats=str(b['environment']['repeats']),
            PythonVersion=b['environment']['python'],
            DenseBaseCompositions=f"{best['runs']['baseline'][0]['compositions']:,}",
            DenseNewCompositions=f"{best['runs']['radical'][0]['compositions']:,}")
(ROOT/'article'/'measurements.tex').write_text('% Generated from final result files; do not edit by hand.\n'+
    ''.join('\\newcommand{\\'+k+'}{'+v+'}\n' for k,v in macros.items()))
rows=[]
for c in b['matrix_cases']:
 p=c['parameters'];kind='sparse' if p.get('sparse') else ('mixed scalar' if p.get('scalar_mix') else 'dense')
 rows.append(f"{p['b']} & {p['m']} & {p['q']} & {kind} & {c['median_ms']['baseline']:.3f} & {c['median_ms']['radical']:.3f} & {c['speedup']:.2f}\\\\")
(ROOT/'article'/'matrix_table.tex').write_text(r'''\begin{table}[htbp]
\centering\small
\begin{tabular}{@{}rrrlrrr@{}}\toprule
$b$ & $m$ & $q$ & Pattern & Scalar (ms) & Transfer (ms) & Ratio\\\midrule
'''+ '\n'.join(rows)+r'''
\bottomrule\end{tabular}
\caption{Final paired stage-kernel timings. Ratio is scalar time divided by transfer time; below one is a regression. Source and target each have $m+q$ objects, with $2q$ survivors.}
\label{tab:matrix}
\end{table}
''')
short={'alternating-3-braid-12':'Alternating 3-braid, 12','cancelling-3-braid-14':'Cancelling 3-braid, 14',
       'mixed-4-braid-12':'Mixed 4-braid, 12','positive-4-braid-12':'Positive 4-braid, 12',
       'trefoil':'Trefoil','figure-eight':'Figure-eight','torus-3-5':'Torus $(3,5)$'}
rows=[]
for c in b['diagram_cases']:
 t=c['median_ms'];calls=c['runs']['adaptive'][0]['radical_stages']
 rows.append(f"{short[c['name']]} & {t['baseline']:.3f} & {t['always']:.3f} & {t['adaptive']:.3f} & {calls}\\\\")
(ROOT/'article'/'diagram_table.tex').write_text(r'''\begin{table}[htbp]
\centering\small
\begin{tabular}{@{}lrrrr@{}}\toprule
Presentation & Scalar (ms) & Eager (ms) & Adaptive (ms) & Block calls\\\midrule
'''+ '\n'.join(rows)+r'''
\bottomrule\end{tabular}
\caption{Complete fixed-order scanner timings, with the same source-derived fixture and fresh caches. The last column counts adaptive full block transfers, not scalar cancellations.}
\label{tab:diagram}
\end{table}
''')
rows=[]
for c in grids:
 check='rank two' if c['cube_ranks'] is not None else 'not computed'
 rows.append(f"{c['m']} & {c['crossings']} & {c['input_width']} & {c['certified_order_width']} & {check}\\\\")
(ROOT/'article'/'grid_table.tex').write_text(r'''\begin{table}[htbp]
\centering\small
\begin{tabular}{@{}rrrrl@{}}\toprule
$m$ & Crossings & Input-order width & Ear-order width & Independent cube\\\midrule
'''+ '\n'.join(rows)+r'''
\bottomrule\end{tabular}
\caption{Explicit descending-grid unknots. Width counts frontier points, not half-width. Ear insertion supplies certification but can worsen width; it is not an optimizer. All listed descending traversals are verified.}
\label{tab:grid}
\end{table}
''')
summary=dict(unit_tests=tests,unit_status='passed',unit_braid_cube_cases=100,
             geometric_braid_cube_cases=g['accepted'],smoothing_checks=g['smoothing_checks'],
             exported_chain_certificates=7,grid_sizes_verified=list(range(1,9)),grid_cube_sizes=[1,2,3],
             best_synthetic_ratio=best['speedup'],sparse_slowdown=1/sparse['speedup'],
             adaptive_full_block_calls_in_diagram_benchmark=0,
             production_checkout_tested=False,rust_tested=False,formally_verified=False)
(ROOT/'results'/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
