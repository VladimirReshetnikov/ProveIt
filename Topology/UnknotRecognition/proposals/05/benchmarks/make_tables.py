"""Generate the report's LaTeX tables from the saved benchmark, not hand-entered data."""
from __future__ import annotations
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
record = json.loads((ROOT/'results/benchmark.json').read_text())
rows = {(x['name'], x['engine']): x for x in record['summary']}
labels = {
    'unknot': 'Crossing-free unknot', 'trefoil': 'Trefoil', 'figure_eight': 'Figure-eight',
    'hard_unknot_8': 'Hard unknot (8 crossings)', 'conway': 'Conway',
    'kinoshita_terasaka': 'Kinoshita--Terasaka', 'torus_3_5': '$T(3,5)$',
    'unknot_braid40': 'Unknot braid (40 crossings)',
    'grid_determinant_one_knot': 'Determinant-one grid knot',
    'grid_scrambled_unknot': 'Scrambled grid unknot',
    'conway_sum_2': 'Conway $\\#\\,$ Conway',
    'conway_sum_3': 'Three Conway summands',
    'conway_sum_4': 'Four Conway summands',
    'raw_random5_36': 'Random 5-braid (36 crossings)',
    'raw_unknot_chain_256': 'Unknot chain (256 crossings)',
    'raw_unknot_chain_1024': 'Unknot chain (1024 crossings)',
    'ordering_chain_256': 'Order only: 256-crossing chain',
    'ordering_chain_1024': 'Order only: 1024-crossing chain',
    'forced_hard_unknot_8': 'No R1/R2/descending: hard unknot',
}
for name in list(labels):
    labels.setdefault('raw_'+name, labels[name])

def table(names, caption, label):
    out = [r'\begin{table}[htbp]\centering\small', r'\begin{tabular}{@{}lrrrr@{}}',
           r'\toprule Case & $n$ & Original (ms) & New (ms) & Ratio \\', r'\midrule']
    for name in names:
        b, o = rows[name,'baseline'], rows[name,'optimized']
        bt, ot = b['median_completed_seconds'], o['median_completed_seconds']
        btext = f'{1000*bt:.3f}' if bt is not None else r'\textsc{limit}'
        otext = f'{1000*ot:.3f}' if ot is not None else r'\textsc{limit}'
        ratio = f'{bt/ot:.2f}' if bt is not None and ot is not None else '--'
        out.append(f"{labels.get(name,name)} & {b['crossings']} & {btext} & {otext} & {ratio} \\")
        # Add the second TeX slash (kept separate to avoid escaping ambiguity).
        out[-1] += '\\'
    out += [r'\bottomrule\end{tabular}', r'\caption{'+caption+r'}\label{'+label+r'}',
            r'\end{table}']
    return '\n'.join(out)
recognition = [x['name'] for x in record['cases'] if x['kind']=='recognize'
               and not x['name'].startswith('forced_')]
raw = [x['name'] for x in record['cases'] if x['kind']=='rank']
aux = [x['name'] for x in record['cases'] if x['kind']=='ordering' or x['name'].startswith('forced_')]
text = table(recognition, 'Full recognition, defaults in both versions. Ratio is original/new; '
             'values below one are regressions. Each time is the median of three completed '
             'cold-process calls. Limit means all three calls returned UNKNOWN.', 'tab:recognition')
text += '\n\n'+table(raw, 'Raw Khovanov backend, without recognition preprocessing or invariant '
                      'filters. Both engines use the same deterministic scan-order policy.', 'tab:raw')
text += '\n\n'+table(aux, 'Planning and forced-fallback diagnostics. In the last row only '
                      'Reidemeister reduction and descending recognition are disabled; invariant '
                      'filters are still enabled.', 'tab:aux')
(ROOT/'docs/benchmark_tables.tex').write_text(text+'\n')
