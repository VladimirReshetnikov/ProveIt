"""Regenerate report tables from the saved raw benchmark measurements."""
from pathlib import Path
import json
ROOT = Path(__file__).resolve().parents[1]
D = json.loads((ROOT/'results/benchmarks.json').read_text())
NAMES = {'trefoil':'Trefoil', 'hard_unknot_8':'Hard unknot (8)', 'conway':'Conway',
         'kinoshita_terasaka':'Kinoshita--Terasaka', 'torus_3_5':r'$T(3,5)$',
         'unknot_braid40':'Unknot braid (40)', 'baseline_timeout36':'Recorded workload (36)',
         'unknot_chain_256':'Greedy order, 256', 'unknot_chain_1024':'Greedy order, 1,024',
         'torus_2_501':'Descending, 501'}


def seconds(x):
    return 'timeout' if x is None else f'{x:.6f}'


def table(rows, header, spec):
    return '\\begin{center}\n\\small\n\\begin{tabular}{'+spec+'}\n\\toprule\n'+header+' \\\\\n\\midrule\n'+'\n'.join(' & '.join(row)+r' \\' for row in rows)+'\n\\bottomrule\n\\end{tabular}\n\\end{center}\n'

for mode in ('pipeline','scan','rank','preprocess'):
    rows=[]
    for c in D['cases']:
        if c['mode'] != mode and not (mode=='preprocess' and c['mode'] in ('order','descending')):
            continue
        b=c['baseline']['median_seconds']; a=c['accelerated']['median_seconds']
        if mode=='rank':
            name = (r'$C^{\# '+c['name'].split('_')[-1]+'}$' if c['name'].startswith('conway')
                    else r'$3_1^{\# 10}$')
            rank = (r'$33^{'+c['name'].split('_')[-1]+'}$' if c['name'].startswith('conway')
                    else r'$3^{10}$')
            peak = c['accelerated']['trials'][0]['result']['stats']['max_objects_before_elimination']
            rows.append([name, str(c['crossings']), '5 s cap',seconds(a),rank,str(peak)])
        elif mode=='scan':
            rank=c['accelerated']['trials'][0]['result']['reduced_rank']
            rows.append([NAMES[c['name']],str(c['crossings']),seconds(b),seconds(a),str(rank)])
        else:
            ratio = '--' if b is None or a is None else f'{b/a:.2f}'
            rows.append([NAMES[c['name']],str(c['crossings']),seconds(b),seconds(a),ratio])
    if mode=='rank':
        text=table(rows,r'Diagram & $n$ & Baseline & New (s) & Reduced rank & Peak objects','lrlrrr')
    elif mode=='scan':
        text=table(rows,r'Diagram & $n$ & Baseline (s) & New (s) & Reduced rank','lrrrr')
    else:
        text=table(rows,r'Workload & $n$ & Baseline (s) & New (s) & Ratio','lrrrr')
    (ROOT/'paper'/f'table_{mode}.tex').write_text(text)
print('Wrote four tables from',len(D['cases']),'benchmark cases.')
