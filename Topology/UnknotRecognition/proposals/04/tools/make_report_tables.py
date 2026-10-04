"""Regenerate the LaTeX benchmark tables from the recorded JSON data."""
from __future__ import annotations
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'report/tables'
OUT.mkdir(parents=True,exist_ok=True)
DATA=json.loads((ROOT/'benchmarks/comparison.json').read_text())
GROUPS={(g['implementation'],g['operation'],g['input']):g for g in DATA['groups']}
NAMES={'conway.json':'Conway (11 crossings)',
       'kinoshita_terasaka.json':'Kinoshita--Terasaka (11)',
       'hard_unknot_8.json':'Hard unknot (8)',
       'trefoil.json':'Trefoil (3)', 'figure_eight.json':'Figure-eight (4)',
       'torus_3_5.json':'Torus $T(3,5)$ (10)',
       'grid_scrambled_unknot.json':'Grid-scrambled unknot',
       'unknot_braid40.json':'Unknot braid (40)',
       'four_braid_41.json':'Four-strand braid (41)',
       'five_braid_36.json':'Five-strand braid (36)',
       'conway_sum2.json':'Conway $\\#2$ (22)',
       'conway_sum3.json':'Conway $\\#3$ (33)'}

def number(g,scale):
    if not g['successful']:return '$>{:,.0f}$'.format(g['censoring_seconds']*scale)
    value=g['median_seconds']*scale
    return f'{value:,.3f}'

def ratio(b,f):
    value=(b['median_seconds'] if b['successful'] else b['censoring_seconds'])/f['median_seconds']
    return ('$' + ('>' if not b['successful'] else '') + f'{value:,.2f}' + r'\times$')

def write_table(path,head,rows,alignment):
    text=[r'\begin{tabular}{'+alignment+'}',r'\toprule',head+r' \\',r'\midrule']
    text += [r' & '.join(row)+r' \\' for row in rows]
    text += [r'\bottomrule',r'\end{tabular}']
    (OUT/path).write_text('\n'.join(text)+'\n')

for operation,filename,scale,unit in [('recognize','recognition.tex',1000,'ms'),
                                     ('scan','scan.tex',1,'s')]:
    rows=[]
    for name,label in NAMES.items():
        key=('baseline',operation,name)
        if key not in GROUPS:continue
        b,f=GROUPS[key],GROUPS['fast',operation,name]
        rows.append([label,number(b,scale),number(f,scale),ratio(b,f)])
    write_table(filename,'Input & Baseline ('+unit+') & Improved ('+unit+') & Ratio',rows,'lrrr')
rows=[]
for knot,powers in [('conway',[2,3,8,16]),('trefoil',[8,16])]:
    for k in powers:
        g=GROUPS['fast','factored',f'{knot}_sum{k}.json'];r=g['samples'][0]['result']
        rows.append([f'{knot.title()} $\\#{k}$',str(g['samples'][0]['crossings']),
                     f'${33 if knot=="conway" else 3}^{{{k}}}$',number(g,1000),
                     str(max(f['stats']['max_objects_before_elimination'] for f in r['factors']))])
write_table('factored.tex','Input & Crossings & Reduced rank & Time (ms) & Peak factor objects',rows,'lrrrr')
rows=[]
for n in (128,256,512,1024):
    b=GROUPS['baseline','order',f'unknot_chain{n}.json'];f=GROUPS['fast','order',f'unknot_chain{n}.json']
    rows.append([str(n),number(b,1000),number(f,1000),ratio(b,f)])
write_table('order.tex','$n$ & Baseline (ms) & Heap order (ms) & Ratio',rows,'rrrr')
ab=json.loads((ROOT/'benchmarks/ablation.json').read_text())['groups']
a={(g['input'],g['strategy']):g for g in ab};rows=[]
for name in ('conway.json','kinoshita_terasaka.json','five_braid_36.json'):
    s,f=a[name,'stack'],a[name,'minfill']
    t=lambda g: (f"{g['median_seconds']:.6f}" if 'median_seconds' in g else '$>10$')
    rows.append([NAMES[name],t(s),t(f)])
write_table('ablation.tex','Input & Cached algebra, stack (s) & Cached algebra, heap (s)',rows,'lrr')
print('Wrote',len(list(OUT.glob('*.tex'))),'tables to',OUT)
