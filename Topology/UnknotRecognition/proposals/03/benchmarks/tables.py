"""Regenerate report/measurements.tex from recorded cold-process JSON trials."""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def name_label(name):
    labels={'conway':'Conway','kinoshita_terasaka':'Kinoshita--Terasaka',
        'hard_unknot_8':'Hard unknot (8)', 'figure_eight':'Figure-eight',
        'trefoil':'Trefoil','unknot':'Crossing-free unknot',
        'unknot_braid40':'Unknot braid (40)',
        'grid_determinant_one_knot':'Determinant-one grid',
        'grid_scrambled_unknot':'Scrambled unknot grid',
        'torus_3_5':'$T(3,5)$',
        'random_braid5_36':'Five-braid (36)',
        'random_braid5_36_reduced':'Same knot, reduced (24)',
        'conway_sum_3':'Three Conway summands'}
    if name in labels:return labels[name]
    if name.startswith('random_'):
        _,s,n=name.split('_');return f'Random {s.replace("-braid", "-braid")} ({n})'
    if name.startswith('unknot_chain_'):return f'Unknot chain ({name.split("_")[-1]})'
    if name.startswith('torus_'):
        _,a,b=name.split('_');return f'$T({a},{b})$'
    return name.replace('_',r'\_')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',default='results/benchmarks.json')
    args=parser.parse_args()
    data=json.loads((ROOT/args.input).read_text())
    index={(r['phase'],r['name'],r['backend']):r for r in data['summary']}
    trials=data['trials']
    def row(p,n,b):return index.get((p,n,b))
    def seconds(p,n,b):return row(p,n,b)['median_seconds']
    def budget(p,n,b):
        return next(x['budget'] for x in trials if (x['phase'],x['case']['name'],x['backend'])==(p,n,b))
    def time_text(p,n,b,scale=1):
        r=row(p,n,b)
        if not r:return '---'
        if r['median_seconds'] is None:return f'$>{budget(p,n,b)*scale:g}$'
        value=r['median_seconds']*scale
        return f'{value:.3f}' if value<10 else f'{value:.2f}'
    def speed(p,n):
        a,b=row(p,n,'original'),row(p,n,'optimized')
        if not a or not b:return '---'
        if a['median_seconds'] is None:
            lower = math.floor(10 * budget(p,n,"original") / b["median_seconds"]) / 10
            return f'$>{lower:.1f}$'
        return f'{a["median_seconds"]/b["median_seconds"]:.2f}'
    def n_crossings(p,n):
        return next(x['crossings'] for x in trials if x['phase']==p and x['case']['name']==n and 'crossings' in x)
    out=['% Generated from '+args.input+' by benchmarks/tables.py.']
    macros={'TrialCount':len(trials),'HardNewSeconds':f'{seconds("raw","random_5-braid_36","optimized"):.3f}',
        'HardLowerSpeedup':math.floor(budget('raw','random_5-braid_36','original')/seconds('raw','random_5-braid_36','optimized')),
        'HardReferenceSeconds':f'{seconds("raw","random_5-braid_36","original-markowitz"):.2f}',
        'ConwayRecognitionSpeedup':f'{seconds("pipeline","conway","original")/seconds("pipeline","conway","optimized"):.1f}',
        'KTRecognitionSpeedup':f'{seconds("pipeline","kinoshita_terasaka","original")/seconds("pipeline","kinoshita_terasaka","optimized"):.1f}',
        'ConwayThreeMilliseconds':f'{seconds("pipeline","conway_sum_3","optimized")*1000:.2f}',
        'ConwayThreeLowerSpeedup':math.floor(10/seconds('pipeline','conway_sum_3','optimized')),
        'ConwayFiftySeconds':f'{seconds("factor","conway_sum_50","optimized"):.3f}'}
    for k,v in macros.items():out.append("\\newcommand{\\"+k+'}{'+str(v)+'}')
    def table_begin(command,columns,header):
        out.extend(["\\newcommand{\\"+command+r'}{',r'\begingroup\small',
            r'\begin{longtable}{@{}'+columns+r'@{}}',r'\toprule',header+r'\\',r'\midrule\endhead'])
    def table_end():out.extend([r'\bottomrule\end{longtable}',r'\endgroup}'])
    names=[r['name'] for r in data['summary'] if r['phase']=='raw' and r['backend']=='optimized']
    table_begin('RawBenchmarkTable','lrrrrr',r'Diagram & $n$ & $r_2$ & Original (s) & New (s) & Ratio')
    for n in names:
        out.append(' & '.join([name_label(n),str(n_crossings('raw',n)),str(row('raw',n,'optimized')['rank']),
             time_text('raw',n,'original'),time_text('raw',n,'optimized'),speed('raw',n)])+r'\\')
    table_end()
    names=[r['name'] for r in data['summary'] if r['phase']=='pipeline' and r['backend']=='optimized']
    methods={'jones-mod-prime':'Jones mod $p$','alexander-mod-prime':'Alexander mod $p$',
             'reduced-khovanov-F2-scan':'Khovanov','reidemeister-reduction':'R1/R2',
             'descending-diagram':'Descending','alexander-polynomial':'Alexander'}
    table_begin('PipelineBenchmarkTable','lrrrl',r'Diagram & Original (ms) & New (ms) & Ratio & New terminal stage')
    for n in names:
        out.append(' & '.join([name_label(n),time_text('pipeline',n,'original',1000),
            time_text('pipeline',n,'optimized',1000),speed('pipeline',n),
            methods[row('pipeline',n,'optimized')['method']]])+r'\\')
    table_end()
    names=[r['name'] for r in data['summary'] if r['phase']=='factor' and r['backend']=='optimized']
    table_begin('FactorBenchmarkTable','lrrrrr',r'Family & $n$ & Reduced rank & Original (ms) & New (ms) & Ratio')
    for n in names:
        block,_,k=n.split('_');base=3 if block=='trefoil' else 33
        out.append(' & '.join([f'{k} {block} summands',str(n_crossings('factor',n)),f'${base}^{{{k}}}$',
            time_text('factor',n,'original',1000),time_text('factor',n,'optimized',1000),speed('factor',n)])+r'\\')
    table_end()
    table_begin('AblationBenchmarkTable','lrr',r'36-crossing raw backend & Seconds & Reduced rank')
    for b,label in [('original','Original algebra, original LIFO'),('optimized-lifo','Compiled algebra, LIFO'),
                    ('original-markowitz','Original algebra, new scheduler'),('optimized','Compiled algebra, new scheduler')]:
        out.append(f'{label} & {time_text("raw","random_5-braid_36",b)} & '+
                   (str(row('raw','random_5-braid_36',b)['rank']) if row('raw','random_5-braid_36',b)['rank'] else '---')+r'\\')
    table_end()
    table_begin('OrderingBenchmarkTable','rrrr',r'Crossings & Original (ms) & New (ms) & Ratio')
    for n in ('order_chain_128','order_chain_256','order_chain_512'):
        out.append(' & '.join([n.split('_')[-1],time_text('ordering',n,'original',1000),
            time_text('ordering',n,'optimized',1000),speed('ordering',n)])+r'\\')
    table_end()
    (ROOT/'report/measurements.tex').write_text('\n'.join(out)+'\n')
    print(json.dumps(macros,indent=2))

if __name__=='__main__':main()
