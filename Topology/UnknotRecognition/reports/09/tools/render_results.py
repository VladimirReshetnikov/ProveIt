#!/usr/bin/env python3
"""Regenerate article tables and vector plots from retained measurements.

The original factorization experiment remains authoritative for that code.
If a final-audit rerun is present, its sparse and pipeline rows supersede
the initial rows in the displayed tables.  No measurement is edited.
Requires matplotlib only for figures; --tables-only uses the standard library.
"""
from __future__ import annotations
import argparse
import csv
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
NAMES = {
    'conway':'Conway', 'kinoshita_terasaka':'Kinoshita--Terasaka',
    'hard_unknot_8':'Hard unknot (8)', 'unknot_braid40':'Unknot braid (40)',
    'stress_braid5_36':'Stress closure (36)', 'T3_11':r'$T(3,11)$',
    'survivor_0':'Survivor 0', 'survivor_1':'Survivor 1', 'survivor_2':'Survivor 2',
    'cyclic_trefoils_128':'128 trefoils', 'cyclic_trefoils_256':'256 trefoils',
    'torus_3_521':r'$T(3,521)$',
}


def load_results():
    original = json.loads((ROOT/'data/paired_benchmarks.json').read_text())
    rows = {row['name']:dict(row, source_file='paired_benchmarks.json')
            for row in original['results']}
    rerun = ROOT/'data/paired_benchmarks_final.json'
    if rerun.exists():
        for row in json.loads(rerun.read_text())['results']:
            rows[row['name']] = dict(row, source_file=rerun.name)
    pointed_path = ROOT/'data/reduced_benchmark_final.json'
    if not pointed_path.exists(): pointed_path = ROOT/'data/reduced_benchmark.json'
    pointed = [dict(row,source_file=pointed_path.name)
               for row in json.loads(pointed_path.read_text())['results']]
    return list(rows.values()), pointed


def fmt(x):
    return f'{x:.5f}' if x < 0.01 else f'{x:.4f}' if x < 0.1 else f'{x:.3f}'


def table(name, align, header, rows):
    text = '\\begin{tabular}{'+align+'}\n\\toprule\n'
    text += ' & '.join(header)+r' \\'+'\n\\midrule\n'
    text += '\n'.join(' & '.join(map(str,row))+r' \\' for row in rows)
    text += '\n\\bottomrule\n\\end{tabular}\n'
    (ROOT/'article/tables'/name).write_text(text)


def generate_tables(results, pointed):
    for kind in ['factorization','alexander','pipeline']:
        rows=[]
        for r in results:
            if r['kind'] != kind: continue
            if kind=='factorization': label=str(r['summands'])
            elif kind=='alexander': label=r'$T(3,'+r['name'].split('_')[-1]+')$'
            else: label=NAMES[r['name'].removeprefix('recognize_')]
            interval='['+fmt(r['ratio_interval'][0])+', '+fmt(r['ratio_interval'][1])+']'
            rows.append([label, r['crossings'],f"{r['baseline_seconds_median']*1000:.3f}",
                         f"{r['improved_seconds_median']*1000:.3f}",fmt(r['ratio_median']),interval])
        table(kind+'.tex','lrrrrl',
              ['Summands' if kind=='factorization' else 'Diagram','$n$',
               'Baseline ms','Updated ms','Ratio',r'96.1\% interval'],rows)
    table('pointed.tex','lrrrl',
          ['Diagram','$n$','Baseline ms','Pointed ms',r'Ratio [95\% bootstrap interval]'],
          [[NAMES[r['case']],r['crossings'],f"{1000*r['baseline_seconds_median']:.3f}",
            f"{1000*r['reduced_seconds_median']:.3f}",fmt(r['ratio_median'])+' ['+
            ', '.join(fmt(t) for t in r['ratio_ci95_bootstrap_median'])+']'] for r in pointed])
    table('pointed_work.tex','lrrrr',
          ['Diagram','Compositions A','Compositions B','Peak objects A','Peak objects B'],
          [[NAMES[r['case']],r['baseline_stats']['compositions'],r['reduced_stats']['compositions'],
            r['baseline_stats']['max_objects_before_elimination'],
            r['reduced_stats']['max_objects_before_elimination']]
           for r in pointed if r['case'] in ('conway','hard_unknot_8','stress_braid5_36','T3_11')])
    table('sparse_work.tex','rrrrrr',
          ['$n$','$E$ (per minor)','$F_{-1}$','$F_t$',r'$Z_{\max,-1}$',r'$Z_{\max,t}$'],
          [[r['crossings'],r['sparse_counters'][0]['input_entries'],
            r['sparse_counters'][0]['schur_updates'],r['sparse_counters'][1]['schur_updates'],
            r['sparse_counters'][0]['peak_nonzeros'],r['sparse_counters'][1]['peak_nonzeros']]
           for r in results if r['kind']=='alexander'])
    with (ROOT/'data/benchmark_summary.csv').open('w',newline='') as handle:
        fields=['case','kind','crossings','baseline_seconds','updated_seconds','ratio',
                'interval_low','interval_high','interval_method','source_file']
        writer=csv.DictWriter(handle,fieldnames=fields);writer.writeheader()
        for r in results:
            writer.writerow(dict(zip(fields,[r['name'],r['kind'],r['crossings'],
                r['baseline_seconds_median'],r['improved_seconds_median'],r['ratio_median'],
                *r['ratio_interval'],'median order statistic, nominal 96.1%',r['source_file']])))
        for r in pointed:
            writer.writerow(dict(zip(fields,[r['case'],'pointed',r['crossings'],
                r['baseline_seconds_median'],r['reduced_seconds_median'],r['ratio_median'],
                *r['ratio_ci95_bootstrap_median'],'median percentile bootstrap, nominal 95%',
                r['source_file']])))


def generate_figures(results, pointed):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.size':9,'axes.spines.top':False,'axes.spines.right':False,
                         'pdf.fonttype':42,'ps.fonttype':42,'axes.labelcolor':'#243847'})
    fig,axes=plt.subplots(1,2,figsize=(10.2,3.7),layout='constrained')
    for ax,kind,title in zip(axes,['factorization','alexander'],
                             ['Visible factorization','Alexander filter, forced sparse backend']):
        rows=[r for r in results if r['kind']==kind]
        x=[r['crossings'] for r in rows]
        ax.loglog(x,[r['baseline_seconds_median'] for r in rows],'o-',color='#52616D',label='Archived baseline')
        ax.loglog(x,[r['improved_seconds_median'] for r in rows],'s-',color='#087E8B',label='Updated')
        ax.set(title=title,xlabel='Diagram crossings',ylabel='Median seconds')
        ax.grid(True,which='major',alpha=.2);ax.legend(frameon=False,fontsize=8)
    fig.savefig(ROOT/'article/figures/scaling.pdf')
    fig.savefig(ROOT/'article/figures/scaling.png',dpi=220)
    plt.close(fig)
    fig,ax=plt.subplots(figsize=(8.9,4.1),layout='constrained')
    labels=[NAMES[r['case']].replace('--','–').replace('$','') for r in pointed]
    for i,r in enumerate(pointed):
        lo,hi=r['ratio_ci95_bootstrap_median'];med=r['ratio_median']
        color='#087E8B' if hi<1 else '#B56B31' if lo>1 else '#52616D'
        ax.errorbar(med,i,xerr=[[med-lo],[hi-med]],fmt='o',color=color,capsize=3)
    ax.axvline(1,color='#243847',lw=1,ls='--')
    ax.set_yticks(range(len(labels)),labels);ax.invert_yaxis()
    ax.set(xlabel='Pointed / ordinary scan time (paired median ratio)',
           title='Direct reduced scanning: mixed results on the fixed corpus')
    ax.grid(axis='x',alpha=.2)
    fig.savefig(ROOT/'article/figures/pointed_ratios.pdf')
    fig.savefig(ROOT/'article/figures/pointed_ratios.png',dpi=220)
    plt.close(fig)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tables-only',action='store_true')
    args=parser.parse_args()
    (ROOT/'article/tables').mkdir(parents=True,exist_ok=True)
    (ROOT/'article/figures').mkdir(parents=True,exist_ok=True)
    results,pointed=load_results();generate_tables(results,pointed)
    if not args.tables_only:generate_figures(results,pointed)
    print('Generated tables, CSV'+('' if args.tables_only else ', and figures')+'.')


if __name__=='__main__':main()
