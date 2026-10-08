#!/usr/bin/env python3
"""Generate article tables and publication figures from the archived raw JSON.

Uses Matplotlib only for the figures. All reported times are the archived
measurements; this script performs no scanner timing or numerical smoothing.
"""
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent / 'paper'
FIGURES = PAPER / 'figures'
TABLES = PAPER / 'tables'
BACKENDS = ['standard', 'component', 'fitting_exact', 'fitting_decision', 'fitting_decision_dp']
LABELS = {
    'hard_unknot_8': r'$U_8$', 'conway': r'$C$',
    'kinoshita_terasaka': r'$KT$', 'conway_sum_2': r'$C^{\#2}$',
    'conway_sum_3': r'$C^{\#3}$', 'conway_sum_8': r'$C^{\#8}$',
    'stress_braid5_36': r'$B_{5,36}$', 'torus_3_11': r'$T(3,11)$',
    'torus_4_9': r'$T(4,9)$', 'torus_5_8': r'$T(5,8)$',
}
PLOT_LABELS = {
    'conway': 'Conway', 'kinoshita_terasaka': 'Kinoshita–Terasaka',
    'conway_sum_2': 'Conway sum × 2', 'conway_sum_3': 'Conway sum × 3',
    'conway_sum_8': 'Conway sum × 8', 'stress_braid5_36': '5-strand stress braid',
    'torus_4_9': 'Torus (4, 9)',
}


def label(name):
    if name in LABELS:
        return LABELS[name]
    return r'$R_{' + name.split('_')[1] + r'}$'


def write_tables(data):
    TABLES.mkdir(exist_ok=True)
    rows = [r'\begin{longtable}{@{}lrrrrrr@{}}',
        r'\caption{Median raw scanner time in milliseconds. $S$: standard; $C_s$: preceding component sharing; $F$: exact Fitting; $F_3$: capped decision Fitting. DP preprocessing is included in the last column. $\mathrm{lim}$ denotes three resource-limited calls.}\label{tab:all-timings}\\',
        r'\toprule Case & $n$ & $S$ & $C_s$ & $F$ & $F_3$ & $F_3+\mathrm{DP}$\\\midrule',
        r'\endfirsthead',
        r'\toprule Case & $n$ & $S$ & $C_s$ & $F$ & $F_3$ & $F_3+\mathrm{DP}$\\\midrule',
        r'\endhead', r'\bottomrule\endfoot']
    for case in data['cases']:
        values = []
        for backend in BACKENDS:
            summary = case['summary'][backend]
            values.append(f"{1000*summary['median_seconds']:.2f}" if summary['completed'] else r'$\mathrm{lim}$')
        rows.append(' & '.join([label(case['name']), str(case['crossings']), *values]) + r'\\')
    rows.append(r'\end{longtable}')
    (TABLES/'timings.tex').write_text('\n'.join(rows)+'\n')

    cases = {case['name']:case for case in data['cases']}
    names = ['conway', 'kinoshita_terasaka', 'conway_sum_2', 'conway_sum_3',
             'conway_sum_8', 'stress_braid5_36', 'torus_4_9', 'random_24']
    summary_data = json.loads((HERE/'summary.json').read_text())
    summaries = {row['name']:row for row in summary_data}
    rows = [r'\begin{tabular}{@{}lrrrrrrr@{}}',r'\toprule',
        r'& \multicolumn{2}{c}{Entries} & \multicolumn{2}{c}{Compositions} & \multicolumn{2}{c}{Largest component} & Splits\\',
        r'Case & $C_s$ & $F$ & $C_s$ & $F$ & $C_s$ & $F$ & $F$\\\midrule']
    for name in names:
        row=summaries[name]
        values=[row[key] for key in ['component_entries','fitting_entries',
                'component_compositions','fitting_compositions','old_largest','new_largest','fitting_splits']]
        rows.append(' & '.join([label(name),*[str(value) for value in values]])+r'\\')
    rows.extend([r'\bottomrule',r'\end{tabular}'])
    (TABLES/'operations.tex').write_text('\n'.join(rows)+'\n')

    rows=[r'\begin{tabular}{@{}lrrrr@{}}',r'\toprule',
          r'Case & Initial mass & Final mass & DP time (ms) & Full time (ms)\\\midrule']
    for case in data['cases']:
        summary=case['summary']['fitting_decision_dp']
        dp=summary['dp']
        if dp['initial_score'] != dp['score']:
            values=[label(case['name']),str(dp['initial_score'][1]),str(dp['score'][1]),
                    f"{1000*dp['seconds']:.2f}",f"{1000*summary['median_seconds']:.2f}"]
            rows.append(' & '.join(values)+r'\\')
    rows.extend([r'\bottomrule',r'\end{tabular}'])
    (TABLES/'ordering.tex').write_text('\n'.join(rows)+'\n')


def figures(data):
    FIGURES.mkdir(exist_ok=True)
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,'axes.titlesize':10,
        'axes.labelsize':9,'xtick.labelsize':8,'ytick.labelsize':8,
        'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42,
        'axes.edgecolor':'#7c8690','text.color':'#15324f','axes.labelcolor':'#15324f'})
    cases={case['name']:case for case in data['cases']}
    summaries={row['name']:row for row in json.loads((HERE/'summary.json').read_text())}
    names=list(PLOT_LABELS)
    fig, axes=plt.subplots(1,2,figsize=(6.5,3.8),gridspec_kw={'width_ratios':[1.35,1]})
    for i,name in enumerate(names):
        row=summaries[name]
        axes[0].barh(i-.15,row['fitting_entries']/row['component_entries'],height=.26,
                     color='#14666b',label='Differential entries' if i==0 else None)
        axes[0].barh(i+.15,row['fitting_compositions']/row['component_compositions'],height=.26,
                     color='#b56a36',label='Compositions' if i==0 else None)
        runs={(run['backend'],run['repetition']):run for run in cases[name]['runs']}
        for repetition in range(data['configuration']['repeats']):
            ratio=runs[('fitting_exact',repetition)]['seconds']/runs[('component',repetition)]['seconds']
            axes[1].plot(ratio,i+(repetition-1)*.14,'o',color='#15324f',markersize=4,alpha=.75)
    axes[0].set_yticks(range(len(names)),[PLOT_LABELS[name] for name in names])
    axes[1].set_yticks(range(len(names)),[])
    for ax in axes:
        ax.invert_yaxis()
        ax.axvline(1,color='#8c959d',linestyle='--',linewidth=1,zorder=0)
        ax.grid(axis='x',alpha=.14)
        ax.set_axisbelow(True)
        ax.set_xlabel('Fitting / component sharing')
    axes[0].set_xlim(0,1.13)
    axes[0].set_title('Deterministic operation counts',loc='left',pad=12)
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc='lower center', bbox_to_anchor=(.5,.008),
               ncol=2, frameon=False, fontsize=8)
    axes[1].set_xscale('log',base=2)
    axes[1].set_xlim(.5,4)
    axes[1].set_xticks([.5,1,2,4],['0.5','1','2','4'])
    axes[1].set_title('Three paired time samples',loc='left',pad=12)
    fig.subplots_adjust(left=.26,right=.985,top=.87,bottom=.24,wspace=.16)
    fig.savefig(FIGURES/'operations_and_time.pdf')
    fig.savefig(FIGURES/'operations_and_time.png',dpi=180)
    plt.close(fig)

    fig,axes=plt.subplots(1,2,figsize=(6.5,3.2))
    pure=[row for row in data['synthetic'] if row['kind']=='pure' and not row['decision']]
    decision=[row for row in data['synthetic'] if row['kind']=='pure' and row['decision']]
    mixed=[row for row in data['synthetic'] if row['kind']=='mixed']
    x=[row['copies'] for row in pure]
    axes[0].plot(x,[row['before_objects'] for row in pure],'o-',color='#7a8590',label='Input')
    axes[0].plot(x,[row['after_objects'] for row in pure],'s-',color='#14666b',label='Exact intervals')
    axes[0].plot(x,[row['after_objects'] for row in decision],'^-',color='#b56a36',label='Decision intervals')
    axes[0].set_title('Eight-layer common-nilpotent quivers',loc='left')
    x2=[row['copies'] for row in mixed]
    axes[1].plot(x2,[row['before_objects'] for row in mixed],'o-',color='#7a8590',label='Input')
    axes[1].plot(x2,[row['after_objects'] for row in mixed],'s-',color='#14666b',label='Exact Fitting + sharing')
    axes[1].set_title('Mixed-matching constructed quivers',loc='left')
    for ax, ticks in zip(axes,[x,x2]):
        ax.set_xscale('log',base=2)
        ax.set_yscale('log',base=2)
        ax.set_xticks(ticks,[str(value) for value in ticks])
        ax.set_xlabel('Multiplicity before basis mixing')
        ax.set_ylabel('Physical objects')
        ax.yaxis.set_major_formatter(ScalarFormatter())
        ax.grid(alpha=.18)
        ax.legend(frameon=False,fontsize=7,loc='upper left')
    axes[0].set_ylim(1.4,1800)
    axes[1].set_ylim(2,95)
    fig.tight_layout(w_pad=2)
    fig.savefig(FIGURES/'synthetic_compression.pdf')
    fig.savefig(FIGURES/'synthetic_compression.png',dpi=180)
    plt.close(fig)


def main():
    data=json.loads((HERE/'paired_results.json').read_text())
    write_tables(data)
    figures(data)
    print('Generated three TeX tables and two PDF/PNG figures from paired_results.json.')


if __name__=='__main__':
    main()
