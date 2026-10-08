#!/usr/bin/env python3
"""Plot recorded results; no fitted curves or inferred absent runtimes."""
import argparse
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--results', type=Path, required=True)
    ap.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1]/'figures')
    a = ap.parse_args()
    a.output.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,'svg.fonttype':'none'})
    rows=[]
    for name in ('streaming_response.json','streaming_response_large.json'):
        rows += json.loads((a.results/name).read_text())['cases']
    rows=sorted((r for r in rows if r['order_kind']=='natural'),key=lambda r:r['crossings'])
    fig,ax=plt.subplots(figsize=(7.2,4),constrained_layout=True)
    n=[r['crossings'] for r in rows]
    for key,col,label in [('dense_a','#b66b35','Independent dense setup'),('stream','#17677b','Reverse-suffix streaming')]:
        ax.plot(n,[1000*r['medians'][key] for r in rows],'o-',color=col,linewidth=1.7,label=label)
    ax.set_xscale('log',base=2)
    ax.set_yscale('log')
    ax.set_xticks(n,labels=[str(x) for x in n])
    ax.set_yticks([0.1,1,10,100,1000,10000])
    ax.yaxis.set_major_formatter(ScalarFormatter())
    ax.set_ylim(.3,7000)
    ax.set_xlabel('Crossings in the supplied torus-braid diagram')
    ax.set_ylabel('All-suffix setup median (milliseconds)')
    ax.set_title('Response compilation only; maximum frontier = 6',loc='left',fontsize=11,fontweight='bold',pad=12)
    ax.grid(axis='y',which='major',color='#d9dfe3',linewidth=.6)
    ax.legend(loc='upper left',frameon=False)
    for ext in ('png','svg'):fig.savefig(a.output/f'response_setup.{ext}',dpi=240)
    plt.close(fig)
    rows=json.loads((a.results/'first_jet_benchmark.json').read_text())['rows']
    rows.sort(key=lambda r:r['median_standard_over_arm']['jet'])
    names={'trefoil':'Trefoil','conway':'Conway','kinoshita_terasaka':'Kinoshita–Terasaka','hard_unknot_8':'Hard unknot (8 crossings)',
           'grid_scrambled_unknot':'Scrambled grid unknot','stress_braid5_36':'Five-strand stress braid','conway_sum_2':'Conway connected sum',
           'coxeter_11':'Coxeter unknot (11 crossings)','coxeter_35':'Coxeter unknot (35 crossings)',
           'trefoil_cancel_pairs_8':'Trefoil + 8 cancelling pairs','trefoil_cancel_pairs_24':'Trefoil + 24 cancelling pairs','torus_3_5':'T(3,5)'}
    fig,ax=plt.subplots(figsize=(7.2,4.6),constrained_layout=True)
    for i,r in enumerate(rows):
        v=r['median_standard_over_arm']['jet'];col='#17677b' if v>1 else '#b66b35'
        ax.plot([1,v],[i,i],color=col,linewidth=2)
        ax.plot(v,i,'o',color=col,markersize=5)
        ax.annotate(f'{v:.3f}',(v,i),xytext=(5 if v>1 else -5,0),textcoords='offset points',
                    ha='left' if v>1 else 'right',va='center',fontsize=8)
    ax.axvline(1,color='#596872',linewidth=1,linestyle='--')
    ax.set_yticks(range(len(rows)),labels=[names[r['name']] for r in rows])
    ax.tick_params(axis='y',length=0)
    ax.set_xscale('log');ax.set_xlim(.14,5)
    ax.set_xticks([.2,.5,1,2,4],labels=['0.2','0.5','1','2','4'])
    ax.set_xlabel('Median paired standard time / first-jet time (larger is faster)')
    ax.set_title('Raw scanner: paired first-jet ratios\nExisting front-end filters bypassed',loc='left',fontsize=11,fontweight='bold',pad=12)
    ax.grid(axis='x',color='#e3e7ea',linewidth=.6);ax.set_axisbelow(True)
    for ext in ('png','svg'):fig.savefig(a.output/f'first_jet_ratios.{ext}',dpi=240)
    plt.close(fig)

if __name__=='__main__':main()
