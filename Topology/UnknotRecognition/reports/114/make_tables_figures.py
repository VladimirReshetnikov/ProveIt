#!/usr/bin/env python3
"""Render the article's tables and scientific figure from frozen JSON data."""

from pathlib import Path
import json
import math

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


ROOT = Path(__file__).resolve().parent
ARTICLE, RESULTS, FIGURES = ROOT/'article', ROOT/'results', ROOT/'figures'
FIGURES.mkdir(exist_ok=True)
native = json.loads((RESULTS/'native_replay.json').read_text())
explore = json.loads((RESULTS/'exploration_summary.json').read_text())
compression = json.loads((RESULTS/'compression.json').read_text())

native_lines = [r'''The extended report-57 scan contains 1,374 standard vertex surfaces,
excluding its Fibonacci and connected-sum records. The baseline completes
1,205 and refuses 169. The recorded baseline refusal reasons are 52 raw
cancellation stalls, 101 boundary-kernel stalls, five raw ball-cancellation
obstructions, and eleven annular attachments. Inspecting the refused cases
under the tested source, maximum-passage, and reverse-ID forests finds 52
with a complete augmented core and pending annuli. Exactly five of those
families pass the signed common-basis test. All five now pass the complete
source-authenticated wrapper with its production forest policy.

\begin{table}[ht]
\centering\small
\begin{tabular}{@{}lrrrrrr@{}}
\toprule
Case & $t$ & $W$ & Source letters & Word nodes & Moves & Regina cut $t$\\
\midrule''']
for r in native['records']:
    label = ('E' if r['source_record']=='finite_figureEight' else 'I') + str(r['source_standard_vertex_index'])
    s = r['signed_stats']
    native_lines.append(f"{label} & {r['tetrahedra']} & {r['normal_disks']} & {s['source_letters']} & {s['grammar_nodes']} & {s['nielsen_moves']} & {r['regina']['tetrahedra']}" + r"\\")
native_lines.append(r'''\bottomrule
\end{tabular}
\caption{Five new native gains. E denotes \texttt{finite\_figureEight}; I
denotes \texttt{finite\_figureEight\_interior}; numbers are the frozen
standard-vertex indices. Every result is two genus-two handlebodies, with
independent whole-cut replay and Regina 7.4 agreement.}
\label{tab:native}
\end{table}

E71 uses the ordinary signed schema. I134, I136, I205, and I290 first use
the established top 2--3 reduction and the second signed schema. The five
complete certificate files have canonical sizes 144,704; 199,262; 160,239;
198,738; and 198,726 bytes respectively. Most evidence is the existing
source geometry, rather than the short Nielsen move list.

In one recorded run, whole-cut production took between 0.053 and 0.105
seconds on these five cases, and full independent replay between 0.075 and
0.118 seconds. These are single-run observations on a shared execution
host, not an isolated timing comparison or a claimed multiplicative speed-up.
The baseline timings measure refusals; the new timings measure completed
certificates. Source encodings and exact operation counts are the more
reproducible performance evidence.

Two other exploratory banks produced no new opportunities: all 660 tested
Fibonacci vertex/scaled cuts and all 1,700 deterministic seed relabelings
were already completed by the baseline. The broader 1,374-case discovery
search took 562.07 seconds and included a separate literal Whitehead search
used to investigate refused states. That exploration time is not the cost
of the new compressed production algorithm.
''')
(ARTICLE/'native_results.tex').write_text('\n'.join(native_lines))

selection = [('fibonacci_pair',128),('fibonacci_pair',2048),
             ('binary_shear_pair',128),('binary_shear_pair',2048),
             ('triangular_transport',128),('triangular_transport',2048),
             ('independent_blocks',16),('independent_blocks',64)]
labels={'fibonacci_pair':'Fibonacci pair','binary_shear_pair':'Binary shear pair',
        'triangular_transport':'Triangular transport','independent_blocks':'Independent blocks'}
by_key={(r['family'],r['parameter']):r for r in compression['results']}
lines=[r'''\begin{table}[ht]
\centering\small
\begin{tabular}{@{}lrrrrrr@{}}
\toprule
Family & Parameter & $\bits(N)$ & Input DAG & Final DAG & Produce ms & Verify ms\\
\midrule''']
for key in selection:
    r=by_key[key]
    assert r['status']=='COMPLETE' and r['verified']
    lines.append(f"{labels[key[0]]} & {key[1]:,} & {r['expanded_length_bits']:,} & {r['source_reachable_nodes']:,} & {r['producer_nodes']:,} & {1000*r['producer_seconds_median']:.2f} & {1000*r['verifier_seconds_median']:.2f}" + r"\\")
lines.append(r'''\bottomrule
\end{tabular}
\caption{Selected compressed benchmarks; all positive results independently
verified. Parameters are depth $n$, exponent-bit parameter $b$, transport
depth $d$, and number of blocks, respectively. $N$ is total expanded root
length, with $\bits(N)=\lfloor\log_2N\rfloor+1$. No expanded words were
materialized. Full measurements and code hashes are in the JSON.}
\label{tab:compression}
\end{table}

\begin{figure}[ht]
\centering
\includegraphics[width=\textwidth]{../figures/compression.pdf}
\caption{Recorded grammar sizes and elapsed production time for three
compressed families. The horizontal parameter controls exponentially large
expanded words. Straight-line growth of stored grammar sizes on these
examples illustrates the proved sharing mechanism; the finite timing curves
do not establish an asymptotic exponent.}
\label{fig:compression}
\end{figure}
''')
(ARTICLE/'compression_results.tex').write_text('\n'.join(lines))

plt.rcParams.update({'font.family':'DejaVu Serif','font.size':9,
                     'axes.spines.top':False,'axes.spines.right':False,
                     'axes.labelcolor':'#23354b','text.color':'#23354b',
                     'xtick.color':'#45556b','ytick.color':'#45556b',
                     'savefig.facecolor':'white'})
fig,axes=plt.subplots(1,2,figsize=(7.6,3.5),layout='constrained')
colors=['#254f7b','#bc682b','#3f806a']
for kind,color in zip(('fibonacci_pair','binary_shear_pair','triangular_transport'),colors):
    rows=[r for r in compression['results'] if r['family']==kind and r['status']=='COMPLETE']
    x=[r['parameter'] for r in rows]
    axes[0].plot(x,[r['producer_nodes'] for r in rows],'-o',color=color,
                 markersize=3.2,linewidth=1.4,label=labels[kind])
    axes[1].plot(x,[1000*r['producer_seconds_median'] for r in rows],'-o',
                 color=color,markersize=3.2,linewidth=1.4,label=labels[kind])
    for r in rows:
        axes[1].scatter([r['parameter']]*len(r['producer_seconds_samples']),
                         [1000*t for t in r['producer_seconds_samples']],
                         s=8,alpha=.22,color=color,edgecolor='none')
for ax in axes:
    ax.set_xscale('log',base=2)
    ax.set_yscale('log',base=10)
    ax.set_xlabel('Depth or exponent-bit parameter')
    ax.grid(True,which='major',color='#dce2e9',linewidth=.55)
    ax.set_axisbelow(True)
axes[0].set_ylabel('Retained grammar productions')
axes[1].set_ylabel('Production time (milliseconds)')
axes[0].set_title('Structural growth',loc='left',fontweight='bold')
axes[1].set_title('Observed cost',loc='left',fontweight='bold')
axes[0].legend(loc='upper left',fontsize=7.5,frameon=False)
fig.savefig(FIGURES/'compression.pdf',bbox_inches='tight')
fig.savefig(FIGURES/'compression.png',dpi=180,bbox_inches='tight')
print('Generated native/compression tables and figures from frozen JSON.')
