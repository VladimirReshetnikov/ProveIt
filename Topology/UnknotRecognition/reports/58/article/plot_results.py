#!/usr/bin/env python3
"""Reproduce this article's figures, numeric section and CSV from its recorded data.

The selected numerical interpretation is specific to the published dataset.
A hash guard prevents silently combining new tables with that interpretation.
For new experiments, revise the narrative as well as replacing the input data.
"""
import argparse
import csv
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('benchmark', type=Path)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    raw = args.benchmark.read_bytes()
    if hashlib.sha256(raw).hexdigest() != 'ce289d47619bacb7cd25e5b1a00b3b527e57c30cde57069a0e1cf3eff9d959c1':
        parser.error('this report generator is pinned to the published benchmark; new data require a new interpretation')
    data = json.loads(raw)
    assert data['sources_unchanged']
    assert len(data['cases']) == 13 and data['rounds_per_case'] == 5
    root = args.output
    root.mkdir(parents=True, exist_ok=True)
    figures = root / 'figures'
    figures.mkdir(exist_ok=True)
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.ticker import ScalarFormatter
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9,
        'axes.spines.top': False, 'axes.spines.right': False,
        'axes.labelcolor': '#17324d', 'text.color': '#17324d',
        'axes.edgecolor': '#8496a5', 'grid.color': '#dbe3e9',
        'pdf.fonttype': 42, 'ps.fonttype': 42, 'savefig.facecolor': 'white'})
    arms = [('coordinates_reference', 'Coordinate reference', '#b26530', 's', '-'),
            ('direct', 'Two-weight direct', '#17324d', 'o', '-'),
            ('reduced', 'Two-weight core', '#087e82', '^', '--')]
    dimensions = [c for c in data['cases'] if c['source']['family'] == 'layered_meridian']
    multiples = [c for c in data['cases']
                 if c['source']['family'] == 'large_quadrilateral_content']
    others = [c for c in data['cases'] if c not in dimensions and c not in multiples]

    def val(case, arm, field='total_ns'):
        return case['summary'][arm]['median_' + field]

    def ratio(case, name):
        return case['summary'][name]['median_paired_total_ns_ratio']

    fig, ax = plt.subplots(figsize=(6.45, 3.6), layout='constrained')
    xs = [c['source']['tetrahedra'] for c in dimensions]
    for arm, label, color, marker, style in arms:
        ax.plot(xs, [val(c, arm) / 1e6 for c in dimensions], label=label,
                color=color, marker=marker, linestyle=style, linewidth=1.65, markersize=4.5)
    ax.set(xscale='log', yscale='log', xlabel='Tetrahedra t',
           ylabel='Median producer + replay time (ms)')
    ax.set_xticks(xs, [str(x) for x in xs])
    ax.grid(axis='y', which='major', linewidth=0.65)
    ax.legend(frameon=False, loc='upper left')
    for extension in ('pdf', 'png'):
        fig.savefig(figures / ('dimension_timing.' + extension), dpi=220)
    plt.close(fig)

    fig, axes = plt.subplots(1, 2, figsize=(6.45, 3.3), layout='constrained')
    xs = [c['source']['maximum_coordinate_bits'] for c in multiples]
    for arm, label, color, marker, style in arms:
        axes[0].plot(xs, [val(c, arm) / 1e6 for c in multiples], label=label,
                color=color, marker=marker, linestyle=style, linewidth=1.5, markersize=4)
        axes[1].plot(xs, [val(c, arm, 'certificate_bytes') / 1024 for c in multiples],
                label=label, color=color, marker=marker, linestyle=style,
                linewidth=1.5, markersize=4)
    for ax in axes:
        ax.set_xscale('log')
        ax.set_xlabel('Maximum coordinate bits B')
        ax.set_xticks([139, 4107, 32779], ['139', '4,107', '32,779'])
        ax.grid(axis='y', which='major', linewidth=0.65)
        ax.tick_params(axis='x', labelsize=8)
    axes[0].set_ylabel('Median producer + replay (ms)')
    axes[0].set_ylim(bottom=0)
    axes[1].set_ylabel('Serialized certificate (KiB)')
    axes[1].set_yscale('log')
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc='outside lower center', ncol=3,
               frameon=False, fontsize=8)
    for extension in ('pdf', 'png'):
        fig.savefig(figures / ('multiplicity_timing_and_proofs.' + extension), dpi=220)
    plt.close(fig)

    fields = ['case', 'family', 'tetrahedra', 'maximum_coordinate_bits']
    for arm, _, _, _, _ in arms + [('direct_aa', '', '', '', '')]:
        fields.extend([arm + '_' + f for f in ('producer_ms', 'verifier_ms', 'total_ms', 'proof_bytes')])
    fields.extend(['paired_reference_direct', 'paired_direct_core', 'paired_aa_direct'])
    with (root / 'benchmark_summary.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        for case in data['cases']:
            source = case['source']
            record = dict(case=source['name'], family=source['family'],
                          tetrahedra=source['tetrahedra'],
                          maximum_coordinate_bits=source['maximum_coordinate_bits'])
            for arm, _, _, _, _ in arms + [('direct_aa', '', '', '', '')]:
                for f in ('producer', 'verifier', 'total'):
                    record[arm + '_' + f + '_ms'] = val(case, arm, f + '_ns') / 1e6
                record[arm + '_proof_bytes'] = val(case, arm, 'certificate_bytes')
            record.update(paired_reference_direct=ratio(case, 'reference_to_direct'),
                          paired_direct_core=ratio(case, 'direct_to_reduced'),
                          paired_aa_direct=ratio(case, 'direct_aa_to_direct'))
            writer.writerow(record)

    lines = [r'''\subsection{Final measurements}
The recorded environment is Python 3.12.14 on Linux x86\_64 with glibc 2.39.
The run on 9 October 2026 took approximately 183 seconds, including fixture
construction and out-of-timer serialization. All 260 measured calls and 52
warm-up calls completed; all result spectra agreed and all certificates
verified. Source hashes before and after the run agree. A separate formula
audit checks all 312 result hashes and the 52 retained proof summaries.

\begin{table}[htbp]
\centering\small
\begin{tabular}{rrrrrr}
\toprule
$t$ & $B$ & Reference (ms) & Direct (ms) & Core (ms) & Ref./direct\\
\midrule''']
    for case in dimensions:
        source = case['source']
        lines.append(f"{source['tetrahedra']} & {source['maximum_coordinate_bits']} & "
                     f"{val(case, 'coordinates_reference')/1e6:,.3f} & "
                     f"{val(case, 'direct')/1e6:,.3f} & {val(case, 'reduced')/1e6:,.3f} & "
                     f"{ratio(case, 'reference_to_direct'):.3f}$\\times$\\\\")
    lines.append(r'''\bottomrule
\end{tabular}
\caption{Primitive layered meridians. Times are medians of producer plus
independent replay. The final column is a median of paired ratios.}
\label{tab:dimension}
\end{table}

\begin{figure}[htbp]
\centering
\includegraphics[width=\linewidth]{figures/dimension_timing.pdf}
\caption{Observed dimension-family timings, on logarithmic axes. Connecting
segments guide the eye; they are not fitted asymptotic laws. Core and direct
curves nearly coincide because these vectors have no large removable content.}
\label{fig:dimension}
\end{figure}

At $t=128$, the direct and coordinate-reference medians are approximately
2.662 and 14.913 seconds. The paired reference/direct factor is 5.733.
The corresponding serialized certificates contain 3,579,367 and 6,082,406
bytes. Thus this family shows increasing practical benefit from the smaller
observer, including a particularly large reduction in coordinate-reference
verification work. It does not identify a universal exponent in $t$.

\begin{table}[htbp]
\centering\small
\begin{tabular}{rrrrrr}
\toprule
Exponent $b$ & Input $B$ & Reference (ms) & Direct (ms) & Core (ms) & Direct/core\\
\midrule''')
    for case in multiples:
        source = case['source']
        lines.append(f"{source['parameters']['exponent_bits']:,} & {source['maximum_coordinate_bits']:,} & "
                     f"{val(case, 'coordinates_reference')/1e6:,.3f} & "
                     f"{val(case, 'direct')/1e6:,.3f} & {val(case, 'reduced')/1e6:,.3f} & "
                     f"{ratio(case, 'direct_to_reduced'):.3f}$\\times$\\\\")
    lines.append(r'''\bottomrule
\end{tabular}
\caption{Fixed $16$-tetrahedron core with $g=2^b$ and
$x_g=gD+(g+1)L$. All full-coordinate gcds are one.}
\label{tab:multiplicity}
\end{table}

\begin{figure}[htbp]
\centering
\includegraphics[width=\linewidth]{figures/multiplicity_timing_and_proofs.pdf}
\caption{The fixed-core family: observed time and certificate size.
Only the orbit-query core becomes small; original source coordinates,
divisor and restored binary multiplicities still appear in the computation.}
\label{fig:multiplicity}
\end{figure}

For the largest fixed-core input, with $B=32,779$, the direct and core
medians are 331.892 and 32.055 milliseconds; the paired improvement is
10.368. The certificates shrink from 10,081,806 to 123,278 bytes, a factor
of about 81.78. The reduced proof therefore remains dependent on $B$, as
predicted, but avoids repeating large multiplicities throughout the orbit
trace. Serialized size is not peak resident memory: the latter was not
measured.

\begin{table}[htbp]
\centering\small
\begin{tabular}{lrrrr}
\toprule
Family & Reference (ms) & Direct (ms) & Core (ms) & Direct/core\\
\midrule''')
    labels = [r'M\"obius, even', r'M\"obius, odd', 'Klein, odd', r'M\"obius + sphere/disc links']
    for case, label in zip(others, labels):
        lines.append(f"{label} & {val(case, 'coordinates_reference')/1e6:,.3f} & "
                     f"{val(case, 'direct')/1e6:,.3f} & {val(case, 'reduced')/1e6:,.3f} & "
                     f"{ratio(case, 'direct_to_reduced'):.3f}$\\times$\\\\")
    aa = [ratio(c, 'direct_aa_to_direct') for c in data['cases']]
    lines.append(r'''\bottomrule
\end{tabular}
\caption{One-sided and mixed-link families at exponent 4,096. These include
parity restoration and the closed zero-signature collision.}
\label{tab:one-sided}
\end{table}

There are informative negative comparisons. On the $b=32,768$ meridian
mixture, the unreduced direct query is slower than the coordinate reference:
their median times are 331.892 versus 299.004 milliseconds, with a paired
reference/direct ratio of 0.900. The even M\"obius example similarly gives
a ratio of 0.945. The core mode is faster on both examples. On a primitive
$t=32$ meridian, reduction increases the median from 84.474 to 93.117
milliseconds; the paired direct/core ratio is 0.912. These measurements
support an explicit choice of representation, not a universal replacement
claim.
''')
    lines.append(f"Across all cases, the paired A/A ratios range from {min(aa):.3f} to "
                 f"{max(aa):.3f}. Five repeats are adequate for a transparent exploratory "
                 "comparison, but do not establish statistical significance for small "
                 "differences. No confidence interval, runtime-exponent fit, whole-knot "
                 "speedup, or extrapolation to untested hard diagrams is claimed. "
                 "The complete per-phase times, orders, exact inputs and proof hashes "
                 "are in the raw JSON; the accompanying CSV exposes every reported median.\n")
    # Keep each small results object beside its interpretation in this report.
    section = '\n'.join(lines).replace('[htbp]', '[H]')
    (root / 'benchmark_results.tex').write_text(section + '\n')
    print('Generated two PDF/PNG figures, benchmark_results.tex and benchmark_summary.csv')


if __name__ == '__main__':
    main()
