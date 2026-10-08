"""Generate LaTeX table fragments from the cross-validation and benchmark JSON files."""
import json
import os

os.chdir(os.path.dirname(os.path.abspath(__file__)))
D = 'data/'


def esc(s):
    return (str(s).replace('_', r'\_').replace('%', r'\%').replace('&', r'\&').replace('#', r'\#')
            .replace('^2', r'$^2$'))


def table(header, spec, rows, tail=''):
    body = "\n".join(rows)
    return (r"\begin{tabular}{" + spec + "}\n" + r"\toprule" + "\n" + header + r" \\" + "\n"
            + r"\midrule" + "\n" + body + "\n" + tail + r"\bottomrule" + "\n" + r"\end{tabular}" + "\n")


# Khovanov cross-validation
k = json.load(open(D + 'khovanov_xval.json'))
named = [c for c in k['cases'] if not c['case'].startswith('random')]
randoms = [c for c in k['cases'] if c['case'].startswith('random')]
rows = []
for c in named:
    r = c['ranks']
    rows.append(f"{esc(c['case'])} & {r['02']} & {r['03']} & {r['04']} & {r['05']} & {r['06']} & "
                f"{'yes' if c['agree'] else 'NO'} \\\\")
agree_random = sum(c['agree'] for c in randoms)
tail = (r"\midrule" + "\n" + f"{len(randoms)} random braid closures (3--4 strands, 6--10 letters) & "
        + r"\multicolumn{5}{c}{ranks 1--13} & " + f"{agree_random}/{len(randoms)}" + r" \\" + "\n")
open('tables/khovanov_xval.tex', 'w').write(
    table("Input & 02 & 03 & 04 & 05 & 06 & agree", "@{}lrrrrrl@{}", rows, tail))

# pattern cross-validation
p = json.load(open(D + 'pattern_xval.json'))
rows = [f"{r['vertices']} & {r['spherical_systems_tested']} & {r['attempts']} & {r['essential']} & "
        f"{r['disagreements']} \\\\" for r in p['random']]
open('tables/pattern_xval.tex', 'w').write(
    table("Vertices & spherical systems tested & random matchings drawn & essential & disagreements",
          "@{}rrrrr@{}", rows))
rows = [f"{esc(n)} & {'essential' if all(v.values()) else 'inessential'} & "
        f"{'yes' if len(set(v.values())) == 1 else 'NO'} \\\\" for n, v in p['named'].items()]
open('tables/pattern_named.tex', 'w').write(table("Pattern & verdict & all six agree", "@{}lll@{}", rows))

# grid cross-validation
if os.path.exists(D + 'grid_xval.json'):
    g = json.load(open(D + 'grid_xval.json'))
    rows = [f"{r['size']} & exhaustive (all shift orbits) & {r['orbits']} & {r['unknot']} & {r['knotted']} & "
            f"{r['disagree']} \\\\" for r in g['exhaustive']]
    rows += [f"{r['size']} & random, $\\le 14$ crossings & {r['tested']} & {r['unknot']} & {r['knotted']} & "
             f"{r['disagree']} \\\\" for r in g['random']]
    open('tables/grid_xval.tex', 'w').write(
        table("Grid size & sample & diagrams & unknots & knots & disagreements", "@{}rlrrrr@{}", rows))

# fastunknot benchmark
bpath = '../fast/results/benchmark_0.1.json'
if os.path.exists(bpath):
    b = json.load(open(bpath))
    def cell(v):
        return 'timeout' if v is None else str(v)
    rows = [f"{esc(r['family'])} & {r['crossings']} & {cell(r['reduced_rank'])} & {cell(r['max_boundary'])} & "
            f"{cell(r['max_objects_before_elimination'])} & {cell(r['max_objects_after_elimination'])} & "
            f"{r['seconds']:.3f} \\\\" for r in b['scan_families']]
    open('tables/benchmark.tex', 'w').write(
        table("Family & $n$ & reduced rank & max.\\ boundary & objects before & objects after & seconds",
              "@{}lrrrrrr@{}", rows))
    rows = [f"{esc(r['example'])} & {r['crossings']} & {r['status']} & {esc(r['method'])} & "
            f"{r['seconds']:.4f} \\\\" for r in b['pipeline']]
    open('tables/pipeline.tex', 'w').write(
        table("Example & $n$ & verdict & deciding step & seconds", "@{}lrllr@{}", rows))


# ---------------------------------------------------------------------------
# acceleration proposals, fastunknot 0.2, Rust
# ---------------------------------------------------------------------------
def ms(row, cap=None):
    """Milliseconds with three significant digits, or a censoring marker."""
    if row is None:
        return '--'
    if 'timeout' in row:
        return f"$>${row['timeout']:.0f}\,s"
    if 'seconds' not in row:
        return 'n/a'
    v = row['seconds'] * 1000
    return f"{v:.0f}" if v >= 100 else f"{v:.1f}" if v >= 10 else f"{v:.2f}" if v >= 0.1 else f"{v:.3f}"


def load(path):
    return json.load(open(path)) if os.path.exists(path) else None


props = load(D + 'proposals_bench_proposals.json')
basenew = load(D + 'proposals_bench_base_new.json')
rust = load('../rust/results/profile.json')
if props and basenew:
    cell = {}
    for r in props:
        if r['engine'] != 'base':
            cell[r['mode'], r['case'], r['engine']] = r
    for r in basenew:
        cell[r['mode'], r['case'], r['engine']] = r
    for r in load(D + 'proposals_bench_rank_rerun.json') or []:      # rank task through each engine's factored API
        cell[r['mode'], r['case'], r['engine']] = r
    if rust:
        group = {'raw': 'raw', 'rank': 'rank', 'recognize': 'recognize'}
        for r in rust['rows']:
            if r['group'] in group and not [o for o in r['options'] if o not in ('--factor',)]:
                cell[group[r['group']], r['case'], 'rust'] = r
    engines = ['base', '01', '02', '03', '04', '05', '06', '07', '08', '09', 'new', 'rust']
    order = []
    for r in props:
        key = (r['mode'], r['case'])
        if key not in order:
            order.append(key)
    names = {'raw': 'scan', 'rank': 'rank', 'recognize': 'recognize'}
    rows = []
    previous = None
    for mode, case in order:
        if previous is not None and previous != mode:
            rows.append(r"\midrule")
        previous = mode
        cells = " & ".join(ms(cell.get((mode, case, e))) for e in engines)
        rows.append(f"{names[mode]}: {esc(case)} & {cells} \\\\")
    header = "Task & 0.1 & " + " & ".join(engines[1:10]) + r" & 0.2 & Rust"
    open('tables/proposals_bench.tex', 'w').write(table(header, "@{}l" + "r" * 12 + "@{}", rows))

abl = load('../fast/results/ablation.json')
if abl:
    scan = [r for r in abl['rows'] if r['group'] == 'scan']
    cases, configs = [], []
    for r in scan:
        if r['case'] not in cases:
            cases.append(r['case'])
        if r['config'] not in configs:
            configs.append(r['config'])
    rows = []
    for config in configs:
        cells = " & ".join(ms(next((r for r in scan if r['case'] == c and r['config'] == config), None)) for c in cases)
        rows.append(f"{esc(config)} & {cells} \\\\")
    open('tables/ablation_scan.tex', 'w').write(
        table("Scanner configuration & " + " & ".join(esc(c) for c in cases), "@{}l" + "r" * len(cases) + "@{}", rows))
    rest = [r for r in abl['rows'] if r['group'] != 'scan']
    rows = []
    for i in range(0, len(rest), 2):
        a, b = rest[i], rest[i + 1]
        ratio = (b['seconds'] / a['seconds']) if 'seconds' in a and 'seconds' in b else None
        times = "$" + chr(92) + "times$"
        ratio = f"{ratio:.0f}{times}" if ratio and ratio >= 10 else f"{ratio:.1f}{times}" if ratio else "censored"
        rows.append(f"{esc(a['case'])} & {esc(a['config'])}: {ms(a)} & {esc(b['config'])}: {ms(b)} & {ratio} \\\\")
    open('tables/ablation_other.tex', 'w').write(
        table("Task & new (ms) & old (ms) & ratio", "@{}p{0.36\linewidth}p{0.23\linewidth}p{0.27\linewidth}r@{}", rows))

if rust:
    rows = []
    for r in rust['rows']:
        if r['group'] != 'scaling':
            continue
        if 'stats' not in r:
            rows.append(f"{esc(r['case'])} & \multicolumn{{6}}{{l}}{{budget of 300 s exhausted}} \\\\")
            continue
        s = r['stats']
        rows.append(f"{esc(r['case'])} & {r['reduced_rank']} & {s['max_boundary']} & {s['max_objects_after_elimination']} & "
                    f"{r['seconds']:.3f} & {s['seconds_transfer']:.3f} & {s['seconds_eliminate']:.3f} \\\\")
    open('tables/rust_scaling.tex', 'w').write(
        table("Input & reduced rank & boundary & objects & total s & transfer s & eliminate s", "@{}lrrrrrr@{}", rows))
    rows = []
    for r in rust['rows']:
        if r['group'] == 'ablation':
            rows.append(f"{esc(r['case'])} & {esc(' '.join(r['options'][:2]))} & {ms(r)} \\\\")
    open('tables/rust_ablation.tex', 'w').write(table("Input & option & ms", "@{}llr@{}", rows))

residue = load('../fast/results/residue_integration_20261007.json')
if residue:
    rows = []
    for r in residue['cases']:
        rows.append(f"{esc(r['name'])} & {r['median_speedup']:.3f} & "
                    f"{r['median_adaptive_speedup']:.3f} & {r['median_aa']:.3f}" + r" \\")
    rows.append(r"\midrule")
    for r in residue['kernels']:
        rows.append(f"Synthetic, {2*r['size']+1} objects & {r['median_speedup']:.2f} & "
                    f"{r['median_adaptive_speedup']:.2f} & {r['median_aa']:.3f}" + r" \\")
    with open('tables/residue-integration.tex', 'w') as handle:
        handle.write(r"\begin{center}" + "\n" +
                     table("Input & Eager ratio & Adaptive ratio & A/A", "@{}lrrr@{}", rows) +
                     r"\end{center}" + "\n" +
                     "Ratios are median paired standard/new times; values above one are faster.\n")

homogeneous = load('../fast/results/homogeneous_integration_20261008.json')
graded = load('../fast/results/adaptive_graded_20261008.json')
if homogeneous and graded:
    rows = []
    kernels = {(r['name'], r['scope']): r for r in homogeneous['kernels']}
    for r in homogeneous['kernels']:
        if r['scope'] != 'product':
            continue
        full = kernels[r['name'], 'full_component']
        rows.append(f"{esc(r['name'])} & {r['median_speedup']:.2f} & {full['median_speedup']:.2f}" + r" \\")
    content = (r"\begin{center}" + "\n" +
               table("Kernel & Product ratio & Full component ratio", "@{}lrr@{}", rows) +
               r"\end{center}" + "\n")
    rows = [f"{r['objects']} & {r['median_speedup']:.2f} & {r['median_aa']:.3f}" + r" \\"
            for r in graded['cases']]
    content += (r"\begin{center}" + "\n" +
                table("Graded two-term objects & Adaptive ratio & A/A", "@{}lrr@{}", rows) +
                r"\end{center}" + "\n")
    rows = [f"{esc(r['name'])} & {r['median_speedup']:.3f} & {r['median_aa']:.3f}" + r" \\"
            for r in homogeneous['scans']]
    content += (r"\begin{center}" + "\n" +
                table("Forced component scan & Ranked/new ratio & A/A", "@{}lrr@{}", rows) +
                r"\end{center}" + "\n" +
                "All speedups are median paired old/new times; values above one are faster.\n")
    with open('tables/homogeneous-integration.tex', 'w') as handle:
        handle.write(content)

print('tables written:', sorted(os.listdir('tables')))

windows = load('../fast/results/window_integration_20261008.json')
if windows:
    rows = []
    for r in windows['cases']:
        ratios = ' & '.join(f"{r[k]:.3f}" for k in (
            'median_full_over_window', 'median_zero_speedup', 'median_widen_speedup', 'median_aa'))
        rows.append(f"{esc(r['name'])} & {ratios}" + r" \\")
    content = (r"\begin{center}" + '\n' +
               table('Input & Full/window & Probe 0 & Probe 4 & A/A', '@{}lrrrr@{}', rows) +
               r"\end{center}" + '\n' +
               'Ratios are median paired baseline/new times; values above one are faster.\n')
    with open('tables/window-integration.tex', 'w') as handle:
        handle.write(content)

continuations = load('../fast/results/continuation_integration_20261008.json')
if continuations:
    rows = []
    for r in continuations['cases']:
        ratios = r['median_full_over']
        cells = ' & '.join(f"{ratios[k]:.3f}" for k in
                           ('barcode_exact', 'fitting_exact', 'fitting_decision', 'control'))
        rows.append(f"{esc(r['name'])} & {cells}" + r" \\")
    content = (r"\begin{center}" + '\n' +
               table('Input & Interval exact & Fitting exact & Fitting decision & A/A',
                     '@{}lrrrr@{}', rows) + r"\end{center}" + '\n' +
               'Ratios are median paired full-scanner/new times; values below one are slower.\n')
    with open('tables/continuation-integration.tex', 'w') as handle:
        handle.write(content)

ranktwo = load('../fast/results/ranktwo_integration_20261008.json')
if ranktwo:
    rows = [f"{esc(r['name'])} & {r['median_speedup']:.3f} & {r['median_aa']:.3f}" + r" \\"
            for r in ranktwo['cases']]
    with open('tables/ranktwo-integration.tex', 'w') as handle:
        handle.write(r"\begin{center}" + '\n' +
                     table('Input & Disabled/enabled & A/A', '@{}lrr@{}', rows) +
                     r"\end{center}" + '\n' +
                     'Ratios are median paired end-to-end times; values above one are faster.\n')

minimal = load('../fast/results/minimal_windows_20261008.json')
if minimal:
    rows=[]
    for r in minimal['cases']:
        v=r['median_full_over']
        rows.append(f"{esc(r['name'])} & {v['support']:.2f} & {v['minimal']:.2f} & "
                    f"{r['median_support_over_minimal']:.3f} & {v['control']:.3f}" + r" \\")
    with open('tables/minimal-window-integration.tex','w') as handle:
        handle.write(r"\begin{center}"+'\n'+
            table('Input & Full/support & Full/minimal & Support/minimal & A/A','@{}lrrrr@{}',rows)+
            r"\end{center}"+'\n'+'Ratios are medians of paired times; larger than one favors the denominator.\n')

corridor = load('../fast/results/corridor_integrated_20261008.json')
if corridor:
    rows = []
    for row in corridor['actual']:
        v = row['paired_ratios']
        cells = ' & '.join(f"{v[k]:.3f}" for k in (
            'standard_over_auto', 'standard_over_adaptive',
            'standard_over_compressed', 'standard_over_control'))
        switches = row['metrics']['adaptive']['stats'].get('corridor_switches', 0)
        rows.append(f"{esc(row['name'])} & {cells} & {switches}" + r" \\")
    content = (r"\begin{center}" + '\n' +
        table('Raw scan & Std/corridor & Std/adapt. & Std/sparse & A/A & Switches',
              '@{}lrrrrr@{}', rows) + r"\end{center}" + '\n' +
        'Sparse denotes the component-scalar/Boolean-port configuration. '
        'Ratios above one favor the denominator.\n')
    rows = []
    for row in corridor['kernels']:
        v = row['paired_ratios']
        cells = ' & '.join(f"{v[k]:.3f}" for k in (
            'prior_over_auto', 'prior_over_compressed',
            'standard_over_compressed', 'standard_over_control'))
        rows.append(f"{esc(row['name'])} & {cells}" + r" \\")
    content += (r"\begin{center}" + '\n' +
        table('Constructed stage & Fwd/corridor & Fwd/sparse & Std/sparse & A/A',
              '@{}lrrrr@{}', rows) + r"\end{center}" + '\n' +
        'Fwd denotes the maintained quantum-ordered forward transfer. '
        'These timings include scalar and graph setup.\n')
    with open('tables/corridor-transfer-integration.tex', 'w') as handle:
        handle.write(content)

garside = load('../fast/results/cyclic_garside_pipeline_20261008.json')
garside_kernel = load('../fast/results/cyclic_garside_kernel_20261008.json')
if garside and garside_kernel:
    rows = []
    for row in garside['cases']:
        ratios = row['paired_ratios']
        cells = ' & '.join('unknown' if ratios[k] is None else f'{ratios[k]:.3f}'
                           for k in ('off_over_radius1', 'off_over_radius2', 'off_over_control'))
        rows.append(f"{esc(row['name'])} & {row['crossings']} & {cells}" + r" \\")
    content = (r"\begin{center}" + '\n' +
        table('Recognition input & $n$ & Off/radius 1 & Off/radius 2 & A/A',
              '@{}lrrrr@{}', rows) + r"\end{center}" + '\n' +
        'Ratios are medians of paired complete-recognition times; '
        'values above one favor the enabled policy.\n')
    rows = [f"{esc(row['case'])} & {row['n']} & {row['paired_speedup']:.3f} & "
            f"{row['aa_ratio']:.3f}" + r" \\" for row in garside_kernel['summary']]
    content += (r"\begin{center}" + '\n' +
        table('Isolated compressor & $n$ & Repeated/shared & A/A', '@{}lrrr@{}', rows) +
        r"\end{center}" + '\n' +
        'Both compressor arms search all cuts without lower-bound pruning and '
        'generate and replay only the winning certificate.\n')
    with open('tables/cyclic-garside-integration.tex', 'w') as handle:
        handle.write(content)

surface_cover = load('../fast/results/surface_cover_20261008.json')
if surface_cover:
    rows = [f"{esc(row['name'])} & {row['sheets']} & {row['families']} & "
            f"{row['expanded_over_compressed']:.2f} & {row['control_over_compressed']:.3f}" + r" \\"
            for row in surface_cover['topology']]
    content = (r"\begin{center}" + '\n' +
        table('Supplied cover & Sheets & Records & Expanded/compressed & A/A',
              '@{}lrrrr@{}', rows) + r"\end{center}" + '\n' +
        'Ratios are median paired times for complete cover topology; '
        'sheet expansion is an independent oracle, not a competing compressed algorithm.\n')
    rows = [f"{row['sheet_exponent']} & {row['marks']} & {1e3*row['query_seconds']:.3f} & "
            f"{row['signature_json_bytes']} & {row['control_over_query']:.3f}" + r" \\"
            for row in surface_cover['marked_queries']]
    content += (r"\begin{center}" + '\n' +
        table('Sheet exponent & Marks & Query (ms) & JSON bytes & A/A',
              '@{}rrrrr@{}', rows) + r"\end{center}" + '\n' +
        'Marked queries reuse a prepared index, with sheet count $W=2^{\\mathrm{exponent}}$. '
        'Preparation and serialization are outside query timing.\n')
    with open('tables/surface-cover-integration.tex', 'w') as handle:
        handle.write(content)

shadow = load('../fast/results/marked_shadow_20261008.json')
if shadow:
    by_case = {}
    for row in shadow['rows']:
        by_case.setdefault(row['name'], {})[row['scope']] = row
    rows = []
    for name, scopes in by_case.items():
        cells = []
        for scope, arm in [('recognition', 'shadow'), ('recognition', 'control'),
                           ('raw-decision', 'shadow'), ('raw-decision', 'euler'),
                           ('raw-decision', 'control')]:
            ratios = scopes[scope]['median_speedups']
            cells.append('unknown' if ratios is None else f'{ratios[arm]:.3f}')
        rows.append(esc(name) + ' & ' + ' & '.join(cells) + r' \\')
    content = (r'\begin{center}\small' + '\n' +
        table('Input & Full/shadow & A/A & Raw/shadow & Raw/Euler & A/A',
              '@{}lrrrrr@{}', rows) + r'\end{center}' + '\n' +
        'Ratios are median paired times; values above one favor the denominator. '
        'Full uses the previous default recognizer; raw uses the saturated scanner. '
        'A/A compares identical implementations in each scope.\n')
    with open('tables/determinant_benchmark.tex', 'w') as handle:
        handle.write(content)

closure = load('../fast/results/closure_reset_20261008.json')
if closure:
    by_case = {}
    for row in closure['rows']:
        by_case.setdefault(row['name'], {})[row['scope']] = row
    rows = []
    for name, scopes in by_case.items():
        cells = []
        for scope, arm in [('recognition', 'closure'), ('raw-decision', 'closure'),
                           ('raw-decision', 'no-reset'), ('raw-decision', 'euler'),
                           ('raw-decision', 'control')]:
            ratios = scopes[scope]['median_speedups']
            cells.append('unknown' if ratios is None else f'{ratios[arm]:.3f}')
        display = name.replace('report28_', 'R28 ')
        rows.append(esc(display) + ' & ' + ' & '.join(cells) + r' \\')
    content = (r'\begin{center}\small' + '\n' +
        table('Input & Full/reset & Raw/reset & Raw/no reset & Raw/Euler & Raw A/A',
              '@{}lrrrrr@{}', rows) + r'\end{center}' + '\n' +
        'Ratios are median paired times; values above one favor the denominator. '
        'Full uses the previous default recognizer; raw uses the saturated scanner. '
        'The no-reset arm retains closure observations but does not restart.\n')
    with open('tables/closure_benchmark.tex', 'w') as handle:
        handle.write(content)

boundary = load('../fast/results/boundary_reuse_20261008.json')
if boundary:
    by_case = {}
    for row in boundary['rows']:
        by_case.setdefault(row['name'], {})[row['scope']] = row
    streams, pipelines = [], []
    for name, scopes in by_case.items():
        if 'euler-stream' in scopes:
            euler = scopes['euler-stream']
            e, s = euler['median_speedups'], scopes['shadow-stream']['median_speedups']
            cells = [e['adaptive'], e['eager'], e['control'], s['boundary'], s['control']]
            streams.append(str(euler['input']['suffix_crossings']) + ' & ' +
                           ' & '.join(f'{v:.3f}' for v in cells) + r' \\')
        else:
            r = scopes['raw-euler']['median_speedups']
            f = scopes['recognition-euler']['median_speedups']
            cells = [r['adaptive'], r['control'], f['adaptive'], f['control']]
            pipelines.append(esc(name) + ' & ' +
                             ' & '.join(f'{v:.3f}' for v in cells) + r' \\')
    for filename, heading, columns, rows in [
        ('boundary_streams', '$n$ & Euler adaptive & Euler eager & A/A & Tait boundary & A/A',
         '@{}rrrrrr@{}', streams),
        ('boundary_pipeline', 'Input & Raw adaptive & A/A & Full adaptive & A/A',
         '@{}lrrrr@{}', pipelines),
    ]:
        with open(f'tables/{filename}.tex', 'w') as handle:
            handle.write(r'\begin{center}\small' + '\n' + table(heading, columns, rows) +
                         r'\end{center}' + '\n' +
                         'Ratios are median paired direct/alternative times; values above one '
                         'favor the alternative. A/A compares identical direct implementations.\n')

tait_blocks = load('../fast/results/tait_blocks_20261008.json')
if tait_blocks:
    by_case = {}
    for row in tait_blocks['rows']:
        by_case.setdefault(row['name'], {})[row['scope']] = row
    names = dict(conway='Conway', conway_double_three='Conway double three',
                 conway_forbidden_pretzel='Conway pretzel', conway_sum_2='Conway sum 2',
                 conway_sum_3='Conway sum 3', conway_sum_8='Conway sum 8',
                 conway_sum_16='Conway sum 16', conway_sum_32='Conway sum 32',
                 figure_eight='Figure eight', grid_determinant_one_knot='Grid determinant one',
                 grid_scrambled_unknot='Scrambled unknot', hard_unknot_8='Hard unknot 8',
                 kinoshita_terasaka='Kinoshita--Terasaka', stress_braid5_36='Stress braid 36',
                 torus_3_5='$T(3,5)$', trefoil='Trefoil', unknot='Crossingless unknot',
                 unknot_braid40='Braid unknot 40')
    rows = []
    for name, scopes in by_case.items():
        cells = []
        for scope in ('closure', 'raw-shadow', 'recognition-shadow'):
            ratios = scopes[scope]['median_speedups'] if scope in scopes else None
            cells.extend(['---', '---'] if ratios is None else
                         [f'{ratios[k]:.3f}' for k in ('blocks', 'control')])
        rows.append(names[name] + ' & ' + ' & '.join(cells) + r' \\')
    with open('tables/tait_blocks_benchmark.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
                     table('Input & Initial & A/A & Raw & A/A & Full & A/A',
                           '@{}lrrrrrr@{}', rows) + r'\end{center}' + '\n' +
                     'Ratios are median paired direct/block times; values above one favor '
                     'block evaluation. A/A compares identical direct implementations. '
                     'Every scope includes fresh setup.\n')

fallback = load('../fast/results/shadow_fallback_20261008.json')
if fallback:
    names = {
        'conway_sum_8': 'Conway sum 8',
        'conway_sum_8_w0_q4096': 'Conway sum 8',
        'conway_sum_8_w2800_q4096': 'Conway sum 8',
        'conway_sum_8_w2800_q1': 'Conway sum 8',
        'torus_3_5_w0_q4096': '$T(3,5)$',
        'hard_unknot_8_w0_q4096': 'Hard unknot 8',
        'conway_torus151_heuristic': '313 crossings, heuristic',
        'conway_torus151_supplied': '313 crossings, supplied',
    }
    rows = []
    for row in fallback['rows']:
        if row['scope'] != 'raw-shadow' or row['name'] not in names:
            continue
        ratios = row['median_speedups']
        before, after = (row['evidence'][arm].get('stage', 'unknown')
                         for arm in ('baseline', 'fallback'))
        work = row['options']['shadow_max_work']
        work = '$10^6$' if work == 1_000_000 else str(work)
        cells = ['unknown', 'unknown'] if ratios is None else [f'{ratios[k]:.3f}' for k in ('fallback', 'control')]
        rows.append(names[row['name']] + f" & {work} & {row['options']['euler_max_states']} & " +
                    f'{before} & {after} & ' + ' & '.join(cells) + r' \\')
    with open('tables/shadow_fallback_benchmark.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
                     table('Input/order & $W$ & $K$ & Old stop & New stop & Speedup & A/A',
                           '@{}lrrrrrr@{}', rows) + r'\end{center}' + '\n' +
                     'Ratios are median paired baseline/fallback times for complete raw scans. '
                     'Stop columns give the processed crossing count. A/A compares identical baselines.\n')
