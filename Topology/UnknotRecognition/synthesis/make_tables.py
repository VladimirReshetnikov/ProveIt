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

separator_orders = load('../fast/results/separator_orders_20261008.json')
if separator_orders:
    names = {'grid-8': r'Grid $8\times8$', 'grid-32': r'Grid $32\times32$',
             'tree-5': 'Tree medial, height 5', 'tree-7': 'Tree medial, height 7',
             'tree-9': 'Tree medial, height 9'}
    rows = []
    for row in separator_orders['ordering']:
        if row['name'] not in names:
            continue
        bounded = row['bounded']
        cells = [names[row['name']], str(row['n']), str(row['greedy_profile'][0]),
                 str(bounded['separator']['profile'][0]), str(bounded['profile'][0]),
                 f"{1000*row['median_seconds']['greedy']:.3f}",
                 f"{1000*row['median_seconds']['bounded']:.3f}"]
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/separator_orders.tex', 'w') as handle:
        handle.write(table('Family & $n$ & Greedy & Separator & Selected & Greedy ms & Bounded ms',
                           '@{}lrrrrrr@{}', rows))

adaptive_potts = load('../fast/results/adaptive_potts_20261008.json')
if adaptive_potts:
    names = {'conway': 'Conway', 'tree-7': 'Tree medial 254',
             'grid-4-random-order': 'Grid 16, shuffled',
             'grid-8-random-order': 'Grid 64, shuffled',
             'grid-10': 'Grid 100', 'grid-12': 'Grid 144'}
    rows = []
    for row in adaptive_potts['rows']:
        if row['scope'] != 'scalar' or row['name'] not in names:
            continue
        cells = [names[row['name']]]
        for arm in ('ordinary', 'control', 'eager', 'initial', 'adaptive'):
            cells.append(f"{1000*row['median_seconds'][arm]:.3f}"
                         if arm in row['completed_arms'] else 'limit')
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/adaptive_potts.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
                     table('Scalar input & Ordinary & A/A & Eager & Initial & Adaptive',
                           '@{}lrrrrr@{}', rows) + r'\end{center}' + '\n' +
                     'Median milliseconds including all setup. A/A repeats ordinary exact Potts. '
                     'A limit is a censored query, not a completed scalar value.\n')

faithful_jones = load('../fast/results/faithful_jones_20261008.json')
if faithful_jones:
    names = {'conway': 'Conway', 'hard_unknot_8': 'Hard unknot 8',
             'weaving-10': 'Weaving 10', 'tree-7': 'Tree medial 254',
             'grid-8-random': 'Grid 64, shuffled', 'grid-10': 'Grid 100'}
    rows = []
    for row in faithful_jones['rows']:
        if row['name'] not in names:
            continue
        cells = [names[row['name']]]
        for arm in ('fixed6', 'control6', 'identity', 'polynomial'):
            complete = all(s['result'][arm]['status'] == 'COMPLETE' for s in row['samples'])
            cells.append(f"{1000*row['median_seconds'][arm]:.3f}" if complete else 'limit')
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/faithful_jones.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
                     table('Input & Fixed $q=6$ & A/A & Identity & Full polynomial',
                           '@{}lrrrr@{}', rows) + r'\end{center}' + '\n' +
                     'Median milliseconds including setup; distinct output guarantees. '
                     'A limit is a censored query.\n')

jones_shortcut = load('../fast/results/jones_identity_shortcut_20261008.json')
if jones_shortcut:
    names = {'trefoil': 'Trefoil', 'conway': 'Conway', 'hard_unknot_8': 'Hard unknot 8',
             'tree-6': 'Tree medial 126', 'tree-7': 'Tree medial 254',
             'grid-10': 'Grid 100', 'grid-8-random': 'Grid 64, shuffled'}
    rows = []
    for row in jones_shortcut['rows']:
        cells = [names[row['name']]]
        cells.extend(f"{1000*row['median_seconds'][arm]:.3f}"
                     for arm in ('before', 'control', 'after'))
        cells.append(f"{row['median_paired_speedup']:.3f}")
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/jones_identity_shortcut.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
                     table('Full polynomial query & Before & A/A & After & Paired speedup',
                           '@{}lrrrr@{}', rows) + r'\end{center}' + '\n' +
                     'Median milliseconds including setup. Ratios are medians of paired '
                     'before/after times for identical complete results.\n')

whitehead_power = load('../fast/results/whitehead_power_20261008.json')
if whitehead_power:
    from statistics import median
    arms = ('baseline', 'control', 'powers')
    rows = ['Small 14, summed medians & ' + ' & '.join(
        f"{1000*sum(r['median_seconds'][a] for r in whitehead_power['rows'] if r['name'] != 'gordian'):.3f}"
        for a in arms) + r' \\']
    gordian = next(r for r in whitehead_power['rows'] if r['name'] == 'gordian')
    rows.append('Gordian, full query & ' + ' & '.join(
        f"{1000*gordian['median_seconds'][a]:.3f}" for a in arms) + r' \\')
    for row in whitehead_power['capacity']:
        rows.append(f"Gordian group, cap {row['max_letters']} & " + ' & '.join(
            f"{1000*median(s['measurements'][a]['seconds'] for s in row['samples']):.3f}"
            for a in arms) + r' \\')
    with open('tables/whitehead_power_queries.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Scope & Before & A/A & Powers', '@{}lrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds; all queries and group probes complete.\n')
    rows = []
    for row in whitehead_power['kernels']:
        cells = [str(row['bits'])]
        for arm in arms:
            complete = all(s['measurements'][arm]['success'] for s in row['samples'])
            cells.append(f"{1000*median(s['measurements'][arm]['seconds'] for s in row['samples']):.3f}"
                         if complete else 'limit')
        cells.extend(str(row['samples'][0]['measurements']['powers'][k]) for k in ('moves', 'nodes'))
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/whitehead_power_kernels.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('$h$ in $N=2^h$ & Before & A/A & Powers & Moves & Nodes', '@{}rrrrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds including grammar construction. '
            'Limits are censored; moves and nodes describe the new search.\n')

compressed_match = load('../fast/results/compressed_match_20261008.json')
if compressed_match:
    from statistics import median
    arms = ('baseline', 'control', 'matching')
    rows = ['Small 14, summed medians & ' + ' & '.join(
        f"{1000*sum(r['median_seconds'][a] for r in compressed_match['rows'] if r['name'] != 'gordian'):.3f}"
        for a in arms) + r' \\']
    gordian = next(r for r in compressed_match['rows'] if r['name'] == 'gordian')
    rows.append('Gordian, full query & ' + ' & '.join(
        f"{1000*gordian['median_seconds'][a]:.3f}" for a in arms) + r' \\')
    for row in compressed_match['capacity']:
        rows.append(f"Gordian group, cap {row['max_letters']} & " + ' & '.join(
            f"{1000*median(s['measurements'][a]['seconds'] for s in row['samples']):.3f}"
            for a in arms) + r' \\')
    with open('tables/compressed_match_queries.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Scope & Before & A/A & Matching', '@{}lrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds; all knot queries and group probes complete.\n')
    rows = []
    for row in compressed_match['presentations']:
        assert all(not s['measurements'][a]['success'] and s['measurements'][a]['reason'] == 'stalled'
                   for s in row['samples'] for a in ('baseline', 'control'))
        assert all(s['measurements']['matching']['success'] for s in row['samples'])
        new = row['samples'][0]['measurements']['matching']
        rows.append(f"{row['bits']} & stalled & " +
            f"{1000*median(s['measurements']['matching']['seconds'] for s in row['samples']):.3f} & " +
            f"{new['moves']} & {new['nodes']}" + r' \\')
    with open('tables/compressed_match_presentations.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('$h$ in $N=2^h$ & Before/A/A & New (ms) & Moves & Nodes', '@{}rlrrr@{}', rows) +
            r'\end{center}' + '\nFull construction and search on abstract presentations; '
            'stalls are incomplete searches, not completed recognition times.\n')
    rows = []
    names = {'first-hit': 'First candidate matches', 'later-hit': 'Later candidate matches', 'absent': 'No occurrence'}
    for row in compressed_match['matching']:
        cells = [names[row['kind']], str(row['bits'])]
        for arm in ('table', 'adaptive', 'control'):
            complete = all(s['measurements'][arm]['status'] == 'COMPLETE' for s in row['samples'])
            cells.append(f"{1000*median(s['measurements'][arm]['seconds'] for s in row['samples']):.3f}"
                         if complete else 'limit')
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/compressed_match_primitive.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Substring query & $h$ & Full table & Adaptive & A/A', '@{}lrrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds including grammar construction. '
            'A/A repeats the adaptive query; both positive and negative results are exact.\n')

relator_power = load('../fast/results/relator_power_20261008.json')
if relator_power:
    from statistics import median
    arms = ('baseline', 'control', 'full')
    rows = ['Small 14, summed medians & ' + ' & '.join(
        f"{1000*sum(r['median_seconds'][a] for r in relator_power['rows'] if r['name'] != 'gordian'):.3f}"
        for a in arms) + r' \\']
    gordian = next(r for r in relator_power['rows'] if r['name'] == 'gordian')
    rows.append('Gordian, full query & ' + ' & '.join(
        f"{1000*gordian['median_seconds'][a]:.3f}" for a in arms) + r' \\')
    for row in relator_power['capacity']:
        rows.append(f"Gordian group, cap {row['max_letters']} & " + ' & '.join(
            f"{1000*median(s['measurements'][a]['seconds'] for s in row['samples']):.3f}"
            for a in arms) + r' \\')
    with open('tables/relator_power_queries.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Scope & Before & A/A & Both changes', '@{}lrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds; all knot queries and group probes complete.\n')
    rows = []
    for row in relator_power['kernels']:
        cells = [str(row['bits']) if row['family'] == 'quotient' else 'Allocation, 500']
        for arm in ('baseline', 'control', 'quotient-prune', 'uniform', 'full'):
            complete = all(s['measurements'][arm]['success'] for s in row['samples'])
            cells.append(f"{1000*median(s['measurements'][arm]['seconds'] for s in row['samples']):.3f}"
                         if complete else 'limit/stall')
        full = row['samples'][0]['measurements']['full']
        cells.extend(str(full[k]) for k in ('moves', 'nodes'))
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/relator_power_kernels.tex', 'w') as handle:
        handle.write(r'\begin{center}\footnotesize' + '\n' +
            table('$h$ & Before & A/A & Quotient & Uniform & Both & Moves & Nodes',
                  '@{}lrrrrrrr@{}', rows) + r'\end{center}' + '\n' +
            'Median milliseconds including grammar construction; Quotient also includes pair pruning. '
            'Moves and nodes describe both changes. Limits/stalls are incomplete searches.\n')

compressed_lcs = load('../fast/results/compressed_lcs_20261008.json')
if compressed_lcs:
    from statistics import median
    arms = ('baseline', 'control', 'complete-overlap')
    rows = ['Small 14, summed medians & ' + ' & '.join(
        f"{1000*sum(r['median_seconds'][a] for r in compressed_lcs['rows'] if r['name'] != 'gordian'):.3f}"
        for a in arms) + r' \\']
    gordian = next(r for r in compressed_lcs['rows'] if r['name'] == 'gordian')
    rows.append('Gordian, full query & ' + ' & '.join(
        f"{1000*gordian['median_seconds'][a]:.3f}" for a in arms) + r' \\')
    with open('tables/compressed_lcs_queries.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Scope & Before & A/A & Complete overlap', '@{}lrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds; all full knot queries complete.\n')
    rows = []
    for row in compressed_lcs['kernels']:
        cells = [row['family'].capitalize(), str(row['bits'])]
        for arm in ('full', 'bound', 'control'):
            samples = [s['measurements'].get(arm) for s in row['samples']]
            if samples[0] is None:
                cells.append('---')
            elif all(s['status'] == 'COMPLETE' for s in samples):
                cells.append(f"{1000*median(s['seconds'] for s in samples):.3f}")
            else:
                cells.append('limit')
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/compressed_lcs_kernels.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('LCS family & $h$ & Full query & Count bound & A/A', '@{}lrrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds including grammar construction. '
            'A/A repeats the bounded query for Cyclic and the full query for Shifted. '
            'Limits are censored queries.\n')
        rows = []
        for row in compressed_lcs['moves']:
            first = row['samples'][0]
            rows.append(f"{row['bits']} & {1000*median(s['seconds'] for s in row['samples']):.3f} & " +
                        f"{first['nodes']} & {first['stats']['work']}" + r' \\')
        handle.write(r'\begin{center}\small' + '\n' +
            table('Partial move, $h$ & Milliseconds & Nodes & Charged work', '@{}rrrr@{}', rows) +
            r'\end{center}' + '\nIncludes grammar construction, failed whole-donor search, '
            'complete cyclic search and checked application. This is not a knot verdict.\n')

lcs_bounds = load('../fast/results/lcs_bounds_20261008.json')
if lcs_bounds:
    from statistics import median
    arms = ('baseline', 'control', 'full')
    rows = ['Small 14, summed medians & ' + ' & '.join(
        f"{1000*sum(r['median_seconds'][a] for r in lcs_bounds['rows'] if r['name'] != 'gordian'):.3f}"
        for a in arms) + r' \\']
    gordian = next(r for r in lcs_bounds['rows'] if r['name'] == 'gordian')
    rows.append('Gordian, full query & ' + ' & '.join(
        f"{1000*gordian['median_seconds'][a]:.3f}" for a in arms) + r' \\')
    with open('tables/lcs_bounds_queries.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Scope & Before & A/A & Both changes', '@{}lrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds; all whole-knot queries complete.\n')
    rows = []
    for row in lcs_bounds['kernels']:
        cells = [row['family'].replace('-', ' ').capitalize(), str(row['bits'])]
        for arm in ('baseline', 'control', 'bounds-only', 'incremental-only', 'full'):
            samples = [s['measurements'][arm] for s in row['samples']]
            cells.append(f"{1000*median(s['seconds'] for s in samples):.3f}"
                         if all(s['status'] == 'COMPLETE' for s in samples) else 'limit')
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/lcs_bounds_kernels.tex', 'w') as handle:
        handle.write(r'\begin{center}\footnotesize' + '\n' +
            table('LCS family & $h$ & Before & A/A & Bounds & Incr. & Both', '@{}llrrrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds including construction. '
            'Bounds retains eager witness collection; Incr. retains ordinary length bounds. '
            'Limits are censored queries.\n')
        rows = []
        for row in lcs_bounds['moves']:
            cells = [str(row['bits'])]
            for arm in arms:
                samples = [s['measurements'][arm] for s in row['samples']]
                cells.append(f"{1000*median(s['seconds'] for s in samples):.3f}"
                             if all(s['status'] == 'COMPLETE' for s in samples) else 'limit')
            full = row['samples'][0]['measurements']['full']
            cells.extend(str(full[k]) for k in ('nodes',))
            cells.append(str(full['stats']['work']))
            rows.append(' & '.join(cells) + r' \\')
        handle.write(r'\begin{center}\small' + '\n' +
            table('Partial move, $h$ & Before & A/A & Both & Nodes & Work', '@{}rrrrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds including construction, failed whole-donor '
            'search, cyclic query and checked application. Nodes/work describe both changes.\n')

lcs_transitions = load('../fast/results/lcs_transitions_20261008.json')
if lcs_transitions:
    from statistics import median
    arms = ('baseline', 'control', 'full')
    rows = ['Small 14, summed medians & ' + ' & '.join(
        f"{1000*sum(r['median_seconds'][a] for r in lcs_transitions['rows'] if r['name'] != 'gordian'):.3f}"
        for a in arms) + r' \\']
    gordian = next(r for r in lcs_transitions['rows'] if r['name'] == 'gordian')
    rows.append('Gordian, full query & ' + ' & '.join(
        f"{1000*gordian['median_seconds'][a]:.3f}" for a in arms) + r' \\')
    with open('tables/lcs_transitions_queries.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Scope & Before & A/A & Transitions', '@{}lrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds; all full knot queries complete.\n')
    rows = []
    for row in lcs_transitions['kernels']:
        cells = [row['family'].replace('-', ' ').capitalize(), str(row['bits'])]
        for arm in arms:
            samples = [s['measurements'][arm] for s in row['samples']]
            cells.append(f"{1000*median(s['seconds'] for s in samples):.3f}"
                         if all(s['status'] == 'COMPLETE' for s in samples) else 'limit')
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/lcs_transitions_kernels.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('LCS family & $h$ & Before & A/A & Transitions', '@{}llrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds including construction; limits are censored.\n')
        rows = []
        for row in lcs_transitions['operations']:
            cells = [row['family'].capitalize(), str(row['bits'])]
            for arm in ('baseline', 'control', 'matcher-only', 'prune-only', 'full'):
                samples = [s['measurements'].get(arm) for s in row['samples']]
                cells.append('---' if samples[0] is None else
                    f"{1000*median(s['seconds'] for s in samples):.3f}"
                    if all(s['status'] == 'COMPLETE' for s in samples) else 'limit')
            rows.append(' & '.join(cells) + r' \\')
        handle.write(r'\begin{center}\footnotesize' + '\n' +
            table('Operation & $h$ & Before & A/A & Matcher & Pruning & Both', '@{}llrrrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds including construction. '
            'Both denotes the initial filter before the uniform-word shortcut. '
            'Partial operations do not produce knot verdicts.\n')

pair_shortcut = load('../fast/results/donor_pair_shortcut_20261008.json')
if pair_shortcut:
    from statistics import median
    rows = []
    for row in pair_shortcut['rows']:
        cells = [row['family'].capitalize(), str(row['bits'])]
        for arm in ('baseline', 'control', 'filtered', 'shortcut'):
            cells.append('---' if arm not in row['median_seconds'] else f"{1000*row['median_seconds'][arm]:.3f}")
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/donor_pair_shortcut.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Operation & $h$ & Before & A/A & Filter & Shortcut', '@{}llrrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds over 21 measured rounds. '
            'A/A repeats Before for Quotient and Filter for Partial. All operations complete with identical traces.\n')

lcs_windows = load('../fast/results/lcs_windows_20261008.json')
if lcs_windows:
    from statistics import median
    arms = ('baseline', 'control', 'full')
    rows = ['Small 14, summed medians & ' + ' & '.join(
        f"{1000*sum(r['median_seconds'][a] for r in lcs_windows['rows'] if r['name'] != 'gordian'):.3f}"
        for a in arms) + r' \\']
    gordian = next(r for r in lcs_windows['rows'] if r['name'] == 'gordian')
    rows.append('Gordian, full query & ' + ' & '.join(
        f"{1000*gordian['median_seconds'][a]:.3f}" for a in arms) + r' \\')
    with open('tables/lcs_windows_queries.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Scope & Before & A/A & Windows', '@{}lrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds; all full knot queries complete.\n')
    for key in ('kernels', 'operations'):
        rows = []
        for row in lcs_windows[key]:
            name = {'equal-bigrams-cyclic': 'Equal-pair cyclic',
                    'equal-bigrams': 'Equal pairs'}.get(row['family'], row['family'].replace('-', ' ').capitalize())
            cells = [name, str(row['bits'])]
            for arm in arms:
                samples = [s['measurements'][arm] for s in row['samples']]
                cells.append(f"{1000*median(s['seconds'] for s in samples):.3f}"
                             if all(s['status'] == 'COMPLETE' for s in samples) else 'limit')
            rows.append(' & '.join(cells) + r' \\')
        with open(f'tables/lcs_windows_{key}.tex', 'w') as handle:
            handle.write(r'\begin{center}\small' + '\n' +
                table('Family & $h$ & Before & A/A & Windows', '@{}llrrr@{}', rows) +
                r'\end{center}' + '\nMedian milliseconds including construction; limits are censored. '
                + ('Full overlap enumerates all lengths in compressed progressions, not all occurrences.\n'
                   if key == 'kernels' else 'Local operations do not produce knot verdicts.\n'))

lcs_periodic = load('../fast/results/lcs_periodic_20261008.json')
if lcs_periodic:
    from statistics import median
    arms = ('baseline', 'control', 'full')
    rows = ['Small 14, summed medians & ' + ' & '.join(
        f"{1000*sum(r['median_seconds'][a] for r in lcs_periodic['rows'] if r['name'] != 'gordian'):.3f}"
        for a in arms) + r' \\']
    gordian = next(r for r in lcs_periodic['rows'] if r['name'] == 'gordian')
    rows.append('Gordian, full query & ' + ' & '.join(
        f"{1000*gordian['median_seconds'][a]:.3f}" for a in arms) + r' \\')
    with open('tables/lcs_periodic_queries.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Scope & Before & A/A & Phases', '@{}lrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds; all full knot queries complete.\n')
    for key in ('kernels', 'operations'):
        rows = []
        for row in lcs_periodic[key]:
            name = {'equal-bigrams-cyclic': 'Equal-pair cyclic',
                    'equal-bigrams': 'Equal pairs', 'shifted-32': 'Shifted 32', 'late-defect': 'Late defect'}.get(row['family'], row['family'].replace('-', ' ').capitalize())
            cells = [name, str(row['bits'])]
            for arm in arms:
                samples = [s['measurements'][arm] for s in row['samples']]
                cells.append(f"{1000*median(s['seconds'] for s in samples):.3f}"
                             if all(s['status'] == 'COMPLETE' for s in samples) else 'limit')
            rows.append(' & '.join(cells) + r' \\')
        with open(f'tables/lcs_periodic_{key}.tex', 'w') as handle:
            handle.write(r'\begin{center}\small' + '\n' +
                table('Family & $h$ & Before & A/A & Phases', '@{}llrrr@{}', rows) +
                r'\end{center}' + '\nMedian milliseconds including construction; limits are censored. '
                + ('Full overlap enumerates all lengths in compressed progressions, not all occurrences.\n'
                   if key == 'kernels' else 'Local operations do not produce knot verdicts.\n'))

lcs_sparse = load('../fast/results/lcs_sparse_20261008.json')
if lcs_sparse:
    from statistics import median
    arms = ('baseline', 'control', 'full')
    rows = ['Small 14, summed medians & ' + ' & '.join(
        f"{1000*sum(r['median_seconds'][a] for r in lcs_sparse['rows'] if r['name'] != 'gordian'):.3f}"
        for a in arms) + r' \\']
    gordian = next(r for r in lcs_sparse['rows'] if r['name'] == 'gordian')
    rows.append('Gordian, full query & ' + ' & '.join(
        f"{1000*gordian['median_seconds'][a]:.3f}" for a in arms) + r' \\')
    with open('tables/lcs_sparse_queries.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Scope & Before & A/A & Endpoints', '@{}lrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds; all full knot queries complete.\n')
    for key in ('kernels', 'operations'):
        rows = []
        for row in lcs_sparse[key]:
            name = {'equal-bigrams-cyclic': 'Equal-pair cyclic',
                    'equal-bigrams': 'Equal pairs', 'shifted-32': 'Shifted 32', 'late-defect': 'Late defect'}.get(row['family'], row['family'].replace('-', ' ').capitalize())
            cells = [name, str(row['bits'])]
            for arm in arms:
                samples = [s['measurements'][arm] for s in row['samples']]
                cells.append(f"{1000*median(s['seconds'] for s in samples):.3f}"
                             if all(s['status'] == 'COMPLETE' for s in samples) else 'limit')
            rows.append(' & '.join(cells) + r' \\')
        with open(f'tables/lcs_sparse_{key}.tex', 'w') as handle:
            handle.write(r'\begin{center}\small' + '\n' +
                table('Family & $h$ & Before & A/A & Endpoints', '@{}llrrr@{}', rows) +
                r'\end{center}' + '\nMedian milliseconds including construction; limits are censored. '
                + ('Full overlap enumerates all lengths in compressed progressions, not all occurrences.\n'
                   if key == 'kernels' else 'Local operations do not produce knot verdicts.\n'))

lcs_endpoint = load('../fast/results/lcs_endpoint_progressions_20261008.json')
if lcs_endpoint:
    from statistics import median
    arms = ('baseline', 'control', 'full')
    rows = ['Small 14, summed medians & ' + ' & '.join(
        f"{1000*sum(r['median_seconds'][a] for r in lcs_endpoint['rows'] if r['name'] != 'gordian'):.3f}"
        for a in arms) + r' \\']
    gordian = next(r for r in lcs_endpoint['rows'] if r['name'] == 'gordian')
    rows.append('Gordian, full query & ' + ' & '.join(
        f"{1000*gordian['median_seconds'][a]:.3f}" for a in arms) + r' \\')
    with open('tables/lcs_endpoint_queries.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Scope & Before & A/A & Grid', '@{}lrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds; all full knot queries complete.\n')
    for key in ('kernels', 'operations'):
        rows = []
        for row in lcs_endpoint[key]:
            name = {'equal-bigrams-cyclic': 'Equal-pair cyclic',
                    'equal-bigrams': 'Equal pairs', 'shifted-32': 'Shifted 32', 'late-defect': 'Late defect'}.get(row['family'], row['family'].replace('-', ' ').capitalize())
            cells = [name, str(row['bits'])]
            for arm in arms:
                samples = [s['measurements'][arm] for s in row['samples']]
                cells.append(f"{1000*median(s['seconds'] for s in samples):.3f}"
                             if all(s['status'] == 'COMPLETE' for s in samples) else 'limit')
            rows.append(' & '.join(cells) + r' \\')
        with open(f'tables/lcs_endpoint_{key}.tex', 'w') as handle:
            handle.write(r'\begin{center}\small' + '\n' +
                table('Family & $h$ & Before & A/A & Grid', '@{}llrrr@{}', rows) +
                r'\end{center}' + '\nMedian milliseconds including construction; limits are censored. '
                + ('Full overlap enumerates all lengths in compressed progressions, not all occurrences.\n'
                   if key == 'kernels' else 'Local operations do not produce knot verdicts.\n'))

spin_integrated = load('../fast/results/spin_jones_integrated_20261008.json')
if spin_integrated:
    arms = ('potts', 'potts-control', 'spin', 'matched-potts', 'matched-spin')
    rows = []
    names = {'kinoshita_terasaka': 'KT', 'hard_unknot_8': 'Hard 8',
             'stress_braid5_36': 'Braid5 36', 'grid-8-shuffled': 'Grid 8 shuffled'}
    for row in spin_integrated['rows']:
        cells = [names.get(row['name'], row['name'].replace('-', ' ').capitalize()),
                 str(row['crossings'])]
        for arm in arms:
            cells.append(f"{1000*row['median_seconds'][arm]:.3f}"
                         if row['complete_queries'][arm] == spin_integrated['rounds'] else 'limit')
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/spin_integrated.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Input & $n$ & Potts & A/A & Spin & Fixed P & Fixed S', '@{}llrrrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds for full Jones queries. '
            'Fixed P/S share an externally prepared order; other columns include ordering. '
            'Limits are censored, not completed-query times.\n')

tensor_candidates = load('../fast/results/tensor_candidates_20261008.json')
if tensor_candidates:
    rows = []
    arms = ('spin', 'spin-control', 'valuation', 'global-shift')
    for row in tensor_candidates['rows']:
        cells = [row['name'].replace('-', ' ').capitalize()]
        for arm in arms:
            cells.append(f"{1000*row['median_seconds'][arm]:.3f}"
                if all(s['measurements'][arm]['status'] == 'COMPLETE' for s in row['samples']) else 'limit')
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/tensor_candidates.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Input & Spin & A/A & Valuation & Global shift', '@{}lrrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds on a common prepared order. '
            'The last two arms load the delivered research module directly.\n')

spin_valuation = load('../fast/results/spin_valuation_20261008.json')
if spin_valuation:
    arms = ('baseline', 'control', 'shifted', 'valuation', 'potts')
    rows = []
    names = {'kinoshita_terasaka': 'KT', 'hard_unknot_8': 'Hard 8',
             'stress_braid5_36': 'Braid5 36', 'grid-8-shuffled': 'Grid 8 shuffled'}
    for row in spin_valuation['rows']:
        cells = [names.get(row['name'], row['name'].replace('-', ' ').capitalize())]
        for arm in arms:
            cells.append(f"{1000*row['median_seconds'][arm]:.3f}"
                         if row['completed'][arm] == spin_valuation['rounds'] else 'limit')
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/spin_valuation.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Input & Before & A/A & Shifted & Valuation & Potts', '@{}lrrrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds for fresh full Jones queries, including ordering. '
            'Current shifted arithmetic controls for the new dispatch and counters. '
            'Limits are censored.\n')

adaptive_jones = load('../fast/results/adaptive_jones_20261008.json')
if adaptive_jones:
    arms = ('baseline', 'control', 'spin', 'adaptive')
    rows = []
    names = {'kinoshita_terasaka': 'KT', 'hard_unknot_8': 'Hard 8',
             'stress_braid5_36': 'Braid5 36', 'grid-8-shuffled': 'Grid 8 shuffled'}
    for row in adaptive_jones['rows']:
        cells = [esc(names.get(row['name'], row['name'].replace('-', ' ').capitalize()))]
        for arm in arms:
            cells.append(f"{1000*row['median_seconds'][arm]:.3f}"
                         if row['completed'][arm] == adaptive_jones['rounds'] else 'limit')
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/adaptive_jones.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' +
            table('Input & Potts & A/A & Spin & Adaptive', '@{}lrrrr@{}', rows) +
            r'\end{center}' + '\nMedian milliseconds for fresh full Jones queries, including ordering. '
            'Limits are censored, not completed-query times.\n')

primary_continuation = load('../fast/results/primary_continuation_20261008.json')
if primary_continuation:
    arms = ('fitting', 'control', 'delivered', 'primary', 'corner')
    for scope in ('knots', 'compression'):
        rows = []
        items = primary_continuation['knots' if scope == 'knots' else 'fields']
        for row in items:
            if scope == 'knots':
                name = {'kinoshita_terasaka': 'KT', 'hard_unknot_8': 'Hard 8',
                        'stress_braid5_36': 'Braid5 36', 'torus_3_5': 'Torus (3,5)'}.get(row['name'],row['name'].capitalize())
                timing = row['timing']
            else:
                name = str(row['degree'])+' '+row['mixing']
                timing = row['compression']['timing']
            rows.append(' & '.join([esc(name)] +
                [f"{1000*timing['median_seconds'][arm]:.3f}" for arm in arms]) + r' \\')
        with open(f'tables/primary_{scope}.tex', 'w') as handle:
            handle.write(r'\begin{center}\small'+'\n'+
                table('Input & Fitting & A/A & Delivered & Local stop & Corner', '@{}lrrrrr@{}', rows)+
                r'\end{center}'+'\nMedian milliseconds; all calls complete. '+
                ('Full raw knot scans at a common prepared order.\n' if scope=='knots' else
                 'Complete recursive compression of graded algebraic fixtures; construction excluded.\n'))

two_meridian = load('../fast/results/two_meridian_20261008.json')
if two_meridian:
    rows = []
    names = {'kinoshita_terasaka': 'KT', 'hard_unknot_8': 'Hard 8',
             'figure_eight': 'Figure eight'}
    for row in two_meridian['rows']:
        cells = [esc(names.get(row['name'], row['name'].replace('-', ' ').capitalize())),
                 str(row['crossings'])]
        for mode in ('ordinary', 'compressed_group'):
            result = row['modes'][mode]
            for arm in ('disabled', 'enabled'):
                times = result['completed_median_seconds'][arm]
                count = sum(s['measurements'][arm]['completed'] for s in result['samples'])
                cells.append(f'{1000*times:.2f}' if count == two_meridian['measured_rounds'] else 'limit')
            pair = result['paired_ratios']['disabled/enabled']
            cells.append(f"{pair['median']:.2f}" if pair['count'] == two_meridian['measured_rounds'] else '--')
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/two_meridian.tex', 'w') as handle:
        handle.write(r'\begin{center}\small'+'\n'+
            table('Input & $n$ & Ord. off & Ord. on & Ratio & Group off & Group on & Ratio',
                  '@{}lrrrrrrr@{}', rows)+r'\end{center}'+'\n'+
            'Median milliseconds for whole recognition, including PD validation and replay. '
            'Ratios are medians of paired off/on times; limits are censored.\n')

endpoint_clipping = load('../fast/results/endpoint_clipping_20261008.json')
if endpoint_clipping:
    names = {'marker-power':'Marker control', 'bigram-power':'Dense bigram',
        'fourgram-power':'Dense fourgram', 'nonperiodic-target':'One rejected',
        'partial-half':'Half rejected', 'period-reject':'Period rejected',
        'full-overlap-control':'Short-period control', 'sparse-17-control':'Sparse control',
        'lcs-phase':'Phased LCS', 'relator-phase':'Phased relator', 'quotient-control':'Quotient control'}
    for scope in ('kernels','operations','rows'):
        rows=[]
        for item in endpoint_clipping[scope]:
            if scope=='rows':
                cells=[esc(item['name'].replace('-', ' ').capitalize())]
            else:
                cells=[names[item['family']],str(item['bits'])]
            for arm in ('baseline','control','clipping'):
                c=item['completed_medians'][arm]
                cells.append(f"{1000*c['seconds']:.3f}" if c['count']==endpoint_clipping['rounds'] else 'limit')
            pair=item['paired_ratios']['baseline/clipping']
            cells.append(f"{pair['median']:.2f}" if pair['count']==endpoint_clipping['rounds'] else '--')
            rows.append(' & '.join(cells)+r' \\')
        with open(f'tables/endpoint_clipping_{scope}.tex','w') as handle:
            handle.write(r'\begin{center}\small'+'\n'+table(
                ('Input' if scope=='rows' else 'Family & Bits')+' & Before & A/A & Clipping & Ratio',
                '@{}lrrrr@{}' if scope=='rows' else '@{}lrrrrr@{}',rows)+r'\end{center}'+'\n'+
                'Median milliseconds; ratios are medians of complete paired before/clipping times. '
                'Censored runs are shown as limits and excluded from ratios.\n')

braid_descent = load('../fast/results/braid_descent_20261008.json')
if braid_descent:
    rows=[]
    for item in braid_descent['summary']:
        cells=[esc(item['case'])]
        cells.extend(f"{1000*item['median_seconds'][arm]:.3f}" for arm in ('baseline','control','adaptive'))
        cells.append(f"{item['paired_ratios']['adaptive']:.2f}" if item['complete'] else '--')
        rows.append(' & '.join(cells)+r' \\')
    with open('tables/braid_descent.tex','w') as handle:
        handle.write(r'\begin{center}\small'+'\n'+table(
            'Case & Before & A/A & Adaptive & Ratio','@{}lrrrr@{}',rows)+r'\end{center}'+'\n'+
            'Median milliseconds; ratios are medians of paired before/adaptive times.\n')

overlap_bounds = load('../fast/results/overlap_bounds_20261008.json')
if overlap_bounds:
    names = {'repeated_16x128': 'Repeated 16 by 128',
             'repeated_128x128': 'Repeated 128 by 128',
             'disjoint_16x128': 'Disjoint 16 by 128',
             'later_longer': 'Later longer donor',
             'native_explicit': 'Gordian explicit',
             'native_exposure_overlap': 'Gordian exposure handoff'}
    rows=[]
    for name, arms in overlap_bounds['summary'].items():
        cells=[names[name]]
        cells.extend(f"{1000*arms[arm]['median_seconds']:.3f}" for arm in ('baseline','control','pruned'))
        cells.append(f"{arms['pruned']['paired_baseline_ratio']:.2f}")
        rows.append(' & '.join(cells)+r' \\')
    with open('tables/overlap_bounds.tex','w') as handle:
        handle.write(r'\begin{center}\small'+'\n'+table(
            'Query or complete search & Before & A/A & Pruned & Ratio','@{}lrrrr@{}',rows)+r'\end{center}'+'\n'+
            'Median milliseconds; ratios are medians of paired before/pruned times. '
            'Native rows include two independent full certificate replays.\n')

dynamic_terminal = load('../fast/results/dynamic_terminal_20261008.json')
if dynamic_terminal:
    rows=[]
    cases=('native_all','native_widest','native_many_queries','native_singular')
    names={'rational':'Rational','control':'Identical control','integer':'Integer quotient',
           'static':'Static modular','static_cached':'Cached static modular',
           'dynamic':'Delivered dynamic','pruned':'Pruned field traversal'}
    for arm,name in names.items():
        cells=[name]
        cells.extend(f"{1000*dynamic_terminal['summary'][case]['arms'][arm]['median_seconds']:.3f}" for case in cases)
        cells.append(f"{dynamic_terminal['summary']['native_all']['arms'][arm]['paired_rational_ratio']:.2f}")
        rows.append(' & '.join(cells)+r' \\')
    with open('tables/dynamic_terminal.tex','w') as handle:
        handle.write(r'\begin{center}\small'+'\n'+table(
            'Observer & All stages & Widest & Most queries & Singular & Ratio',
            '@{}lrrrrr@{}',rows)+r'\end{center}'+'\n'+
            'Median milliseconds per fresh replay; the final column is the median paired '
            'rational/arm ratio for all 582 stages. These are observer timings.\n')

integer_terminal = load('../fast/results/integer_terminal_20261008.json')
if integer_terminal:
    rows=[]
    names={'native_all':'Native corpus','padding_4_one':'17 vertices, one',
           'padding_4_all':'17 vertices, stream','padding_16_one':'41 vertices, one',
           'padding_16_all':'41 vertices, stream','padding_32_one':'73 vertices, one',
           'padding_32_all':'73 vertices, stream','padding_32_repeated':'73 vertices, repeats'}
    for name,arms in integer_terminal['summary'].items():
        cells=[names[name]]
        cells.extend(f"{1000*arms[arm]['median_seconds']:.3f}" for arm in
                     ('rational','control','direct','integer_kernel','adaptive_four'))
        cells.append(f"{arms['integer_kernel']['paired_rational_ratio']:.2f}")
        rows.append(' & '.join(cells)+r' \\')
    with open('tables/integer_terminal.tex','w') as handle:
        handle.write(r'\begin{center}\small'+'\n'+table(
            'Stage & Rational & A/A & Direct & Kernel & Switch & Ratio','@{}lrrrrrr@{}',rows)+
            r'\end{center}'+'\n'+'Median milliseconds; final column is the median paired '
            'rational/integer-kernel ratio. These are complete observer-stage timings.\n')

orbit_controls = load('../fast/results/orbits_20261008.json')
if orbit_controls:
    rows = []
    selected = [(f"Chain, {r['pairings']} pairings", r)
                for r in orbit_controls['intervals']
                if r['family'] == 'adjacent_periodic_chain']
    selected += [(f"Meridian, {r['tetrahedra']} tetrahedra", r)
                 for r in orbit_controls['surfaces']
                 if r['scale_bits'] == 1 and r['tetrahedra'] in (4, 32, 128)]
    selected += [(r'$2^{2000}$ parallel discs', r)
                 for r in orbit_controls['surfaces'] if r['scale_bits'] == 2001]
    for label, row in selected:
        cells = [label]
        cells.extend(f"{1000 * row['medians'][arm]:.3f}"
                     for arm in ('aht', 'fine_wilf', 'fine_wilf_AA'))
        cells.append(f"{row['paired_speedup']:.3f}")
        cells.append(str(row['outputs']['aht']['cycles']) + '/' +
                     str(row['outputs']['fine_wilf']['cycles']))
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/interval_orbits.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' + table(
            'Query & Classical & Sharp & A/A & Ratio & Cycles',
            '@{}lrrrrr@{}', rows) + r'\end{center}' + '\n' +
            'Median milliseconds; ratio is the median paired classical/sharp '
            'time. Cycles are classical/sharp. Surface queries include validation '
            'and all three orbit counts; chain queries count interval orbits only.\n')

orbit_proofs = load('../fast/results/orbit_certificates_20261008.json')
if orbit_proofs:
    rows = []
    for row in orbit_proofs['incidence']:
        family, shape = row['name'].split('_', 1)
        cells = [{'static': 'Static', 'normal8': 'Meridian',
                  'parallel500': 'Parallel'}[family] + ', ' + shape]
        cells.extend(f"{1000*row['medians'][arm]:.2f}" for arm in
                     ('uncached', 'cached', 'certified'))
        cells.append(f"{row['paired_ratio']['cached']:.2f}")
        cells.append(str(row['old_queries']) + '/' + str(row['stats']['orbit_queries']))
        rows.append(' & '.join(cells) + r' \\')
    with open('tables/orbit_certificates.tex', 'w') as handle:
        handle.write(r'\begin{center}\small' + '\n' + table(
            'Marked system & Fresh & Reuse & Certified & Ratio & Queries',
            '@{}lrrrrr@{}', rows) + r'\end{center}' + '\n' +
            'Median milliseconds per complete incidence query. Certified includes '
            'proof construction and independent replay; ratio is the median paired '
            'fresh/reuse time. Queries are fresh/reuse.\n')

# Native compressed braid discovery includes independent replay.
cb = load('../fast/results/compressed_braid_20261008.json')
if cb:
    rows = []
    selected = {'sleeve_0_0', 'sleeve_8_0', 'sleeve_12_0', 'sleeve_16_0',
                'sleeve_16_1', 'sleeve_4096_0', 'explicit_random_500', 'forest_16'}
    for r in cb['cases']:
        if r['name'] not in selected:
            continue
        explicit = r['medians'].get('explicit')
        old = '--' if explicit is None else f'{1000*explicit:.3f}'
        ratio = '--' if explicit is None else f"{r['paired_ratios']['native']:.3f}"
        rows.append(f"{esc(r['name'])} & {r['rules']} & {old} & "
                    f"{1000*r['medians']['native']:.3f} & {ratio} \\\\")
    open('tables/compressed_braid.tex', 'w').write(
        '\\begin{center}\n' + table('Input & rules & explicit ms & native ms & paired ratio',
                                    '@{}lrrrr@{}', rows) + '\\end{center}\n')

# Complete exceptional-factor fallback: same proof-producing cube with/without cuts.
ec = load('../fast/results/exceptional_cube_20261008.json')
if ec:
    rows = []
    for r in ec['cases']:
        old = r['medians'].get('whole')
        old_cell = '--' if old is None else f'{1000*old:.2f}'
        ratio = '--' if old is None else f"{r['paired_ratios']['hybrid']:.3f}"
        rows.append(f"{esc(r['name'])} & {old_cell} & {1000*r['medians']['hybrid']:.2f} & "
                    f"{ratio} & {r['resources']['cube_generators']} \\\\")
    open('tables/exceptional_cube.tex', 'w').write(
        '\\begin{center}\n' + table('Input & whole ms & hybrid ms & paired ratio & generators',
                                    '@{}lrrrr@{}', rows) + '\\end{center}\n')

# Adaptive forest scheduling and checked pre-cube reduction, actual pinned host.
af = load('../fast/results/adaptive_forest_20261008.json')
if af:
    rows = []
    for r in af['cases']:
        rows.append(f"{esc(r['name'])} & {1000*r['medians']['old']:.2f} & "
                    f"{1000*r['medians']['current']:.2f} & "
                    f"{1000*r['medians']['no_reduction']:.2f} & "
                    f"{r['paired_ratios']['current']:.3f} \\\\")
    open('tables/adaptive_forest.tex','w').write(
        '\\begin{center}\n' + table('Input & old ms & current ms & no reduction ms & paired ratio',
                                    '@{}lrrrr@{}', rows) + '\\end{center}\n')

# Report-47 seed search rerun on the maintained pipeline.
ss = load('../fast/results/two_meridian_search_native_20261008.json')
if ss:
    selected = {'survivor-00','survivor-01','survivor-04','survivor-09',
                'gordian','conway','kinoshita_terasaka','trefoil'}
    rows = []
    def seed_ms(value):
        return '--' if value is None else f'{1000*value:.3f}'
    def seed_ratio(value):
        return '--' if value is None else f'{value:.3f}'
    for r in ss['rows']:
        if r['name'] not in selected:
            continue
        s = r['standalone']; m = s['completed_median_seconds']
        rows.append(f"{esc(r['name'])} & {seed_ms(m['baseline'])} & {seed_ms(m['stamped'])} & "
                    f"{seed_ms(m['candidate_only'])} & {seed_ms(m['optimized'])} & "
                    + seed_ratio(s['paired_ratios']['baseline/optimized']['median']) + r' \\')
    open('tables/sparse_seeds.tex','w').write('\\begin{center}\n'+
        table('Input & old ms & stamped ms & pairs ms & full ms & ratio','@{}lrrrrr@{}',rows)+'\\end{center}\n')
    rows = []
    for r in ss['rows']:
        if r['name'] not in selected:
            continue
        cells = [esc(r['name'])]
        for mode in ('ordinary','compressed_group'):
            s = r['pipeline'][mode]; m = s['completed_median_seconds']
            cells += [seed_ms(m['baseline'])+'/'+seed_ms(m['optimized']),
                      seed_ratio(s['paired_ratios']['baseline/optimized']['median'])]
        rows.append(' & '.join(cells)+r' \\')
    open('tables/sparse_seeds_pipeline.tex','w').write('\\begin{center}\n'+
        table('Input & ordinary old/new ms & ratio & group old/new ms & ratio','@{}lrrrr@{}',rows)+'\\end{center}\n')

# Native supplied-normal-vector certificates: distinguish discovery and replay.
nc = load('../fast/results/normal_certificates_20261008.json')
if nc:
    rows = []
    for r in nc['cases']:
        m = r['medians']
        rows.append(esc(r['name']) + ' & ' + ' & '.join(
            f'{1000*m[arm]:.3f}' for arm in ('current', 'record', 'certified', 'replay'))
            + f" & {r['current_over']['replay']:.3f}" + r' \\')
    open('tables/normal_certificates.tex', 'w').write('\\begin{center}\n' + table(
        'Input & count ms & record ms & both ms & replay ms & ratio',
        '@{}lrrrrr@{}', rows) + '\\end{center}\n')

# Common coordinate multiplicity: complete topology calls and complete proof arms.
nm = load('../fast/results/normal_multiplicity_20261008.json')
if nm:
    rows = []
    for r in nm['cases']:
        m = r['medians']; q = r['paired_ratios']
        rows.append(esc(r['name']) + ' & ' + ' & '.join(
            f'{1000*m[arm]:.3f}' for arm in ('old', 'current'))
            + f" & {q['count']:.3f} & {q['certified']:.3f} & "
            + f"{r['old_proof_bytes']}/{r['new_proof_bytes']}" + r' \\')
    open('tables/normal_multiplicity.tex', 'w').write('\\begin{center}\\small\n' + table(
        'Input & old ms & new ms & count ratio & proof ratio & proof bytes old/new',
        '@{}lrrrrr@{}', rows) + '\\end{center}\n')

# Lazy projection within the complete source-bound compressed-braid recognizer.
lf = load('../fast/results/lazy_forest_20261008.json')
if lf:
    rows = []
    for r in lf['cases']:
        m = r['medians']
        rows.append(esc(r['name'])+' & '+' & '.join(
            f'{1000*m[a]:.3f}' for a in ('old','current','eager'))
            +f" & {r['paired_ratios']['current']:.3f} & "
            +f"{len(r['old_projection_calls'])}/{len(r['new_projection_calls'])}"+r' \\')
    open('tables/lazy_forest.tex','w').write('\\begin{center}\\small\n'+table(
        'Input & old ms & lazy ms & eager ms & ratio & projections old/new',
        '@{}lrrrrr@{}',rows)+'\\end{center}\n')

# Compact live permutations: full recognition and independently measured memory.
cp = load('../fast/results/compact_permutations_20261008.json')
if cp:
    rows = []
    for r in cp['cases']:
        m = r['medians']; memory = r['root_summary_peak_traced_bytes']
        rows.append(esc(r['name'])+' & '+' & '.join(
            f'{1000*m[a]:.3f}' for a in ('old','current','live_dense'))
            +f" & {r['paired_ratios']['current']:.3f} & "
            +f"{memory['old']/1024:.1f}/{memory['current']/1024:.1f}"+r' \\')
    open('tables/compact_permutations.tex','w').write('\\begin{center}\\small\n'+table(
        'Input & old ms & new ms & dense ms & ratio & peak KiB old/new',
        '@{}lrrrrr@{}',rows)+'\\end{center}\n')

# Report-46 shared overlap rebased onto maintained donor pruning.
jo = load('../fast/results/joint_overlap_kernels_20261008.json')
if jo:
    rows = []
    names = {'gordian-derived':'Gordian residual','random-8x64':r'random $8\times64$',
             'random-32x64':r'random $32\times64$','random-128x64':r'random $128\times64$',
             'duplicate-periodic':'periodic duplicates','duplicate-native-cutoff':'full-donor duplicates',
             'many-empty-slots':'many empty slots'}
    for r in jo['rows']:
        rows.append(names[r['name']]+' & '+' & '.join(f"{1000*r['medians'][a]:.3f}"
            for a in ('old','current','report','joint'))
            +f" & {r['paired_ratios']['current']['median']:.3f}"+r' \\')
    open('tables/joint_overlap_kernels.tex','w').write('\\begin{center}\\small\n'+table(
        'Query & old ms & native ms & report ms & joint ms & ratio',
        '@{}lrrrrr@{}',rows)+'\\end{center}\n')
jp = load('../fast/results/joint_overlap_pipeline_20261008.json')
if jp:
    rows = []
    selected = {'survivor-00','mirror-03','mirror-08','gordian','trefoil','conway','kinoshita_terasaka'}
    for r in jp['rows']:
        if r['name'] not in selected:
            continue
        cells = [esc(r['name'])]
        for mode in ('explicit','compressed'):
            v = r['modes'][mode]; m = v['medians']
            times = '/'.join('--' if m[a] is None else f'{1000*m[a]:.3f}'
                             for a in ('old','current'))
            ratio = v['paired_ratios']['current']['median']
            cells += [times, '--' if ratio is None else f'{ratio:.3f}']
        rows.append(' & '.join(cells)+r' \\')
    open('tables/joint_overlap_pipeline.tex','w').write('\\begin{center}\\small\n'+table(
        'Input & explicit old/new ms & ratio & compressed old/new ms & ratio',
        '@{}lrrrr@{}',rows)+'\\end{center}\n')

nb = load('../fast/results/normal_boundary_20261008.json')
if nb:
    rows = []
    names = {'parallel5000':'parallel 5000', 'pure_orientable':'pure orientable',
             'one_boundary':'one boundary', 'mixed_odd':'mixed odd',
             'mixed_even':'mixed even', 'mixed_even5000':'even 5000',
             'mixed_odd5000':'odd 5000', 'closed_one_sided':'closed one-sided'}
    for r in nb['cases']:
        m, q = r['medians'], r['paired_ratios']
        cells = [esc(names.get(r['name'],r['name'])),
                 f"{len(r['direct']['queries'])}/{len(r['adaptive']['queries'])}",
                 f"{1000*m['direct']:.3f}",f"{1000*m['adaptive']:.3f}",
                 f"{q['count']:.3f}",f"{q['certified']:.3f}"]
        rows.append(' & '.join(cells)+r' \\')
    open('tables/normal_boundary.tex','w').write('\\begin{center}\\small\n'+table(
        'Input & queries D/A & direct ms & adaptive ms & count ratio & proof ratio',
        '@{}lrrrrr@{}',rows)+'\\end{center}\n')

pp = load('../fast/results/primitive_power_pipeline_20261008.json')
if pp:
    rows=[]
    selected={'survivor-00','survivor-02','survivor-11','mirror-03','mirror-08','gordian','trefoil','conway','kinoshita_terasaka'}
    for r in pp['cases']:
        if r['source']['name'] not in selected: continue
        m=r['medians'];q=r['paired_ratios']
        cells=[esc(r['source']['name'])]+['--' if m[a] is None else f'{1000*m[a]:.3f}' for a in ('old','current')]
        cells += ['--' if q[a]['median'] is None else f"{q[a]['median']:.3f}" for a in ('current','old_AA','current_AA')]
        rows.append(' & '.join(cells)+r' \\')
    open('tables/primitive_power.tex','w').write('\\begin{center}\\small\n'+table(
        'Input & old ms & new ms & ratio & old A/A & new A/A',
        '@{}lrrrrr@{}',rows)+'\\end{center}\n')

pj = load('../fast/results/primitive_projection_pipeline_20261008.json')
if pj:
    rows=[]
    selected={'survivor-00','survivor-06','survivor-08','mirror-03','gordian','trefoil','conway'}
    for r in pj['cases']:
        if r['source']['name'] not in selected: continue
        m=r['medians'];q=r['paired_ratios']
        cells=[esc(r['source']['name'])]+['--' if m[a] is None else f'{1000*m[a]:.3f}' for a in ('old','projection')]
        cells += ['--' if q[a]['median'] is None else f"{q[a]['median']:.3f}" for a in ('projection','old_AA','projection_AA')]
        rows.append(' & '.join(cells)+r' \\')
    open('tables/primitive_projection.tex','w').write('\\begin{center}\\small\n'+table(
        'Input & old ms & projection ms & ratio & old A/A & proj. A/A',
        '@{}lrrrrr@{}',rows)+'\\end{center}\n')

pf = load('../fast/results/primitive_forest_audit_20261008.json')
if pf:
    rows=[]
    for r in pf['capacity']['cases']:
        old,new=(r['modes'][k] for k in ('old_projection','forest'))
        cells=[f"{esc(r['shape'])} {r['rank']}",f"{old['rounds']}/{new['rounds']}",
            f"{old['stats']['work']:,}/{new['stats']['work']:,}",f"{old['final_nodes']:,}/{new['final_nodes']:,}"]
        rows.append(' & '.join(cells)+r' \\')
    open('tables/primitive_forest_capacity.tex','w').write('\\begin{center}\\small\n'+table(
        'Family & rounds pair/forest & search work pair/forest & nodes pair/forest',
        '@{}lrrr@{}',rows)+'\\end{center}\n')

pf = load('../fast/results/primitive_forest_pipeline_20261008.json')
if pf:
    rows=[]
    selected={'survivor-00','survivor-06','survivor-08','mirror-03','gordian','trefoil','conway'}
    for r in pf['cases']:
        if r['source']['name'] not in selected:continue
        m,q=r['medians'],r['paired_ratios']
        cells=[esc(r['source']['name'])]+['--' if m[a] is None else f'{1000*m[a]:.3f}' for a in ('old','old_projection','forest')]
        cells+=['--' if q[a]['median'] is None else f"{q[a]['median']:.3f}" for a in ('forest','versus_projection')]
        rows.append(' & '.join(cells)+r' \\')
    open('tables/primitive_forest_pipeline.tex','w').write('\\begin{center}\\small\n'+table(
        'Input & old ms & pair ms & forest ms & old/forest & pair/forest',
        '@{}lrrrrr@{}',rows)+'\\end{center}\n')

pf = load('../fast/results/primitive_forest_stages_20261008.json')
if pf:
    rows=[]
    for r in pf['cases']:
        m,q=r['medians'],r['paired_ratios']
        cells=[str(r['rank'])]+['--' if m[a] is None else f'{1000*m[a]:.3f}' for a in ('old','projection','forest')]
        cells+=['--' if q[a]['median'] is None else f"{q[a]['median']:.3f}" for a in ('forest','versus_projection')]
        rows.append(' & '.join(cells)+r' \\')
    open('tables/primitive_forest_stages.tex','w').write('\\begin{center}\\small\n'+table(
        'Crossings & old ms & pair ms & forest ms & old/forest & pair/forest',
        '@{}rrrrrr@{}',rows)+'\\end{center}\n')

for planner_mode in ('pipeline','stages'):
    pp = load(f'../fast/results/primitive_planner_{planner_mode}_20261008.json')
    if not pp:continue
    rows=[]
    selected={'survivor-00','survivor-06','survivor-08','mirror-03','gordian','trefoil','conway'}
    for r in pp['cases']:
        if planner_mode=='pipeline' and r['source']['name'] not in selected:continue
        m,q=r['medians'],r['paired_ratios']
        cells=[esc(r['source']['name']) if planner_mode=='pipeline' else str(r['source']['crossings'])]
        for mode in ('projection','forest'):
            cells.append('/'.join('--' if m[a] is None else f'{1000*m[a]:.3f}' for a in ('old_'+mode,mode)))
            cells.append('--' if q[mode]['median'] is None else f"{q[mode]['median']:.3f}")
        rows.append(' & '.join(cells)+r' \\')
    first='Input' if planner_mode=='pipeline' else 'Crossings'
    open(f'tables/primitive_planner_{planner_mode}.tex','w').write('\\begin{center}\\small\n'+table(
        first+' & pair old/new ms & ratio & forest old/new ms & ratio',
        '@{}lrrrr@{}',rows)+'\\end{center}\n')

def normalization_tables(prefix):
    for syllable_mode in ('pipeline','stages'):
        data = load(f'../fast/results/{prefix}_{syllable_mode}_20261008.json')
        if not data:continue
        rows=[]
        for r in data['cases']:
            m,q=r['medians'],r['paired_ratios']
            cells=[esc(r['source']['name']) if syllable_mode=='pipeline' else str(r['source']['crossings'])]
            for mode in ('projection','forest'):
                cells.append('/'.join('--' if m[a] is None else f'{1000*m[a]:.3f}' for a in ('old_'+mode,mode)))
                cells.append('--' if q[mode]['median'] is None else f"{q[mode]['median']:.3f}")
            rows.append(' & '.join(cells)+r' \\')
        first='Input' if syllable_mode=='pipeline' else 'Crossings'
        open(f'tables/{prefix}_{syllable_mode}.tex','w').write('\\begin{center}\\small\n'+table(
            first+' & pair old/new ms & ratio & forest old/new ms & ratio',
            '@{}lrrrr@{}',rows)+'\\end{center}\n')

    data = load(f'../fast/results/{prefix}_kernels_20261008.json')
    if data:
        rows=[]
        for r in data['cases']:
            m,q=r['medians'],r['paired_ratios']
            cells=[esc(r['kind']),str(r['bits'])]+['--' if m[a] is None else f'{1000*m[a]:.3f}' for a in ('old','current')]
            cells+=['--' if q[a]['median'] is None else f"{q[a]['median']:.3f}" for a in ('current','old_AA','current_AA')]
            rows.append(' & '.join(cells)+r' \\')
        open(f'tables/{prefix}_kernels.tex','w').write('\\begin{center}\\small\n'+table(
            'Case & bits & old ms & new ms & ratio & old A/A & new A/A',
            '@{}lrrrrrr@{}',rows)+'\\end{center}\n')


for normalization_prefix in ('syllable_normalization','syllable_frontier'):
    normalization_tables(normalization_prefix)

for elimination_mode in ('pipeline','stages'):
    data=load(f'../fast/results/elimination_batch_{elimination_mode}_20261008.json')
    if not data:continue
    rows=[]
    for r in data['cases']:
        m,q=r['medians'],r['paired_ratios']
        cells=[esc(r['source']['name']) if elimination_mode=='pipeline' else str(r['source']['crossings'])]
        arms=('old','current','portfolio') if elimination_mode=='pipeline' else ('old','old_forest','direct','portfolio')
        cells+=['--' if m[a] is None else f'{1000*m[a]:.3f}' for a in arms]
        ratios=('portfolio',) if elimination_mode=='pipeline' else ('direct','portfolio')
        cells+=['--' if q[a]['median'] is None else f"{q[a]['median']:.3f}" for a in ratios]
        rows.append(' & '.join(cells)+r' \\')
    heading=('Input & old ms & default ms & portfolio ms & old/portfolio' if elimination_mode=='pipeline' else
        'Crossings & old ms & forest ms & direct ms & portfolio ms & old/direct & old/port.')
    open(f'tables/elimination_batch_{elimination_mode}.tex','w').write('\\begin{center}\\small\n'+table(heading,'@{}l'+('r'* (len(arms)+len(ratios)))+'@{}',rows)+'\\end{center}\n')


for reach_mode in ('pipeline','stages'):
    data=load(f'../fast/results/elimination_reach_{reach_mode}_20261008.json')
    if not data:continue
    rows=[]
    for r in data['cases']:
        m,q=r['medians'],r['paired_ratios']
        cells=[esc(r['source']['name']) if reach_mode=='pipeline' else str(r['source']['crossings'])]
        if reach_mode=='pipeline':
            cells+=['--' if m[a] is None else f'{1000*m[a]:.3f}' for a in ('current','old_portfolio','portfolio')]
            cells+=['--' if q[a]['median'] is None else f"{q[a]['median']:.3f}" for a in ('portfolio','versus_default')]
        else:
            for mode,old in (('direct','old_direct'),('portfolio','old_portfolio')):
                cells.append('/'.join('--' if m[a] is None else f'{1000*m[a]:.3f}' for a in (old,mode)))
                cells.append('--' if q[mode]['median'] is None else f"{q[mode]['median']:.3f}")
        rows.append(' & '.join(cells)+r' \\')
    heading=('Input & default ms & old port. ms & new port. ms & old/new & default/new' if reach_mode=='pipeline' else
        'Crossings & direct old/new ms & ratio & portfolio old/new ms & ratio')
    open(f'tables/elimination_reach_{reach_mode}.tex','w').write('\\begin{center}\\small\n'+table(heading,'@{}l'+('r'* (5 if reach_mode=='pipeline' else 4))+'@{}',rows)+'\\end{center}\n')


for word_mode in ('pipeline','kernels'):
    data=load(f'../fast/results/word_cache_frontier_{word_mode}_20261008.json')
    if not data:continue
    rows=[]
    for r in data['cases']:
        m,q=r['medians'],r['paired_ratios']
        if word_mode=='pipeline':
            cells=[esc(r['source']['name'])]
            for old,new,key in (('old','current','current'),('old_portfolio','portfolio','portfolio')):
                cells.append('/'.join('--' if m[a] is None else f'{1000*m[a]:.3f}' for a in (old,new)))
                cells.append('--' if q[key]['median'] is None else f"{q[key]['median']:.3f}")
        else:
            cells=[esc(r['kind']),str(r['size'])]+['--' if m[a] is None else f'{1000*m[a]:.3f}' for a in ('old','current')]
            cells+=['--' if q['current']['median'] is None else f"{q['current']['median']:.3f}"]
            cells+=['/'.join('--' if q[a]['median'] is None else f"{q[a]['median']:.3f}" for a in ('old_AA','current_AA'))]
        rows.append(' & '.join(cells)+r' \\')
    heading=('Input & default old/new ms & ratio & portfolio old/new ms & ratio' if word_mode=='pipeline' else
        'Family & size & old ms & new ms & ratio & old/new A/A')
    open(f'tables/word_cache_frontier_{word_mode}.tex','w').write('\\begin{center}\\small\n'+table(heading,'@{}l'+('r'* (4 if word_mode=='pipeline' else 5))+'@{}',rows)+'\\end{center}\n')


for sparse_mode, filename in (('pipeline','benchmark'),('kernels','kernels')):
    data=load(f'data/sparse-substitution-{filename}.json')
    if not data:continue
    rows=[]
    for r in data['cases']:
        m,q=r['medians'],r['paired_ratios']
        if sparse_mode=='pipeline':
            cells=[esc(r['source']['name'])]
            for old,new,key in (('old','current','current'),('old_portfolio','portfolio','portfolio')):
                cells.append('/'.join('--' if m[a] is None else f'{1000*m[a]:.3f}' for a in (old,new)))
                cells.append('--' if q[key]['median'] is None else f"{q[key]['median']:.3f}")
        else:
            cells=[esc(r['kind']),str(r['size'])]+[f'{1000*m[a]:.3f}' for a in ('old','current')]
            cells+=[f"{q['current']['median']:.3f}",'/'.join(f"{q[a]['median']:.3f}" for a in ('old_AA','current_AA'))]
        rows.append(' & '.join(cells)+r' \\')
    heading=('Input & default old/new ms & ratio & portfolio old/new ms & ratio' if sparse_mode=='pipeline' else
        'Family & size & old ms & new ms & ratio & old/new A/A')
    open(f'tables/sparse_substitution_{sparse_mode}.tex','w').write('\\begin{center}\\small\n'+table(heading,'@{}l'+('r'* (4 if sparse_mode=='pipeline' else 5))+'@{}',rows)+'\\end{center}\n')


sparse_incidence=load('data/sparse-incidence-benchmark.json')
if sparse_incidence:
    rows=[]
    for r in sparse_incidence['cases']:
        m,q=r['medians'],r['paired_ratios']
        cells=[esc(r['name'])]+[f'{1000*m[a]:.3f}' for a in ('dense','linear','split')]
        cells += [f'{q[a]:.3f}' for a in ('linear','split')]
        rows.append(' & '.join(cells)+r' \\')
    open('tables/sparse_incidence_pipeline.tex','w').write('\\begin{center}\\small\n'+table(
        'Input & dense ms & linear ms & split ms & dense/linear & dense/split','@{}lrrrrr@{}',rows)+'\\end{center}\n')


weighted_components=load('data/weighted-components-benchmark.json')
if weighted_components:
    for kind in ('dimension','core'):
        rows=[]
        old,new=('full_coordinates','three_weights') if kind=='dimension' else ('three_weights','core')
        for r in weighted_components['records']:
            if r['kind']!=kind:continue
            m,q=r['medians'],r['paired_median_ratios']
            cells=[str(r['parameter'])]+[f'{1000*m[a]["total"]:.3f}' for a in (old,new)]
            cells += [f'{q[f"{old}/{new}"]:.3f}']
            cells += [f'{q[f"{a}/{a}_control"]:.3f}' for a in (old,new)]
            rows.append(' & '.join(cells)+r' \\')
        heading=('Tetrahedra & full ms & three ms & full/three & full A/A & three A/A' if kind=='dimension' else
                 '$b$, $g=2^b$ & raw ms & core ms & raw/core & raw A/A & core A/A')
        open(f'tables/weighted_components_{kind}.tex','w').write('\\begin{center}\\small\n'+table(
            heading,'@{}rrrrrr@{}',rows)+'\\end{center}\n')


for ordered_mode in ('kernels','stages','pipeline'):
    data=load(f'data/ordered-batch-{ordered_mode}.json')
    if not data:continue
    rows=[]
    for r in data['cases']:
        s,m,q=r['source'],r['medians'],r['paired_ratios']
        cells=([esc(s['kind']),str(s['size'])] if ordered_mode=='kernels' else
               [str(s['crossings'])] if ordered_mode=='stages' else [esc(s['name'])])
        cells += ['--' if m[a] is None else f'{1000*m[a]:.3f}' for a in ('old','current')]
        cells += ['--' if q[a]['median'] is None else f"{q[a]['median']:.3f}" for a in ('current','old_AA','current_AA')]
        rows.append(' & '.join(cells)+r' \\')
    heading=('Family & pivots' if ordered_mode=='kernels' else 'Crossings' if ordered_mode=='stages' else 'Input')
    heading += ' & old ms & new ms & old/new & old A/A & new A/A'
    open(f'tables/ordered_batch_{ordered_mode}.tex','w').write('\\begin{center}\\small\n'+table(
        heading,'@{}l'+('r'* (6 if ordered_mode=='kernels' else 5))+'@{}',rows)+'\\end{center}\n')


for merger_mode in ('intervals','normal'):
    data=load(f'data/adaptive-merger-{merger_mode}.json')
    if not data:continue
    rows=[]
    for r in data['cases']:
        m,q=r['medians'],r['paired_ratios']
        cells=[esc(r['source']['name'])]
        arms=('old','adaptive','queue') if merger_mode=='intervals' else ('old','current')
        cells += [f'{1000*m[a]:.3f}' for a in arms]
        ratios=('adaptive','queue') if merger_mode=='intervals' else ('current','old_AA','current_AA')
        cells += [f"{q[a]['median']:.3f}" for a in ratios]
        rows.append(' & '.join(cells)+r' \\')
    heading=('Input & old ms & adaptive ms & queue ms & old/adapt. & old/queue' if merger_mode=='intervals' else
             'Query & old ms & new ms & old/new & old A/A & new A/A')
    open(f'tables/adaptive_merger_{merger_mode}.tex','w').write('\\begin{center}\\small\n'+table(
        heading,'@{}lrrrrr@{}',rows)+'\\end{center}\n')


for persistent_mode in ('kernels','source','stages','pipeline'):
    data=load(f'data/persistent-replay-{persistent_mode}.json')
    if not data:continue
    rows=[]
    for r in data['cases']:
        s,m,q=r['source'],r['medians'],r['paired_ratios']
        cells=([esc(s['kind']),str(s['size'])] if persistent_mode=='kernels' else
               [str(s['crossings'])] if persistent_mode in ('stages','source') else [esc(s['name'])])
        cells += ['--' if m[a] is None else f'{1000*m[a]:.3f}' for a in ('old','current')]
        cells += ['--' if q[a]['median'] is None else f"{q[a]['median']:.3f}" for a in ('current','old_AA','current_AA')]
        rows.append(' & '.join(cells)+r' \\')
    heading=('Family & pivots' if persistent_mode=='kernels' else 'Crossings' if persistent_mode in ('stages','source') else 'Input')
    heading += ' & old ms & new ms & old/new & old A/A & new A/A'
    open(f'tables/persistent_replay_{persistent_mode}.tex','w').write('\\begin{center}\\small\n'+table(
        heading,'@{}l'+('r'* (6 if persistent_mode=='kernels' else 5))+'@{}',rows)+'\\end{center}\n')

# Keep the scope-separated coherent-analysis tables tied to their raw records.
if os.path.exists('data/coherent-escape-benchmark.json'):
    import runpy
    runpy.run_path('data/coherent_escape_tables.py')

if os.path.exists('data/coorientation-benchmark.json'):
    import runpy
    runpy.run_path('data/coorientation_tables.py')

if os.path.exists('data/orbit-direction-benchmark.json'):
    import runpy
    runpy.run_path('data/orbit_direction_tables.py')

if os.path.exists('data/orbit-race-benchmark.json'):
    import runpy
    runpy.run_path('data/orbit_race_tables.py')

if os.path.exists('data/incoming-sectors-benchmark.json'):
    import runpy
    runpy.run_path('data/incoming_sectors_tables.py')

if os.path.exists('data/topology-spectra-benchmark.json'):
    import runpy
    runpy.run_path('data/topology_spectra_tables.py')

if os.path.exists('data/unit-ray-benchmark.json'):
    import runpy
    runpy.run_path('data/unit_ray_tables.py')

if os.path.exists('data/weighted-coorientation-benchmark.json'):
    import runpy
    runpy.run_path('data/weighted_coorientation_tables.py')

if os.path.exists('data/envelopes-benchmark.json'):
    import runpy
    runpy.run_path('data/envelopes_tables.py')

if os.path.exists('data/planar-sectors-benchmark.json'):
    import runpy
    runpy.run_path('data/planar_sectors_tables.py')

if os.path.exists('data/planar-adaptive-benchmark.json'):
    import runpy
    runpy.run_path('data/planar_adaptive_tables.py')

if os.path.exists('data/sector-windows-benchmark.json'):
    import runpy
    runpy.run_path('data/sector_windows_tables.py')

if os.path.exists('data/window-basis-benchmark.json'):
    import runpy
    runpy.run_path('data/window_basis_tables.py')

if os.path.exists('data/window-euler-benchmark.json'):
    import runpy
    runpy.run_path('data/window_euler_tables.py')

if os.path.exists('data/window-modes-benchmark.json'):
    import runpy
    runpy.run_path('data/window_modes_tables.py')

if os.path.exists('data/window-geometry-benchmark.json'):
    import runpy
    runpy.run_path('data/window_geometry_tables.py')

if os.path.exists('data/disc-context-benchmark.json'):
    import runpy
    runpy.run_path('data/disc_context_tables.py')

if os.path.exists('data/euler-aggregate-benchmark.json'):
    import runpy
    runpy.run_path('data/euler_aggregate_tables.py')

if os.path.exists('data/generic-euler-benchmark.json'):
    import runpy
    runpy.run_path('data/generic_euler_tables.py')

if os.path.exists('data/feasible-span-benchmark.json'):
    import runpy
    runpy.run_path('data/feasible_span_tables.py')

if os.path.exists('data/matching-support-benchmark.json'):
    import runpy
    runpy.run_path('data/matching_support_tables.py')

if os.path.exists('data/pachner-native-diagram-benchmark.json'):
    import runpy
    runpy.run_path('data/pachner_native_tables.py')

if os.path.exists('data/cover-oracle-diagram-benchmark.json'):
    import runpy
    runpy.run_path('data/cover_oracle_tables.py')

if os.path.exists('data/pachner-epochs-benchmark.json'):
    import runpy
    runpy.run_path('data/pachner_epochs_tables.py')

if os.path.exists('data/epoch-gauge-benchmark.json'):
    import runpy
    runpy.run_path('data/epoch_gauge_tables.py')

if os.path.exists('data/transport-annulus-benchmark.json'):
    import runpy
    runpy.run_path('data/transport_annulus_tables.py')

if os.path.exists('data/matching-pairs-benchmark.json'):
    import runpy
    runpy.run_path('data/matching_pairs_tables.py')

if os.path.exists('data/cut-complement-benchmark.json'):
    import runpy
    runpy.run_path('data/cut_complement_tables.py')

if os.path.exists('data/cut-products-benchmark.json'):
    import runpy
    runpy.run_path('data/cut_products_tables.py')

if os.path.exists('data/prismatic-inventory-benchmark.json'):
    import runpy
    runpy.run_path('data/prismatic_inventory_tables.py')
