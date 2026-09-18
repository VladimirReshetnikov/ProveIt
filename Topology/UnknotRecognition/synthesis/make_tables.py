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

print('tables written:', sorted(os.listdir('tables')))
