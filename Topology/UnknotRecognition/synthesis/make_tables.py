"""Generate LaTeX table fragments from the cross-validation and benchmark JSON files."""
import json
import os

os.chdir(os.path.dirname(os.path.abspath(__file__)))
D = 'data/'


def esc(s):
    return str(s).replace('_', r'\_').replace('%', r'\%').replace('&', r'\&')


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
bpath = '../fast/results/benchmark.json'
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
print('tables written:', sorted(os.listdir('tables')))
