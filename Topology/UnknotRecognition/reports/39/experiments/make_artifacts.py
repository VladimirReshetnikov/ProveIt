import json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'code'))
from su2budget.fixtures import trefoil,cyclic_meridians,torus_nonmeridional,huge_braid_relation,braid_wirtinger
from su2budget.wirtinger import minimum_degrees,compile_seeds,find_small_seeds
from su2budget.dihedral import solve
from su2budget.multivariate import compile_formula

root=Path(__file__).resolve().parents[1]
fixtures={'trefoil':trefoil(),'unknot_two_meridians':cyclic_meridians(),
          'trefoil_nonmeridional':torus_nonmeridional(),'compressed_torus_1024':huge_braid_relation(1024)}
n,c,co=braid_wirtinger(3,[1,-2,1,-2]);cert=minimum_degrees(n,c,[0,1])
fixtures['figure_eight']=compile_seeds(n,c,cert,label='figure-eight: braid (sigma1 sigma2^-1)^2, seeds 0 and 1')
(root/'examples'/'figure_eight_wirtinger_certificate.json').write_text(json.dumps(dict(
    strands=3,braid_word=[1,-2,1,-2],components=co,arcs=n,crossings=c,certificate=cert),indent=2)+'\n')
for name,p in fixtures.items():
    (root/'examples'/f'{name}.json').write_text(json.dumps(p.to_dict(),indent=2)+'\n')
    if p.meridian_generators:
        (root/'examples'/f'{name}.certificate.json').write_text(json.dumps(solve(p),indent=2)+'\n')
for name in ('trefoil','trefoil_nonmeridional'):
    p=fixtures[name]
    (root/'examples'/f'{name}_generic.wl').write_text(compile_formula(p).wolfram())
    (root/'examples'/f'{name}_lifted.wl').write_text(compile_formula(p,p.products()).wolfram())
bench=json.loads((root/'data'/'benchmarks.json').read_text())
lines=[r'\begin{tabular}{rrrrr}',r'\toprule',r'$p$ & Integer (ms) & Control (ms) & Univariate (ms) & Ratio\\',r'\midrule']
for row in bench['paired']:
    m=row['median_seconds']
    lines.append(f"{row['p']} & {1000*m['dihedral']:.4f} & {1000*m['control']:.4f} & {1000*m['univariate']:.3f} & {row['ratio_univariate_over_dihedral']:.1f}\\\\")
lines.extend([r'\bottomrule',r'\end{tabular}'])
(root/'data'/'paired_table.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{tabular}{rrrr}',r'\toprule',r'Squaring depth $b$ & Live nodes & Exponent bits & Solve + replay (ms)\\',r'\midrule']
for row in bench['capacity']:
    lines.append(f"{row['squaring_depth']:,} & {row['live_nodes']:,} & {row['peak_exponent_bits']:,} & {1000*row['median_seconds']:.3f}\\\\")
lines.extend([r'\bottomrule',r'\end{tabular}'])
(root/'data'/'capacity_table.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{tabular}{rrrrr}',r'\toprule',r'$m$ & Live products & No checkpoints & All checkpoints & Mixed\\',r'\midrule']
for row in bench['tradeoff']:
    lines.append(f"{row['m']} & {row['live_products']} & {row['no_checkpoints']['kappa']:.2f} & {row['all_checkpoints']['kappa']:.2f} & {row['mixed_checkpoints']['kappa']:.2f}\\\\")
lines.extend([r'\bottomrule',r'\end{tabular}'])
(root/'data'/'tradeoff_table.tex').write_text('\n'.join(lines)+'\n')
print('Examples, replay certificates, generic Wolfram queries, and article tables written.')
