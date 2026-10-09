"""Build LaTeX tables from retained raw records; does not rerun timings."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
j=json.loads((root/'results/benchmark.json').read_text())
a=json.loads((root/'results/audit.json').read_text())
out=root/'paper/tables';out.mkdir(exist_ok=True)
rows=[r'\begin{tabular}{rrrrrr}',r'\toprule',r'$r$ & Full states & Basis & Full probes & Basis probes & Probe ratio \\',r'\midrule']
for x in j['static']:
 f,b=x['median']['full'],x['median']['basis']
 rows.append(f"{x['ports']} & {x['candidates']:,} & {x['dimension']} & {int(f['probes']):,} & {int(b['probes']):,} & {f['probes']/b['probes']:.1f} \\\\")
rows.extend([r'\bottomrule',r'\end{tabular}'])
(out/'sizes.tex').write_text('\n'.join(rows)+'\n')
rows=[r'\begin{tabular}{rrrrrrr}',r'\toprule',r'$r$ & Full setup & Basis setup & Full queries & Basis queries & Batch gain & One-query gain \\',r'\midrule']
for x in j['static']:
 f,b=x['median']['full'],x['median']['basis']
 rows.append(f"{x['ports']} & {1000*f['setup_s']:.2f} & {1000*b['setup_s']:.2f} & {1000*f['query_s']:.2f} & {1000*b['query_s']:.2f} & {x['whole_batch_speedup']:.2f} & {x['one_query_speedup']:.2f} \\\\")
rows.extend([r'\bottomrule',r'\end{tabular}'])
(out/'timings.tex').write_text('\n'.join(rows)+'\n')
rows=[r'\begin{tabular}{rrrrrrr}',r'\toprule',r'$r$ & Gates & Full generated & Basis generated & Full (ms) & Basis (ms) & Gain \\',r'\midrule']
for x in j['dynamic']:
 y=x['raw'][0]
 rows.append(f"{x['ports']} & {x['edges']} & {y['full_generated']:,} & {y['basis_generated']:,} & {1000*x['median_full_s']:.2f} & {1000*x['median_basis_s']:.2f} & {x['median_full_s']/x['median_basis_s']:.2f} \\\\")
rows.extend([r'\bottomrule',r'\end{tabular}'])
(out/'dynamic.tex').write_text('\n'.join(rows)+'\n')
rows=[r'\begin{tabular}{lrrrrrr}',r'\toprule',r'$G$ & $r$ & States & Rank over $\mathbb Q$ & Rank mod 2 & Rank mod 3 & Rank mod 5 \\',r'\midrule']
for x in a['group_rank_audit']:
 name={'trivial':r'$1$','C2':r'$C_2$','C3':r'$C_3$','S3':r'$S_3$'}[x['group']]
 rows.append(f"{name} & {x['ports']} & {x['states']} & {x['states']} & {x['rank_mod']['2']} & {x['rank_mod']['3']} & {x['rank_mod']['5']} \\\\")
rows.extend([r'\bottomrule',r'\end{tabular}'])
(out/'ranks.tex').write_text('\n'.join(rows)+'\n')

p=json.loads((root/'results/patch_benchmark.json').read_text())
rows=[r'\begin{tabular}{lrrrrrr}',r'\toprule',r'Grid & Sites & $b$ & Full peak & Basis peak & Full (ms) & Basis (ms) \\',r'\midrule']
for x in p['cases']:
    y=x['raw'][0]
    rows.append(f"${x['rows']}\\times {x['columns']}$ & {x['sites']} & {y['frontier_width']} & {y['full_peak_states']} & {y['basis_peak_states']} & {1000*x['median_full_s']:.2f} & {1000*x['median_basis_s']:.2f} \\\\")
rows.extend([r'\bottomrule',r'\end{tabular}'])
(out/'patchwork.tex').write_text('\n'.join(rows)+'\n')
