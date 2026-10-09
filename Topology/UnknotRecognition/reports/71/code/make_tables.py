"""Generate article tables from retained JSON; never reruns experiments."""
import csv
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
data=json.loads((root/'results/benchmark.json').read_text())
audit=json.loads((root/'results/audit.json').read_text())
rows=[]
lines=[r'\begin{tabular}{rrrrrrr}',r'\toprule',r'$r$ & $\lambda$ & Layers & Exact (ms) & Root (ms) & Cycle (ms) & Root/cycle\\',r'\midrule']
for f in data['fixtures']:
    m=f['median_seconds'];ratio=m['root']/m['cycle']
    lines.append(f"{f['r']} & {f['lambda']} & {f['depth']} & {m['exact']*1000:.2f} & {m['root']*1000:.2f} & {m['cycle']*1000:.2f} & {ratio:.2f}\\\\")
    rows.append({'r':f['r'],'lambda':f['lambda'],'depth':f['depth'],**{f'{k}_seconds':v for k,v in m.items()},'root_over_cycle':ratio})
lines += [r'\bottomrule',r'\end{tabular}']
(root/'results/benchmark_table.tex').write_text('\n'.join(lines)+'\n')
with (root/'results/benchmark.csv').open('w',newline='') as stream:
    writer=csv.DictWriter(stream,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
lines=[r'\begin{tabular}{rrrrrrr}',r'\toprule',r'$r$ & $\lambda$ & Initial input & Exact peak & Root peak & Cycle peak & Exact/cycle work\\',r'\midrule']
for f in data['fixtures']:
    peaks={m:max(v) for m,v in f['retained_by_stage'].items()}
    ratio=f['generated_total']['exact']/f['generated_total']['cycle']
    lines.append(f"{f['r']} & {f['lambda']} & {f['initial_candidates']} & {peaks['exact']} & {peaks['root']} & {peaks['cycle']} & {ratio:.2f}\\\\")
lines += [r'\bottomrule',r'\end{tabular}']
(root/'results/work_table.tex').write_text('\n'.join(lines)+'\n')
m=data['single_cap_control']['median_seconds']
text=(rf"\newcommand{{\SingleDirect}}{{{1000*m['direct']:.2f}}}"+'\n'+
      rf"\newcommand{{\SingleRoot}}{{{1000*m['root']:.2f}}}"+'\n'+
      rf"\newcommand{{\SingleCycle}}{{{1000*m['cycle']:.2f}}}"+'\n')
(root/'results/measurements.tex').write_text(text)
lines=[r'\begin{tabular}{lr}',r'\toprule',r'Independent audit item & Completed checks\\',r'\midrule']
for name,key in [('Envelope matrices','envelope_cases'),('Direct matrix entries','matrix_entries'),('Graded rank checks','graded_rank_checks'),('Weighted families','weighted_families'),('Weighted cap/sector queries','weighted_queries'),('Complete grammar triples','grammar_triples'),('Successful grammar mesh replays','successful_mesh_replays'),('Random surface pairs','random_surface_pairs'),('Fully enumerated small grammars','literal_assignment_grammars'),('Literal complete assignments','literal_assignments')]:
    lines.append(f"{name} & {audit[key]:,}\\\\")
lines += [r'\bottomrule',r'\end{tabular}']
(root/'results/audit_table.tex').write_text('\n'.join(lines)+'\n')
