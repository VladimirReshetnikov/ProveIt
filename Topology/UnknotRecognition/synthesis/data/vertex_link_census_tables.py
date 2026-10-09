"""Render vertex-link operation counts and complete recognition timings."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
a=json.loads((ROOT/'data/vertex-link-census-audit.json').read_text())
rows=[r'\begin{tabular}{rrrrr}',r'\toprule',r'Tetrahedra & Old nodes & New nodes & Old unions & New unions \\',r'\midrule']
for r in a['union_find_family']:
 o,n=r['results']['old'],r['results']['new']
 rows.append(f"{r['tetrahedra']:,} & {o['allocated_nodes']:,} & {n['allocated_nodes']:,} & {o['joins']:,} & {n['joins']:,}"+r' \\')
rows.extend([r'\bottomrule',r'\end{tabular}']);(ROOT/'tables/vertex_link_census_family.tex').write_text('\n'.join(rows)+'\n')
b=json.loads((ROOT/'data/vertex-link-census-recognize-final.json').read_text())
rows=[r'\begin{tabular}{lrrrrr}',r'\toprule',r'Pipeline & Old ms & New ms & Old/new & Old A/A & New A/A \\',r'\midrule']
for r in b['cases']:
 name=r['name'].replace('optimized-positive','Original disc').replace('genus-one-miss','Three-crossing').replace('circle-9','Circle 9').replace('random-','Random ').replace('-plain',', plain').replace('-shell',', shell')
 m,p=r['medians'],r['paired_ratios']
 rows.append(f"{name} & {1000*m['old']:.3f} & {1000*m['new']:.3f} & {p['old_new']['median']:.3f} & {p['old_AA']['median']:.3f} & {p['new_AA']['median']:.3f}"+r' \\')
rows.extend([r'\bottomrule',r'\end{tabular}']);(ROOT/'tables/vertex_link_census_recognize.tex').write_text('\n'.join(rows)+'\n')
