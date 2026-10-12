import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
names=['positive-3','positive-9','positive-17','negative-3','negative-64','negative-1024']
lines=[r'\begin{center}',r'\begin{tabular}{lrrrr}',r'\toprule',r'Family & Copies & Explicit (ms) & Kernel (ms) & Ratio\\',r'\midrule']
for name in names:
 d=json.loads((root/'experiments'/('benchmark-'+name+'.json')).read_text())
 lines.append(f"{d['family'].capitalize()} & {d['source_count']:,} & {d['medians']['explicit']*1000:.3f} & {d['medians']['kernel']*1000:.3f} & {d['median_paired_ratio']:.3f}\\\\")
lines.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
(root/'article/benchmark_table.tex').write_text('\n'.join(lines)+'\n')

# Keep the downloadable main TeX file self-contained.
p=root/'article/disconnected_tile_kernels.tex'
s=p.read_text();a='% BEGIN GENERATED BENCHMARK TABLE';b='% END GENERATED BENCHMARK TABLE'
if a in s and b in s:
    start=s.index(a)+len(a);end=s.index(b,start)
    p.write_text(s[:start]+'\n'+'\n'.join(lines)+'\n'+s[end:])
