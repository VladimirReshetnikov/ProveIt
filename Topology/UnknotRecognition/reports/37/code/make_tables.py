"""Regenerate frozen article tables from delivered or rerun measurements."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
data=json.loads((root/'results/benchmarks.json').read_text())
head=r'\begin{center}\begin{tabular}{lrrrrr}\toprule'+'\n'
head+=r'Case & Forward & A/A control & Reverse & Cut-factor & F/C\\\midrule'+'\n'
def timing(rows,filename,synthetic=False):
    out=head
    for a in rows:
        t=a['median_seconds']; name=('$R='+str(a['R'])+'$') if synthetic else a['name'].replace('_',r'\_')
        out+=name+' & '+' & '.join(f'{1000*t[x]:.3f}' for x in ('forward','control','reverse','cut_factor'))
        out+=f" & {t['forward']/t['cut_factor']:.2f}"+r'\\'+'\n'
    out+=r'\bottomrule\end{tabular}\end{center}'+'\n'
    (root/'article'/filename).write_text(out)
timing(data['actual'],'actual_table.tex'); timing(data['synthetic'],'synthetic_table.tex',True)
out=r'\begin{center}\begin{tabular}{rrrrrr}\toprule'+'\n'
out+=r'$R$ & $M$ & Vertices & Edges & Endpoint compositions & First-hit compositions\\\midrule'+'\n'
for a in data['synthetic']:
    out+=' & '.join(str(a[x]) for x in ('R','M','vertices','edges','forward_compositions','factor_compositions'))+r'\\'+'\n'
out+=r'\bottomrule\end{tabular}\end{center}'+'\n'
(root/'article/counts_table.tex').write_text(out)
