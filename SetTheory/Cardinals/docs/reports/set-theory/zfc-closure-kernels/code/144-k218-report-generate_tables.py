#!/usr/bin/env python3
"""Generate the complete machine, delta, and identity appendices."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def parse(path):
    ans={}
    for line in path.read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,z=line.split();ans[int(q),int(b)]=(int(w),d,int(z))
    return ans
def action(x,canonical=False):
    w,d,z=x
    if isinstance(d,int):d='R'if d==1 else'L'
    target='H'if canonical and z==218 else str(z)
    return f'${w}{d}{target}$'
T=parse(ROOT/'machine/k218.tm')
assert set(T)=={(q,b)for q in range(218)for b in(0,1)}
head=r'State & Read 0 & Read 1 & State & Read 0 & Read 1 & State & Read 0 & Read 1\\'
lines=[r'\small',r'\begin{longtable}{rll@{\quad}rll@{\quad}rll}',r'\toprule',head,r'\midrule\endfirsthead',r'\toprule',head,r'\midrule\endhead',r'\bottomrule\endfoot']
for q in range(73):
    cells=[]
    for z in (q,q+73,q+146):
        cells.extend([str(z),action(T[z,0],True),action(T[z,1],True)]if z<218 else['','',''])
    lines.append(' & '.join(cells)+r'\\')
lines.append(r'\end{longtable}\normalsize')
(HERE/'table.tex').write_text('\n'.join(lines)+'\n')
D=json.loads((ROOT/'verification/construction/construction.json').read_text())
lines=[r'\begin{longtable}{rrll}',r'\toprule',r'Native state & Read & K219 action & K218 action\\',r'\midrule\endfirsthead',r'\toprule',r'Native state & Read & K219 action & K218 action\\',r'\midrule\endhead',r'\bottomrule\endfoot']
assert len(D['changed_retained_rows'])==32
for r in D['changed_retained_rows']:lines.append(f"{r['state']} & {r['read']} & {action(r['old'])} & {action(r['new'])}"+r'\\')
lines.append(r'\end{longtable}')
(HERE/'delta.tex').write_text('\n'.join(lines)+'\n')
files=[('Native table','machine/k218.native.tm'),('Canonical table','machine/k218.tm'),('Source sites','machine/sites218.json'),('Guarded case summaries','portable/reference_results/cases.json'),('Pinned K219 archive','portable/vendor/K219_Construction_2026-10-20.zip')]
lines=[r'\begin{center}\small',r'\begin{tabular}{ll}',r'\toprule',r'Artifact & SHA-256\\',r'\midrule']
for label,p in files:
    h=hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
    lines.append(label+r' & \shortstack[l]{\texttt{'+h[:32]+r'}\\\texttt{'+h[32:]+r'}}\\[5pt]')
lines.extend([r'\bottomrule',r'\end{tabular}\end{center}'])
(HERE/'hashes.tex').write_text('\n'.join(lines)+'\n')
