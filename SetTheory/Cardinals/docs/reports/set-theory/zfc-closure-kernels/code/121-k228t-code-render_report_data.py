#!/usr/bin/env python3
"""Generate the report's exact hash panel and complete canonical table appendix."""
from pathlib import Path
import hashlib

package=Path(__file__).resolve().parent.parent
paths=[('Released K230 table','inputs/k230.tm'),
       ('Released K230 site certificate','inputs/sites230.json'),
       ('Primary canonical K228 table','machines/k228.tm'),
       ('K228 in original K230 labels','machines/k228_original_labels.tm'),
       ('Modified logical source','machines/sites228.json')]
out=[]
for title,path in paths:
    digest=hashlib.sha256((package/path).read_bytes()).hexdigest()
    out += [r'\textbf{'+title+r'} (\file{'+path+r'}):\\',r'\sha{'+digest+r'}\par\smallskip']
(package/'report/artifact-hashes.tex').write_text('\n'.join(out)+'\n')

table={}
for line in (package/'machines/k228.tm').read_text().splitlines():
    if line and not line.startswith('#'):
        q,b,w,d,z=line.split()
        table[int(q),int(b)]=w+d+z
assert set(table)=={(q,b) for q in range(228) for b in(0,1)}
out=[r'{\small',r'\setlength{\tabcolsep}{5pt}',
     r'\begin{longtable}{rrr@{\hspace{8mm}}rrr@{\hspace{8mm}}rrr}',
     r'\toprule',
     r'State & On 0 & On 1 & State & On 0 & On 1 & State & On 0 & On 1\\',
     r'\midrule\endfirsthead',r'\toprule',
     r'State & On 0 & On 1 & State & On 0 & On 1 & State & On 0 & On 1\\',
     r'\midrule\endhead',r'\midrule\multicolumn{9}{r}{Continued on next page}\\\endfoot',
     r'\bottomrule\endlastfoot']
for i in range(76):
    fields=[]
    for q in (i,i+76,i+152):
        fields += [str(q),r'\texttt{'+table[q,0]+'}',r'\texttt{'+table[q,1]+'}']
    out.append(' & '.join(fields)+r'\\')
out += [r'\end{longtable}',r'}']
(package/'report/canonical-table.tex').write_text('\n'.join(out)+'\n')
print('Generated exact hashes and all456 canonical transitions')
