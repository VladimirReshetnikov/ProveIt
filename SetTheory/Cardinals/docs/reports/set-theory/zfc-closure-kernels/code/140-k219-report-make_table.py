#!/usr/bin/env python3
from pathlib import Path
H=Path(__file__).resolve().parent;table={}
for line in(H.parent/'machine/k219.tm').read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,z=line.split();table[int(q),int(b)]=w+d+z
assert len(table)==438
out=[r'\begingroup\small',r'\setlength{\tabcolsep}{7pt}',r'\begin{longtable}{rll@{\hspace{12mm}}rll}',r'\toprule',r'State & Read 0 & Read 1 & State & Read 0 & Read 1\\',r'\midrule\endfirsthead',r'\toprule',r'State & Read 0 & Read 1 & State & Read 0 & Read 1\\',r'\midrule\endhead',r'\midrule\multicolumn{6}{r}{Continued on the next page}\\\endfoot',r'\bottomrule\endlastfoot']
for q in range(110):
 cols=[str(q),r'\texttt{'+table[q,0]+'}',r'\texttt{'+table[q,1]+'}']
 z=q+110
 cols+=([str(z),r'\texttt{'+table[z,0]+'}',r'\texttt{'+table[z,1]+'}']if z<219 else['','',''])
 out.append(' & '.join(cols)+r'\\')
out += [r'\end{longtable}',r'\endgroup']
(H/'table219.tex').write_text('\n'.join(out)+'\n')
