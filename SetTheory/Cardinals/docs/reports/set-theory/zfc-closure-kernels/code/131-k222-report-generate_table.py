from pathlib import Path
import argparse
p=argparse.ArgumentParser();p.add_argument('table',type=Path);a=p.parse_args()
rows={}
for line in a.table.read_text().splitlines():
    if not line or line.startswith('#'):continue
    q,b,w,d,t=line.split();rows[int(q),int(b)]=(w,d,t)
assert set(rows)=={(q,b)for q in range(222) for b in range(2)}
lines=[r'\small']
def f(q,b):
    w,d,t=rows[q,b];return f'{w}{d}{t}'
for page in range(2):
    if page:lines += [r'\clearpage',r'\noindent Complete canonical table continued.']
    lines += [r'\begin{center}',r'\begin{tabular}{rll@{\qquad}rll@{\qquad}rll}',r'\toprule',r'$q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1\\',r'\midrule']
    for i in range(37):
        pieces=[]
        for col in range(3):
            q=page*111+col*37+i
            pieces.append(f'{q} & {f(q,0)} & {f(q,1)}')
        lines.append(' & '.join(pieces)+r'\\')
    lines += [r'\bottomrule',r'\end{tabular}',r'\end{center}']
lines += [r'\normalsize']
Path(__file__).with_name('transition_table.tex').write_text('\n'.join(lines)+'\n')
