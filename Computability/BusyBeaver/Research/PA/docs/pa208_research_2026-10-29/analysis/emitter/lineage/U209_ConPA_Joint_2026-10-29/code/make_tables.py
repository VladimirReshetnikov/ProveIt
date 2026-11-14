#!/usr/bin/env python3
"""Generate exact LaTeX table fragments from the delivered literal data."""
from common import ROOT,read
from build import TARGET

def action(row):
    w,d,z=row;return f'${w}\\mathrm{{{"R"if d==1 else"L"}}}{z}$'
def main():
    directory=ROOT/'tables';directory.mkdir(exist_ok=True)
    pairs=list(TARGET.items());lines=[r'\begin{center}\small',r'\begin{tabular}{@{}rrr@{\qquad\qquad}rrr@{}}',r'\toprule',r'$q$ & zero child & one child & $q$ & zero child & one child\\',r'\midrule']
    for i in range(9):
        a,(x,y)=pairs[i];b,(u,v)=pairs[i+9];lines.append(f'{a}&{x}&{y}&{b}&{u}&{v}'+r'\\')
    lines.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
    (directory/'decoder.tex').write_text('\n'.join(lines)+'\n')
    old=read(ROOT/'baseline/u212.native.tm');new=read(ROOT/'machine/u209.native.tm')
    lines=[r'\begin{longtable}{@{}rrll@{}}',r'\toprule',r'Native state & Read & U212 action & U209 action\\',r'\midrule\endfirsthead',r'\toprule',r'Native state & Read & U212 action & U209 action\\',r'\midrule\endhead',r'\bottomrule\endfoot']
    for key in sorted(old):
        if old[key]==new.get(key):continue
        q,b=key;last=action(new[key])if key in new else r'\emph{deleted}'
        lines.append(f'{q}&{b}&{action(old[key])}&{last}'+r'\\')
    lines.append(r'\end{longtable}');(directory/'patch.tex').write_text('\n'.join(lines)+'\n')
    dense=read(ROOT/'machine/u209.tm')
    lines=[r'\begingroup\small',r'\setlength{\tabcolsep}{6pt}',r'\begin{longtable}{@{}rrr@{\qquad}rrr@{\qquad}rrr@{}}',r'\toprule',r'$q$&read 0&read 1&$q$&read 0&read 1&$q$&read 0&read 1\\',r'\midrule\endfirsthead',r'\toprule',r'$q$&read 0&read 1&$q$&read 0&read 1&$q$&read 0&read 1\\',r'\midrule\endhead',r'\bottomrule\endfoot']
    for i in range(70):
        cells=[]
        for q in(i,i+70,i+140):
            cells.extend([str(q),action(dense[q,0]),action(dense[q,1])]if q<209 else['','',''])
        lines.append('&'.join(cells)+r'\\')
    lines.extend([r'\end{longtable}',r'\endgroup']);(directory/'transitions.tex').write_text('\n'.join(lines)+'\n')
if __name__=='__main__':main()
