#!/usr/bin/env python3
"""Generate the complete mathematical tables in the article from frozen data."""
import argparse,json
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
def tex_term(c,mon):
    body=''.join('x_{%d}'%v+('^{%d}'%e if e>1 else '') for v,e in sorted(Counter(mon).items()))
    return ('-' if c<0 else '+')+(str(abs(c)) if not body or abs(c)!=1 else '')+body
def parent_text():
    src=json.loads((ROOT/'sources/parent225.json').read_text());out=['\\begingroup\\small\n']
    for ri,row in enumerate(src['residuals']):
        chunks=[];line='';count=0
        for c,m in row['terms']:
            term=tex_term(c,m)
            if (len(line)+len(term)>115 or count>=8) and line:chunks.append(line);line='';count=0
            line+=term;count+=1
        if line:chunks.append(line)
        if chunks[0].startswith('+'):chunks[0]=chunks[0][1:]
        out.append('%%BEGIN_RESIDUAL %d\n\\[\n\\begin{aligned}\nR_{%d}={}&%s'%(ri,ri,chunks[0]))
        for line in chunks[1:]:out.append('\\\\\n&'+line)
        out.append('\n\\end{aligned}\n\\]\n%%END_RESIDUAL %d\n'%ri)
    out.append('\\endgroup\n');return ''.join(out)
def metric_text():
    data=[json.loads(p.read_text()) for p in (ROOT/'equations').glob('*.json')]
    data.sort(key=lambda p:(p['metrics']['degree'],p['metrics']['variables']))
    out=['\\begin{center}\\small\n\\begin{tabular}{rrrrr}\n\\toprule\nInteger variables & Exact degree & Residuals & Operations & $H$\\\\\n\\midrule\n']
    for p in data:
        m=p['metrics'];out.append(' & '.join(format(m[k],',') for k in ['variables','degree','residuals','binary_operations','coefficient_height_strict_power_of_two'])+'\\\\\n')
    out.append('\\bottomrule\n\\end{tabular}\n\\end{center}\n');return ''.join(out)
def pivots_text():
    data=[(p,json.loads(p.read_text())) for p in (ROOT/'certificates').glob('*.json')]
    data.sort(key=lambda q:(q[1]['degree_bound'],q[1]['variables']))
    out=[]
    for path,p in data:
        out.append('\\Needspace{5\\baselineskip}\n\\subsection*{%d integers, degree %s; %s grouping}\n'%(p['variables'],format(p['degree_bound'],','),p['variant']))
        out.append('%%BEGIN_PIVOTS %s\n\\begingroup\\small\n\\begin{longtable}{rrrrrr}\n'%path.stem)
        pairs=['$(%d,%d)$'%(s['row'],s['variable']) for s in p['steps']]
        for j in range(0,len(pairs),6):out.append(' & '.join(pairs[j:j+6])+(' &'*(6-len(pairs[j:j+6])))+'\\\\\n')
        out.append('\\end{longtable}\n\\endgroup\n%%END_PIVOTS %s\n'%path.stem)
    return ''.join(out)
def requests_text():
    rows=[(0,0,'x_0','x_5',146,'x_{147}','x_{148}'),(1,1,'x_1','x_{18}',182,'x_{183}','x_{184}+1'),(2,2,'x_1','x_{102}-1',182,'x_{183}','x_{184}+1'),(3,4,'x_0+x_3','x_{103}',155,'x_{156}','x_{157}'),(4,3,'x_0','x_{104}',146,'x_{147}','x_{148}'),(5,4,'x_9-1','x_{108}',158,'x_{159}-1','x_{160}'),(7,4,'x_{10}','x_{111}',161,'x_{162}','x_{163}'),(8,4,'x_{11}','x_{114}',164,'x_{165}','x_{166}'),(9,4,'x_{12}','x_{117}',167,'x_{168}','x_{169}'),(10,4,'x_{13}','x_{120}',170,'x_{171}','x_{172}'),(11,3,'x_5','x_{121}',173,'x_{174}','x_{175}'),(12,4,'x_{14}','x_{124}',176,'x_{177}','x_{178}'),(13,4,'x_{15}','x_{127}',179,'x_{180}','x_{181}'),(14,3,'x_1','x_{128}',182,'x_{183}','x_{184}+1'),(15,4,'x_{16}','x_{132}',185,'x_{186}','x_{187}'),(16,4,'x_{17}','x_{135}',188,'x_{189}','x_{190}'),(17,4,'x_{100}','x_{138}',191,'x_{192}','x_{193}')]
    out=['\\begin{center}\\small\n\\begin{tabular}{rrlllll}\n\\toprule\nRequest & Group & Index $k_i$ & Output $m_i$ & $D_i$ & $Y_i$ & $Z_i$\\\\\n\\midrule\n']
    for req,g,k,m,d,y,z in rows:out.append('%d & %d & $%s$ & $%s$ & $x_{%d}$ & $%s$ & $%s$\\\\\n'%(req,g,k,m,d,y,z))
    out.append('\\bottomrule\n\\end{tabular}\n\\end{center}\n');return ''.join(out)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    for name,text in [('parent_residuals.tex',parent_text()),('metrics.tex',metric_text()),('pivot_tables.tex',pivots_text()),('requests.tex',requests_text())]:
        p=ROOT/'report'/name
        if a.check:
            if p.read_text()!=text:raise ValueError('Article input differs: '+name)
        else:p.write_text(text)
    print('PASS: all four complete article inputs match frozen equations and certificates')
if __name__=='__main__':main()
