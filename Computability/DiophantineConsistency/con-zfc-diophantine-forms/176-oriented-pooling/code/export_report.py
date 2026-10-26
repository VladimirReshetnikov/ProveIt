#!/usr/bin/env python3
"""Generate exact printed inputs; an independent parser checks the rows."""
from pathlib import Path
from collections import Counter
import json

ROOT=Path(__file__).resolve().parents[1]
REPORT=ROOT/'report'

def polynomial(terms):
    result=[]
    for c,mon in terms:
        powers=Counter(mon)
        body=''.join('x_{%d}'%i+('^{%d}'%e if e>1 else '') for i,e in sorted(powers.items()))
        if abs(c)!=1 or not mon:body=str(abs(c))+body
        result.append(('-' if c<0 else '+')+body)
    text=' '.join(result)
    return text[1:] if text.startswith('+') else text

def export_rows():
    source=json.loads((ROOT/'source/equation216.json').read_text())
    omit={97,98,99,100,101,102,149,150,151,152}
    text=[r'{\footnotesize']
    for j,row in enumerate(source['residuals']):
        if j in omit:continue
        chunks=[];current=[];cost=0
        for term in row['terms']:
            c,mon=term
            width=8+4*len(str(abs(c)))+sum(7+2*len(str(i)) for i in set(mon))
            if current and cost+width>335:
                chunks.append(current);current=[];cost=0
            current.append(term);cost+=width
        if current:chunks.append(current)
        text.extend(['% BEGIN_RESIDUAL '+str(j),r'\begin{align*}'])
        for k,chunk in enumerate(chunks):
            body=polynomial(chunk)
            if k:
                if chunk[0][0]>0:body='+'+body
                text.append(' &{}'+body+(r'\\' if k<len(chunks)-1 else ''))
            else:text.append(' Q_{%d}={}&'%j+body+(r'\\' if len(chunks)>1 else ''))
        text.extend([r'\end{align*}','% END_RESIDUAL '+str(j)])
    text.append('}')
    (REPORT/'residuals.tex').write_text('\n'.join(text)+'\n')

def export_ports():
    cert=json.loads((ROOT/'equations/P207_certificate.json').read_text())
    rows=[r'\begin{center}\small',r'\begin{longtable}{rclllll}',
          r'\toprule Request & Base group & Output $m$ & Index $k$ & Difference $D_i$ & $Y_i$ & $Z_i$\\\midrule\endhead']
    for r in cert['ports']['requests']:
        fields=[str(r['number']),str(r['group'])]
        for key in ['m','k','D','Y','Z']:
            value='h' if r['number']==17 and key=='k' else polynomial(r[key])
            fields.append('$'+value+'$')
        rows.append(' & '.join(fields)+r'\\')
    rows.extend([r'\bottomrule\end{longtable}\end{center}'])
    (REPORT/'ports.tex').write_text('\n'.join(rows)+'\n')

def export_results():
    data=json.loads((ROOT/'higher_degree/RESULTS.json').read_text())
    rows=[r'\begin{center}\small',r'\begin{tabular}{rrrrrl}',r'\toprule',
          r'Variables & Degree & Residuals & Live operations & Height bound & Seed\\\midrule']
    for r in data:
        seed={'source211.json':r'$P_{211}$','source209.json':r'$P_{209}$',
              'source207.json':r'$P_{207}$','source206_joint.json':r'$P_{206}$'}[r['base_file']]
        rows.append(f"{r['variables']} & {r['degree']:,} & {r['residuals']} & {r['live_binary_operations']:,} & $2^{{{r['coefficient_height_bound_exponent']}}}$ & {seed}"+r'\\')
    rows.extend([r'\bottomrule\end{tabular}\end{center}',
       'The height column is a checked upper bound on the maximum absolute expanded coefficient. ',
       'The largest literal integer in each circuit is 384. Live operations count binary ',
       'addition, subtraction, and multiplication in the emitted shared circuit, including squares.',
       '',r'The 90-variable equation has 27 residuals and exact degree 32,768. ',
       r'It is the smallest-arity equation produced in this package. The 121-variable ',
       r'degree-16 equation is a useful alternative when degree matters. Their exact files are ',
       r'\code{higher_degree/equations/integer90_degree32768.json} and ',
       r'\code{higher_degree/equations/integer121_degree16.json}.'])
    (REPORT/'results.tex').write_text('\n'.join(rows)+'\n')

def export_pivots():
    data=json.loads((ROOT/'higher_degree/RESULTS.json').read_text())
    lines=[]
    for r in data:
        doc=json.loads((ROOT/'higher_degree/equations'/r['file']).read_text())
        lines.append(r'\subsection*{%d variables, degree %s}'%(r['variables'],f"{r['degree']:,}"))
        lines.append(r'Seed: \code{%s}. Coordinates and row labels below are original P216 indices; the pool quotients have synthetic labels beginning at 216.'%r['base_file'])
        lines.append(r'{\small\raggedright')
        lines.append(', '.join('$({},{})$'.format(s['row'],s['variable']) for s in doc['elimination_steps'])+r'.\par}')
        lines.append('')
    (REPORT/'pivots.tex').write_text('\n'.join(lines)+'\n')

def flatten():
    main=(REPORT/'report.tex').read_text()
    for stem in ['results','ports','residuals','pivots']:
        main=main.replace('\\input{'+stem+'.tex}',(REPORT/(stem+'.tex')).read_text())
    (REPORT/'report_standalone.tex').write_text(main)

if __name__=='__main__':
    export_rows();export_ports();export_results();export_pivots();flatten()
    print('Generated four mathematical appendices and standalone LaTeX.')
