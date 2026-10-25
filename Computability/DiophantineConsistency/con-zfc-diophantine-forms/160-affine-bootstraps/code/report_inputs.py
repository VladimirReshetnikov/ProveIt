#!/usr/bin/env python3
"""Render the literal endpoint table and complete polynomial appendix."""
from collections import Counter
import argparse, json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
def read(p): return json.loads(p.read_text())
def number(n): return format(n,',').replace(',',r'\,')

def term(c,indices,latex=True):
    factors=[]
    for i,power in sorted(Counter(indices).items()):
        v=(r'x_{'+str(i)+'}') if latex else 'x'+str(i)
        if power>1: v+=('^{'+str(power)+'}') if latex else '**'+str(power)
        factors.append(v)
    product=('' if latex else '*').join(factors)
    magnitude='' if abs(c)==1 and product else str(abs(c))
    if not latex and magnitude and product: magnitude+='*'
    return ('-' if c<0 else '+')+magnitude+product

def residual_appendix(equation, symbol):
    lines=[r'\begingroup\footnotesize',r'\setlength{\jot}{2pt}\allowdisplaybreaks[4]',r'\begin{align*}']
    for i,row in enumerate(equation['residuals']):
        pieces=[term(c,m) for c,m in row['terms']]
        for j in range(0,len(pieces),5):
            segment=' '.join(pieces[j:j+5])
            if j==0 and segment.startswith('+'): segment=segment[1:]
            prefix=(f'{symbol}_{{{i}}} &={{}} ' if j==0 else r'&\quad{} ')
            lines.append(prefix+segment+r' \\')
    lines.extend([r'\end{align*}',r'\endgroup'])
    return '\n'.join(lines)+'\n'

def render():
    config=read(ROOT/'ENDPOINTS.json')
    selected=config['selected']
    primary=selected[config['primary']]
    smallest=selected[config['smallest']]
    metrics=read(ROOT/primary['path']/'METRICS.json')
    small=read(ROOT/smallest['path']/'METRICS.json')
    eq=read(ROOT/primary['path']/'equation.json')
    macros={
       'PrimaryVars':metrics['variables'],'PrimaryRows':metrics['rows'],
       'PrimaryTerms':metrics['monomials'],'PrimaryHeight':metrics['height'],
       'PrimaryLastVar':metrics['variables']-1,'PrimaryLastRow':metrics['rows']-1,
       'SmallVars':small['variables'],'SmallLastVar':small['variables']-1,
       'SmallRows':small['rows'],'SmallLastRow':small['rows']-1,
    }
    outputs={ROOT/'report/metrics.tex':''.join(fr'\newcommand{{\{k}}}{{{number(v)}}}'+'\n' for k,v in macros.items())}
    comparisons=[
        ('Inherited factorial-free',242,178,5018,7968),
        ('Inherited factorial-free, dense',241,177,12774,7968),
        ('Incoming shared factorial error',240,177,21482,6144),
        ('Incoming normalized residues',244,176,5212,3968),
    ]
    rows=[]
    for name,n,r,m,h in comparisons:
        rows.append(name+' & '+' & '.join(number(x) for x in (n,r,m,h))+r' \\'+'\n')
    rows.append(r'\midrule'+'\n')
    for key,entry in selected.items():
        m=read(ROOT/entry['path']/'METRICS.json')
        label=entry['label']+(' (main)' if key==config['primary'] else '')
        rows.append(label+' & '+' & '.join(number(m[x]) for x in ['variables','rows','monomials','height'])+r' \\'+'\n')
    outputs[ROOT/'report/comparison.tex']=(r'\begin{center}\small'+'\n'+r'\begin{tabular}{@{}lrrrr@{}}'+'\n'+
        r'\toprule Construction & Variables & Rows & Monomials & Height \\'+'\n'+r'\midrule'+'\n'+''.join(rows)+r'\bottomrule\end{tabular}\end{center}'+'\n')
    outputs[ROOT/'report/residuals.tex']=residual_appendix(eq,'R')
    outputs[ROOT/'report/residuals_237.tex']=residual_appendix(read(ROOT/smallest['path']/'equation.json'),'S')
    for entry in selected.values():
        path=ROOT/entry['path'];e=read(path/'equation.json')
        plain=[]
        for i,row in enumerate(e['residuals']):
            s=' '.join(term(c,m,False) for c,m in row['terms'])
            if s.startswith('+'):s=s[1:]
            plain.append(f'R{i} = {s}')
        outputs[path/'residuals.txt']='\n'.join(plain)+'\n'
    return outputs

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    outputs=render()
    for path,data in outputs.items():
        if args.check:
            if not path.exists() or path.read_text()!=data:
                raise ValueError('generated report input mismatch: '+str(path.relative_to(ROOT)))
        else:
            path.parent.mkdir(parents=True,exist_ok=True);path.write_text(data)
    print(('Checked' if args.check else 'Generated'),len(outputs),'literal report/endpoint exports.')

if __name__=='__main__':main()
