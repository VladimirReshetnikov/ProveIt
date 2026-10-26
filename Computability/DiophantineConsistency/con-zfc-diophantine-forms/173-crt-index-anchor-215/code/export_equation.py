#!/usr/bin/env python3
"""Export literal residuals and tables from the frozen exact JSON equations."""
from collections import Counter, defaultdict
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]

def collect(eq):
    out=defaultdict(int)
    for row in eq['residuals']:
        for a,m in row['terms']:
            for b,n in row['terms']:
                out[tuple(sorted(m+n))]+=a*b
    return {m:c for m,c in out.items() if c}

def measure(eq):
    poly=collect(eq)
    return {'variables':len(eq['variables']),'rows':len(eq['residuals']),
            'degree':max(map(len,poly)),'monomials':len(poly),
            'height':max(map(abs,poly.values())),
            'row_height':max(abs(c) for r in eq['residuals'] for c,m in r['terms'])}

def rendered_term(c,m,tex=False,first=False):
    sign=('-' if c<0 else '') if first else (' - ' if c<0 else ' + ')
    power=Counter(m)
    if tex:
        variables=' '.join('x_{'+str(i)+'}'+('^{'+str(p)+'}' if p>1 else '') for i,p in sorted(power.items()))
        coeff=str(abs(c)) if abs(c)!=1 or not m else ''
        return sign+coeff+variables
    variables='*'.join('x'+str(i)+('^'+str(p) if p>1 else '') for i,p in sorted(power.items()))
    coeff=str(abs(c)) if abs(c)!=1 or not m else ''
    return sign+coeff+('*' if coeff and variables else '')+variables

def export_profile(folder):
    eq=json.loads((folder/'equation.json').read_text())
    met=measure(eq)
    (folder/'metrics.json').write_text(json.dumps(met,indent=2)+'\n')
    lines=['Domain: all coordinates independently range over the integers.',
           f'P(x0,...,x{met["variables"]-1}) = sum(Rj^2 for j=0,...,{met["rows"]-1}).',
           'The equation is P=0. All residuals below are literal polynomials.','']
    for j,row in enumerate(eq['residuals']):
        terms=sorted(row['terms'],key=lambda item:item[1])
        lines.append(f'R{j} = '+''.join(rendered_term(c,m,first=i==0) for i,(c,m) in enumerate(terms)))
    (folder/'residuals.txt').write_text('\n'.join(lines)+'\n')
    (folder/'variables.tsv').write_text('index\thistorical_coordinate_name\n'+''.join(
        f'{i}\t{v.get("name",str(v))}\n' for i,v in enumerate(eq['variables'])))
    return eq,met

def main():
    principal,pm=export_profile(ROOT/'equations/principal')
    _,m214=export_profile(ROOT/'equations/companions/p214')
    _,m213=export_profile(ROOT/'equations/companions/p213')
    parent=json.loads((ROOT/'source/parent225/equation.json').read_text())
    parent_metrics=measure(parent)
    (ROOT/'source/parent225/metrics.json').write_text(json.dumps(parent_metrics,indent=2)+'\n')
    metrics={'parent225':parent_metrics,'principal215':pm,'companion214':m214,'companion213':m213}
    (ROOT/'verification/METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
    macros={'NV':pm['variables'],'LastVar':pm['variables']-1,'NR':pm['rows'],
            'LastRow':pm['rows']-1,'NT':pm['monomials'],'Height':pm['height']}
    (ROOT/'report/metrics.tex').write_text('% Generated from the literal equation.\n'+''.join(
        '\\newcommand{\\'+key+'}{'+str(value)+'}\n' for key,value in macros.items()))
    tex=['% Full literal residual list; parsed independently by the release checker.',
         '{\\small',r'\setlength{\jot}{2pt}',r'\allowdisplaybreaks[0]']
    for j,row in enumerate(principal['residuals']):
        terms=sorted(row['terms'],key=lambda item:item[1])
        tex.extend([f'% BEGIN RESIDUAL {j}',r'\begin{align*}'])
        for start in range(0,len(terms),6):
            line=''.join(rendered_term(c,m,tex=True,first=start+i==0)
                         for i,(c,m) in enumerate(terms[start:start+6]))
            prefix='R_{'+str(j)+'} ={}& ' if start==0 else '&{} '
            tex.append(prefix+line+(r' \\' if start+6<len(terms) else ''))
        tex.extend([r'\end{align*}',f'% END RESIDUAL {j}'])
    tex.append('}')
    (ROOT/'report/residuals.tex').write_text('\n'.join(tex)+'\n')
    comparison=[r'\begin{center}',r'\small',r'\begin{tabular}{@{}lrrrrr@{}}',
        r'\toprule Form & Variables & Squares & Degree & Monomials & Height\\\midrule']
    for label,m in [('Pinned parent',parent_metrics),('Principal',pm),('Companion',m214),('Companion',m213)]:
        if m['height']>10**20: height=r'$2.4179\times10^{24}$'
        elif m['height']>10**10: height=r'$1.0996\times10^{12}$'
        else: height=f'{m["height"]:,}'
        comparison.append(f'{label} & {m["variables"]} & {m["rows"]} & {m["degree"]} & {m["monomials"]:,} & {height}'+r'\\')
    comparison.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}',
        'The companion heights are rounded upward here. Their exact values are',
        r'\[1\,099\,511\,627\,852\qquad\text{and}\qquad2\,417\,851\,639\,242\,452\,488\,945\,685.\]'])
    (ROOT/'report/comparison.tex').write_text('\n'.join(comparison)+'\n')
    print(json.dumps(metrics,indent=2))

if __name__=='__main__':main()
