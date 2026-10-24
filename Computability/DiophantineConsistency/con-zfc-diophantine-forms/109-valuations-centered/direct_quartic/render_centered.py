#!/usr/bin/env python3
"""Print every final quadratic residual; deterministic JSON -> LaTeX."""
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'ConZFC_407_888_Quartics/code'))
from render_residuals import term

def generate(name,symbol):
    path=ROOT/'centered_output'/name/'equation.json'
    eq=json.loads(path.read_text())
    lines=['% Source SHA256: '+hashlib.sha256(path.read_bytes()).hexdigest(),
        '% Every listed residual is squared and all squares are summed.',
        r'\begingroup\small',r'\allowdisplaybreaks[4]',r'\setlength{\jot}{2pt}',
        r'\begin{align*}']
    for i,row in enumerate(eq['residuals']):
        chunks=[];current='';width=0
        for j,(c,m) in enumerate(row['terms']):
            sign,body,w=term(c,m)
            rendered=('-' if sign=='-' else '')+body if j==0 else sign+body
            if current and width+w>37:
                chunks.append(current);current=rendered;width=w
            else:current+=rendered;width+=w
        if current:chunks.append(current)
        for k,chunk in enumerate(chunks):
            prefix=symbol+'_{'+str(i)+'}={}&' if k==0 else '&{}'
            suffix=r'\\[3pt]' if k==len(chunks)-1 else r'\\*'
            lines.append(prefix+chunk+suffix)
    lines += [r'\end{align*}',r'\endgroup','']
    dest=ROOT/'appendix';dest.mkdir(exist_ok=True)
    target=dest/(('natural395' if name=='natural_cap64' else 'integer853')+'_rows.tex')
    target.write_text('\n'.join(lines))
    return {'path':str(target.relative_to(ROOT)),'rows':len(eq['residuals']),
        'variables':len(eq['variables']),'sha256':hashlib.sha256(target.read_bytes()).hexdigest()}
if __name__=='__main__':
    print(json.dumps([generate('natural_cap64','R'),generate('integer_cap16','S')],indent=2))

