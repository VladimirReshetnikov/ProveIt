#!/usr/bin/env python3
"""Parse the displayed polynomial subset and compare it to the 87-gate graph.

This handles only the TeX subset used here; it is not a general TeX interpreter.
The final square sum is checked structurally to avoid expanding a huge polynomial.
"""
import hashlib
import json
from pathlib import Path
import re
import runpy
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
base=runpy.run_path(str(D.parent/'adaptive-direct-ordinate86/verify_display_tex86.py'))
dag=base['dag']; Parser=base['Parser']; symbol_map=base['symbol_map']
raw=(D/'candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828':
    raise ValueError('candidate mismatch')
c=json.loads(raw)
expected={'b':'qm','q':'q','C':'C','U':'U','E':'E','k':'k','ell':'ell','c':'c',
          'a':'a','H':'H','Delta':'Delta','L':'b0','M':'M','W':'Bt','R':'R',
          'Z':'Z','D':'Dstar','I':'I','Q':'Q','V':'V','A':'A0','B':'A1',
          'N':'Fa','S':'g72'}
def validate(text):
    display=text[text.index('% BEGIN VERIFIED DISPLAY\n'):text.index('% END VERIFIED DISPLAY\n')]
    # Pin the entire raw math environment before translating any residual aliases.
    marker = 'The single Diophantine equation is'
    if display.count(marker) != 1: raise ValueError('equation marker')
    section = display.split(marker, 1)[1]
    raw_equation = re.fullmatch(r'\s*\\\[(.*?)\\\]\s*', section, re.S)
    if not raw_equation or re.sub(r'\s+', '', raw_equation.group(1)) != '\\boxed{\\mathcal{P}^2+\\mathcal{D}^2+\\mathcal{Q}^2+\\mathcal{R}^2=0.}':
        raise ValueError('raw equation environment differs')
    unknowns=re.search(r'The only unknowns are the thirteen separately named positive-integer variables\s*\\\[(.*?)\\in\\mathbb Z_\{>0\}\.\s*\\\]',display,re.S)
    if not unknowns:raise ValueError('unknown declaration')
    listed=[x.strip().lstrip('\\') for x in unknowns.group(1).split(',')]
    if listed!=['J','F','alpha','f','g','T','X','Y','xi','eta','zeta','upsilon','gamma'] or len(set(listed))!=13:
        raise ValueError('unknown names')
    for key,value in ((r'\mathcal{P}','A'),(r'\mathcal{D}','B'),(r'\mathcal{Q}','N'),(r'\mathcal{R}','S')):
        display=display.replace(key,value)
    group=re.search(r'\\begin\{gathered\}(.*?)\\end\{gathered\}',display,re.S)
    if not group:raise ValueError('missing definitions')
    body=group.group(1).strip()
    if not body.endswith('.'):raise ValueError('definition punctuation')
    defs=[s.strip() for s in body[:-1].replace(r'\quad','').replace('\\\\',',').split(',') if s.strip()]
    variables={printed:dag[internal] for printed,internal in symbol_map.items()}
    seen=[]
    for definition in defs:
        parser=Parser(definition,variables);lhs=parser.take()
        if lhs not in expected or lhs in seen or parser.take()!='=':raise ValueError(('definition',definition))
        value=parser.expression();want=dag[expected[lhs]]
        if lhs=='N':want=want-1
        if parser.peek() is not None or value!=want:raise ValueError(('incorrect polynomial',lhs))
        variables[lhs]=value;seen.append(lhs)
    if seen!=list(expected):raise ValueError(('definitions',seen))
    box=re.search(r'\\boxed\{(.*?)\}',display,re.S)
    if not box or re.sub(r'\s+','',box.group(1))!='A^2+B^2+N^2+S^2=0.':
        raise ValueError('incorrect final sum')
    return len(seen)
text=(ROOT/'equation36.tex').read_text()
count=validate(text)
# Exact raw-environment controls: a bare alias and an inserted outside term.
raw_marker = 'The single Diophantine equation is'
start_raw = text.index(raw_marker)
raw_open = text.index(r'\[', start_raw) + len(r'\[')
outside_mutation = text[:raw_open] + '1+' + text[raw_open:]
mutations_raw = [outside_mutation]
if r'\mathcal{P}^2' in text[start_raw:]:
    mutations_raw.append(text[:start_raw] + text[start_raw:].replace(r'\mathcal{P}^2', 'resA^2', 1))
for mutation in mutations_raw:
    try: validate(mutation)
    except ValueError: pass
    else: raise ValueError('raw equation mutation was not detected')

for old,new in [('M=q^3b','M=q^2b'), ('-Q(\\upsilon^2-V^2)-1','+Q(\\upsilon^2-V^2)-1')]:
    if old not in text:raise ValueError('mutation site missing')
    try:validate(text.replace(old,new,1))
    except ValueError:pass
    else:raise ValueError('mutation was not detected')
rename={'r':'xi','i':'g','y':'upsilon','K0':'K','MC':'mu','MF':'omega',
        'qm':'b','Bt':'W','b0':'L','Dstar':'D','G':'rankseed'}
def fmt(x):return rename.get(str(x),str(x)).replace('_',r'\_')
lines=[line for line in text.splitlines() if line[:1].isdigit() and '. ' in line and ' = ' in line and line.endswith(r'\\')]
if len(lines)!=87:raise ValueError('rendered circuit count')
for idx,(line,(name,op,a,b)) in enumerate(zip(lines,c['source']),1):
    if line!=f'{idx}. {fmt(name)} = {fmt(a)} {op} {fmt(b)}'+r'\\':raise ValueError(('circuit row',idx))
old=(ROOT/'equation.tex').read_text();start=old.index(r'\textbf{The four fixed integers.}')
end=old.index(r'\endgroup',old.index(r'\textbf{The integer $\mathcal A$'))+len(r'\endgroup')
if old[start:end] not in text:raise ValueError('fixed constants differ')
print('PASS:',count,'parsed polynomial definitions; exact sum wiring; 87 circuit rows; fixed constants; two mutation controls')
