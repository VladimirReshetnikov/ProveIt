#!/usr/bin/env python3
"""Compare displayed degree-30 TeX and its circuit to exact sparse polynomials."""
import hashlib
import json
from pathlib import Path
import re
import runpy
D=Path(__file__).resolve().parent
ROOT=D.parents[1]
degree=runpy.run_path(str(D/'verify_degree.py'))
base=runpy.run_path(str(D.parent/'adaptive-direct-ordinate86/verify_display_tex86.py'))
P=degree['P'];g=degree['g'];Parser=base['Parser']
def power(self,n):
    r=P.lift(1)
    for _ in range(n):r=r*self
    return r
P.__pow__=power
P.__radd__=P.__add__
P.__rmul__=P.__mul__
P.__rsub__=lambda self,x:P.lift(x)-self
parser_globals=Parser.expression.__globals__
parser_globals['Poly']=P
parser_globals['commands'].update({'vartheta','psi','varphi'})
raw=(D/'candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='bfb13952920a218bb13b168006f19d2d1a29eaf184077cee319cf323472d44cc':raise ValueError('candidate pin')
c=json.loads(raw)
symbol_map=dict(base['symbol_map'],vartheta='squareVariable',psi='scaleVariable',varphi='mainScaleVariable')
expected={'b':'qm','q':'q','C':'C','U':'U','E':'E','k':'k','ell':'ell','c':'c',
          'a':'a','H':'H','Delta':'Delta','L':'b0','M':'M','W':'Bt','R':'R',
          'Z':'Z','D':'Dstar','I':'I','Q':'Q','V':'V','A':'A0','B':'A1',
          'N':'auxResidual','S':'g72','O':'squareDifference','G':'scaleDifference','h':'mainScaleDifference'}
def validate(text):
    display=text[text.index('% BEGIN VERIFIED DISPLAY\n'):text.index('% END VERIFIED DISPLAY\n')]
    # Pin the entire raw math environment before translating any residual aliases.
    marker = 'The single Diophantine equation is'
    if display.count(marker) != 1: raise ValueError('equation marker')
    section = display.split(marker, 1)[1]
    raw_equation = re.fullmatch(r'\s*\\\[(.*?)\\\]\s*', section, re.S)
    if not raw_equation or re.sub(r'\s+', '', raw_equation.group(1)) != '\\boxed{\\mathcal{P}^2+\\mathcal{D}^2+\\mathcal{Q}^2+\\mathcal{R}^2+\\mathcal{E}^2+\\mathcal{B}^2+\\mathcal{C}^2=0.}':
        raise ValueError('raw equation environment differs')
    unknowns=re.search(r'The only unknowns are the sixteen separately named positive-integer variables\s*\\\[(.*?)\\in\\mathbb Z_\{>0\}\.\s*\\\]',display,re.S)
    if not unknowns:raise ValueError('unknown declaration')
    listed=[x.strip().lstrip('\\') for x in unknowns.group(1).split(',')]
    if listed!=['J','F','alpha','f','g','T','X','Y','xi','eta','zeta','upsilon','gamma','vartheta','psi','varphi'] or len(set(listed))!=16:
        raise ValueError('unknown names')
    for key,value in ((r'\mathcal{P}','A'),(r'\mathcal{D}','B'),(r'\mathcal{Q}','N'),(r'\mathcal{R}','S'),(r'\mathcal{E}','O'),(r'\mathcal{B}','G'),(r'\mathcal{C}','h')):
        display=display.replace(key,value)
    group=re.search(r'\\begin\{gathered\}(.*?)\\end\{gathered\}',display,re.S)
    if not group:raise ValueError('definitions')
    body=group.group(1).strip()
    if not body.endswith('.'):raise ValueError('punctuation')
    defs=[x.strip() for x in body[:-1].replace(r'\quad','').replace('\\\\',',').split(',') if x.strip()]
    variables={printed:g[internal] for printed,internal in symbol_map.items()};seen=[]
    for definition in defs:
        parser=Parser(definition,variables);lhs=parser.take()
        if lhs not in expected or lhs in seen or parser.take()!='=':raise ValueError(('definition',definition))
        value=parser.expression()
        if parser.peek() is not None or value!=g[expected[lhs]]:raise ValueError(('polynomial',lhs))
        variables[lhs]=value;seen.append(lhs)
    if seen!=list(expected):raise ValueError(('definition list',seen))
    box=re.search(r'\\boxed\{(.*?)\}',display,re.S)
    if not box or re.sub(r'\s+','',box.group(1))!='A^2+B^2+N^2+S^2+O^2+G^2+h^2=0.':raise ValueError('sum wiring')
    return len(seen)
text=(ROOT/'equation24.tex').read_text();count=validate(text)
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

for old,new in [('M=q^3b','M=q^2b'),(r'\varphi-U',r'\varphi+U')]:
    if old not in text:raise ValueError('mutation site missing')
    try:validate(text.replace(old,new,1))
    except ValueError:pass
    else:raise ValueError('undetected mutation')
rename={'r':'xi','i':'g','y':'upsilon','K0':'K','MC':'mu','MF':'omega',
        'qm':'b','Bt':'W','b0':'L','Dstar':'D','G':'rankseed','squareVariable':'vartheta','scaleVariable':'psi','mainScaleVariable':'varphi','mainScaleDifference':'mainDiff','mainScaleConstraint':'mainCheck','finalWithMainScale':'result16','scaleDifference':'scaleDiff','scaleConstraint':'scaleCheck','finalWithScale':'final','squareConstraint':'constraint','squareDifference':'difference','sumWithConstraint':'result'}
def fmt(x):return rename.get(str(x),str(x)).replace('_',r'\_')
lines=[line for line in text.splitlines() if line[:1].isdigit() and '. ' in line and ' = ' in line and line.endswith(r'\\')]
if len(lines)!=96:raise ValueError('gate count')
for i,(line,(name,op,a,b)) in enumerate(zip(lines,c['source']),1):
    if line!=f'{i}. {fmt(name)} = {fmt(a)} {op} {fmt(b)}'+r'\\':raise ValueError(('gate',i))
old=(ROOT/'equation.tex').read_text();start=old.index(r'\textbf{The four fixed integers.}')
end=old.index(r'\endgroup',old.index(r'\textbf{The integer $\mathcal A$'))+len(r'\endgroup')
if old[start:end] not in text:raise ValueError('fixed constants differ')
print('PASS:',count,'display definitions; seven-square wiring; 96 circuit rows; fixed constants; two mutation controls')
