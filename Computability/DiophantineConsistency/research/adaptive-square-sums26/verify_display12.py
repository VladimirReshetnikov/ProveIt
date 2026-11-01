#!/usr/bin/env python3
"""Compare displayed degree-12 TeX and its circuit to exact sparse polynomials."""
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
parser_globals['commands'].update({'vartheta','psi','varphi','epsilon'})
raw=(D/'candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='4f321364aa9d7fdf91263e174841bb48a441532cce6b8e95b9dc22c4ebc5718a':raise ValueError('candidate pin')
c=json.loads(raw)
symbol_map=dict(base['symbol_map'],vartheta='squareVariable',psi='scaleVariable',varphi='mainScaleVariable',epsilon='rankVariable',c='cVariable',a='aVariable',ell='ellVariable',h='wPositive',t='wNegative',s='cubeVariable',x='productVariable',m='fSquareVariable',n='cSquareVariable')
expected={'b':'qm','q':'q','C':'C','U':'U','E':'E','k':'k','W':'namedBt',
          'H':'H','Delta':'Delta','L':'b0','M':'M','R':'R',
          'Z':'Z','D':'Dstar','I':'I','Q':'Q','V':'V','A':'A0','B':'A1',
          'N':'auxResidual','S':'g72','O':'squareDifference','G':'scaleDifference',
          'u':'mainScaleDifference','v':'rankDifference','d':'cDifference',
          'j':'aDifference','o':'ellDifference','z':'wDifference', 'p':'cubeDifference','w':'productDifference','y':'fSquareDifference','l':'cSquareDifference'}

def validate(text):
    display=text[text.index('% BEGIN VERIFIED DISPLAY\n'):text.index('% END VERIFIED DISPLAY\n')]
    unknowns=re.search(r'The only unknowns are the twenty-six distinct positive integers\s*\\\[(.*?)\\in\\mathbb Z_\{>0\}\.\s*\\\]',display,re.S)
    if not unknowns:raise ValueError('unknown declaration')
    listed=[x.strip().lstrip('\\') for x in unknowns.group(1).split(',')]
    if listed!=['J','F','alpha','f','g','T','X','Y','xi','eta','zeta','upsilon','gamma','vartheta','psi','varphi','epsilon','c','a','ell','h','t','s','x','m','n'] or len(set(listed))!=26:
        raise ValueError('unknown names')
    for key,value in ((r'\mathcal{P}','A'),(r'\mathcal{D}','B'),(r'\mathcal{Q}','N'),(r'\mathcal{R}','S'),(r'\mathcal{E}','O'),(r'\mathcal{B}','G'),(r'\mathcal{C}','u'),(r'\mathcal{G}','v'),(r'\mathcal{H}','d'),(r'\mathcal{T}','j'),(r'\mathcal{L}','o'),(r'\mathcal{W}','z'),(r'\mathcal{X}','p'),(r'\mathcal{Y}','w'),(r'\mathcal{Z}','y'),(r'\mathcal{N}','l')):
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
    box=re.search(r'\\begin\{split\}(.*?)\\end\{split\}',display,re.S)
    if not box:raise ValueError('sum display')
    wiring=re.sub(r'\s+','',box.group(1)).replace('&','').replace('\\\\','')
    if wiring!='A^2+B^2+N^2+S^2+O^2+G^2+u^2+v^2+d^2+j^2+o^2+z^2+p^2+w^2+y^2+l^2=0.':raise ValueError(('sum wiring',wiring))
    return len(seen)
text=(ROOT/'equation12.tex').read_text();count=validate(text)
for old,new in [('M=sb','M=s+b'),(r'\epsilon-R',r'\epsilon+R')]:
    if old not in text:raise ValueError('mutation site missing')
    try:validate(text.replace(old,new,1))
    except ValueError:pass
    else:raise ValueError('undetected mutation')
rename={'r':'xi','i':'g','y':'upsilon','K0':'K','MC':'mu','MF':'omega',
        'qm':'b','Bt':'W','b0':'L','Dstar':'D','G':'rankseed','squareVariable':'vartheta','scaleVariable':'psi','mainScaleVariable':'varphi','rankVariable':'epsilon','cVariable':'cNamed','aVariable':'aNamed','ellVariable':'ellNamed','wPositive':'h','wNegative':'t','namedBt':'WNamed','cubeVariable':'s','productVariable':'x','fSquareVariable':'m','cSquareVariable':'n','rankDifference':'rankDiff','rankConstraint':'rankCheck','finalWithRank':'result17','mainScaleDifference':'mainDiff','mainScaleConstraint':'mainCheck','finalWithMainScale':'result16','scaleDifference':'scaleDiff','scaleConstraint':'scaleCheck','finalWithScale':'final','squareConstraint':'constraint','squareDifference':'difference','sumWithConstraint':'result'}
def fmt(x):return rename.get(str(x),str(x)).replace('_',r'\_')
lines=[line for line in text.splitlines() if line[:1].isdigit() and '. ' in line and ' = ' in line and line.endswith(r'\\')]
if len(lines)!=124:raise ValueError('gate count')
for i,(line,(name,op,a,b)) in enumerate(zip(lines,c['source']),1):
    if line!=f'{i}. {fmt(name)} = {fmt(a)} {op} {fmt(b)}'+r'\\':raise ValueError(('gate',i))
old=(ROOT/'equation.tex').read_text();start=old.index(r'\textbf{The four fixed integers.}')
end=old.index(r'\endgroup',old.index(r'\textbf{The integer $\mathcal A$'))+len(r'\endgroup')
if old[start:end] not in text:raise ValueError('fixed constants differ')
print('PASS:',count,'display definitions; sixteen-square wiring; 124 circuit rows; fixed constants; two mutation controls')
