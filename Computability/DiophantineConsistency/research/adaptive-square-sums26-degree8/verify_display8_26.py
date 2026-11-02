#!/usr/bin/env python3
"""Compare displayed degree-6 TeX and its circuit to exact sparse polynomials."""
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
parser_globals['commands'].update({'vartheta','psi','varphi','epsilon','delta','chi','theta','sigma','lambda','kappa','nu','tau'} | {'res'+chr(65+i) for i in range(26)} | {'resAA','resAB'})
raw=(D/'candidate.json').read_bytes()
if hashlib.sha256(raw).hexdigest()!='d8e80e15d74271ba62877e841198a85729c0c4a74a5927927591b9ec2204b1a5':raise ValueError('candidate pin')
c=json.loads(raw)
symbol_map=dict(base['symbol_map'],psi='scaleVariable',varphi='mainScaleVariable',epsilon='rankVariable',c='cVariable',ell='ellVariable',n='cSquareVariable',Z='zValueVariable',D='dValueVariable',V='vValueVariable',delta='deltaVariable',kappa='qSquareVariable',lambda_='productVariable2',Q='qValueVariable')
symbol_map['lambda']=symbol_map.pop('lambda_')
expected={'b':'qm','q':'q','C':'C','U':'U','a':'a','s':'q3','x':'g55','W':'Bt','m':'f2','sigma':'g39','nu':'y2','E':'productVariable2','k':'k',
 'tau':'g40','chi':'g62','H':'H','Delta':'deltaVariable','L':'b0','M':'M','R':'R','vartheta':'g80','I':'I',
 'resA':'A0',
 'resB':'A1',
 'resC':'auxResidual',
 'resD':'g72',
 'resF':'scaleDifference',
 'resG':'mainScaleDifference',
 'resH':'rankDifference',
 'resI':'cDifference',
 'resK':'ellDifference',
 'resP':'cSquareDifference',
 'resQ':'zDifference',
 'resR':'dDifference',
 'resS':'vDifference',
 'resT':'deltaDifference',
 'resU':'qSquareDifference',
 'resV':'product2Difference',
 'resAB':'qSignedDifference',
}

def validate(text):
    display=text[text.index('% BEGIN VERIFIED DISPLAY\n'):text.index('% END VERIFIED DISPLAY\n')]
    # The fixed decimal encoding uses calligraphic A outside this block.
    if r'\mathcal{A}' in display or r'\mathcal A' in display:
        raise ValueError('fixed-constant symbol reused in equation')
    # Pin the entire raw math environment before translating any residual aliases.
    marker = 'The single Diophantine equation is'
    if display.count(marker) != 1: raise ValueError('equation marker')
    section = display.split(marker, 1)[1]
    raw_equation = re.fullmatch(r'\s*\\\[(.*?)\\\]\s*', section, re.S)
    if not raw_equation or re.sub(r'\s+', '', raw_equation.group(1)) != '\\begin{split}\\mathcal{P}^2+\\mathcal{D}^2+\\mathcal{Q}^2+\\mathcal{R}^2+\\mathcal{B}^2+\\mathcal{C}^2+\\mathcal{G}^2&\\\\+\\mathcal{H}^2+\\mathcal{L}^2+\\mathcal{N}^2&\\\\+\\mathcal{I}^2+\\mathcal{J}^2+\\mathcal{K}^2+\\mathcal{O}^2+\\mathfrak{J}^2+\\mathcal{F}^2&\\\\+\\mathfrak{B}^2&=0.\\end{split}':
        raise ValueError('raw equation environment differs')
    unknowns=re.search(r'The only unknowns are the twenty-six separately named positive-integer variables\s*\\\[(.*?)\\in\\mathbb Z_\{>0\}\.\\end\{gathered\}\s*\\\]',display,re.S)
    if not unknowns:raise ValueError('unknown declaration')
    listed=[x.strip().lstrip('\\') for x in unknowns.group(1).replace(r'\begin{gathered}','').replace('\\\\','').split(',')]
    if listed!=['J','F','alpha','f','g','T','X','Y','xi','eta','zeta','upsilon','gamma','psi','varphi','epsilon','c','ell','n','Z','D','V','delta','kappa','lambda','Q'] or len(set(listed))!=26:
        raise ValueError('unknown names')
    for key,value in (('\\mathcal{P}','\\resA'),('\\mathcal{D}','\\resB'),('\\mathcal{Q}','\\resC'),('\\mathcal{R}','\\resD'),('\\mathcal{E}','\\resE'),('\\mathcal{B}','\\resF'),('\\mathcal{C}','\\resG'),('\\mathcal{G}','\\resH'),('\\mathcal{H}','\\resI'),('\\mathcal{T}','\\resJ'),('\\mathcal{L}','\\resK'),('\\mathcal{W}','\\resL'),('\\mathcal{X}','\\resM'),('\\mathcal{Y}','\\resN'),('\\mathcal{Z}','\\resO'),('\\mathcal{N}','\\resP'),('\\mathcal{I}','\\resQ'),('\\mathcal{J}','\\resR'),('\\mathcal{K}','\\resS'),('\\mathcal{O}','\\resT'),('\\mathfrak{J}','\\resU'),('\\mathcal{F}','\\resV'),('\\mathcal{M}','\\resW'),('\\mathcal{S}','\\resX'),('\\mathcal{U}','\\resY'),('\\mathcal{V}','\\resZ'),('\\mathfrak{A}','\\resAA'),('\\mathfrak{B}','\\resAB')):
        display=display.replace(key,value)
    group=re.search(r'\\begin\{gathered\}(.*?)\\end\{gathered\}',display[unknowns.end():],re.S)
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
    wiring=re.sub(r'\s+','',box.group(1)).replace('&','').replace('\\\\','').replace('\\','')
    if wiring!='resA^2+resB^2+resC^2+resD^2+resF^2+resG^2+resH^2+resI^2+resK^2+resP^2+resQ^2+resR^2+resS^2+resT^2+resU^2+resV^2+resAB^2=0.':raise ValueError(('sum wiring',wiring))
    return len(seen)
text=(D/'equation8-26.tex').read_text();count=validate(text)
# Exact raw-environment controls: a bare alias and an inserted outside term.
raw_marker = 'The single Diophantine equation is'
start_raw = text.index(raw_marker)
raw_open = text.index(r'\[', start_raw) + len(r'\[')
outside_mutation = text[:raw_open] + '1+' + text[raw_open:]
mutations_raw = [outside_mutation]
mutations_raw.append(text.replace(r'\mathfrak{J}=', r'\mathcal{A}=', 1))
if r'\mathcal{P}^2' in text[start_raw:]:
    mutations_raw.append(text[:start_raw] + text[start_raw:].replace(r'\mathcal{P}^2', 'resA^2', 1))
for mutation in mutations_raw:
    try: validate(mutation)
    except ValueError: pass
    else: raise ValueError('raw equation mutation was not detected')

for old,new in [('M=sb','M=s+b'),(r'\epsilon-R',r'\epsilon+R')]:
    if old not in text:raise ValueError('mutation site missing')
    try:validate(text.replace(old,new,1))
    except ValueError:pass
    else:raise ValueError('undetected mutation')
rename={'r':'xi','i':'g','y':'upsilon','K0':'K','MC':'mu','MF':'omega',
        'qm':'b','Bt':'WComputed','b0':'L','Dstar':'D','G':'rankseed','squareVariable':'vartheta','scaleVariable':'psi','mainScaleVariable':'varphi','rankVariable':'epsilon','cVariable':'cNamed','aVariable':'aNamed','ellVariable':'ellNamed','wValueVariable':'WNamed','cubeVariable':'s','productVariable':'x','f2':'m','cSquareVariable':'n','zValueVariable':'Z','dValueVariable':'D','vValueVariable':'V','deltaVariable':'delta','qSquareVariable':'kappa','productVariable2':'lambda','psiSquareVariable':'sigma','ellProductVariable':'tau','varphiSquareVariable':'chi','scaledIndexVariable':'theta','ySquareVariable':'nu','qValueVariable':'Q','rankDifference':'rankDiff','rankConstraint':'rankCheck','finalWithRank':'result17','mainScaleDifference':'mainDiff','mainScaleConstraint':'mainCheck','finalWithMainScale':'result16','scaleDifference':'scaleDiff','scaleConstraint':'scaleCheck','finalWithScale':'final','squareConstraint':'constraint','squareDifference':'difference','sumWithConstraint':'result'}
def fmt(x):return rename.get(str(x),str(x)).replace('_',r'\_')
lines=[line for line in text.splitlines() if line[:1].isdigit() and '. ' in line and ' = ' in line and line.endswith(r'\\')]
if len(lines)!=126:raise ValueError('gate count')
for i,(line,(name,op,a,b)) in enumerate(zip(lines,c['source']),1):
    if line!=f'{i}. {fmt(name)} = {fmt(a)} {op} {fmt(b)}'+r'\\':raise ValueError(('gate',i))
old=(ROOT/'equation.tex').read_text();start=old.index(r'\textbf{The four fixed integers.}')
end=old.index(r'\endgroup',old.index(r'\textbf{The integer $\mathcal A$'))+len(r'\endgroup')
if old[start:end] not in text:raise ValueError('fixed constants differ')
print('PASS:',count,'display definitions; seventeen-square wiring; 126 circuit rows; fixed constants; two mutation controls')
