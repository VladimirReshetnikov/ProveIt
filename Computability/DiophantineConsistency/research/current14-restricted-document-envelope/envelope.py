"""Exact wrapper and restricted hole lexer; no mathematical interpretation."""
from pathlib import Path
import json, re
D=Path('research/current14-restricted-document-envelope')
DATA=json.loads((D/'envelope.json').read_text())
NAMES=DATA['names']; FRAGMENTS=DATA['fragments']
MATH_WORDS=set('Delta Lambda Phi Pi alpha beta bmod cap chi ell eta fl frac gamma hline in kappa le mathcal mathbb mu nu omega pi prod qquad quad rg rho sigma substack sum tau text zeta begin end arraycolsep setlength'.split())
SYMBOLS=set('\\[]{} ,;!')
ENVIRONMENTS={'gathered','align*','split','array'}

def check_math(text):
    if not text or '^^' in text or '%' in text or '~' in text: return False
    if any(ord(c)>126 or (ord(c)<32 and c not in '\n\r\t') for c in text): return False
    i=0; stack=[]
    while i<len(text):
        if text[i]!='\\': i+=1; continue
        i+=1
        if i==len(text): return False
        if text[i].isalpha() and text[i].isascii():
            start=i
            while i<len(text) and text[i].isascii() and text[i].isalpha(): i+=1
            word=text[start:i]
            if word not in MATH_WORDS: return False
            if word=='setlength':
                fixed=r'{\arraycolsep}{1.4pt}'
                if not text.startswith(fixed,i): return False
                i+=len(fixed)
            if word in ('begin','end'):
                m=re.match(r'\{([^{}]+)\}',text[i:])
                if not m or m[1] not in ENVIRONMENTS:return False
                if word=='begin': stack.append(m[1])
                elif not stack or stack.pop()!=m[1]: return False
                i+=len(m[0])
        else:
            if text[i] not in SYMBOLS:return False
            i+=1
    return not stack

def check_seed(text):
    return re.fullmatch(r'(?:[0-9]{1,100}\\par\n){12}',text) is not None

def extract(data):
    """Return only actual delimited source regions, or None on envelope failure."""
    if not isinstance(data,str) or not data.startswith(FRAGMENTS[0]):return None
    position=len(FRAGMENTS[0]); holes=[]
    for following in FRAGMENTS[1:]:
        end=data.find(following,position)
        if end<0 or data.find(following,end+1)>=0:return None
        holes.append(data[position:end]); position=end+len(following)
    if position!=len(data) or len(holes)!=len(NAMES):return None
    if not all(check_math(x) for x in holes[:-1]) or not check_seed(holes[-1]):return None
    return dict(zip(NAMES,holes))
