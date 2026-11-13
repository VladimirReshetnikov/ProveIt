"""Independent accepted-envelope recognizer for the concrete frozen wrapper.

This is a Python executable specification, not a Lean inductive relation.
"""
import re, json
from pathlib import Path
DATA=json.loads(Path("research/current14-restricted-document-envelope/envelope.json").read_text())
WORDS=set('Delta Lambda Phi Pi alpha beta bmod cap chi ell eta fl frac gamma hline in kappa le mathcal mathbb mu nu omega pi prod qquad quad rg rho sigma substack sum tau text zeta begin end arraycolsep setlength'.split())
SYMBOLS=set('\\[]{} ,;!')
ENVS={'gathered','align*','split','array'}
CONTROL=re.compile(r'\\([A-Za-z]+|[^A-Za-z])')

def allowed(h):
    if not h or '^^' in h or any(c in h for c in '%~'):return False
    if any(not (c in '\n\r\t' or 32<=ord(c)<=126) for c in h):return False
    commands=list(CONTROL.finditer(h))
    covered={i for m in commands for i in range(m.start(),m.end())}
    if any(c=='\\' and i not in covered for i,c in enumerate(h)):return False
    stack=[]
    for m in commands:
        t=m[1]
        if (len(t)==1 and not t.isalpha() and t not in SYMBOLS) or (t.isalpha() and t not in WORDS):return False
        if t=='setlength' and not h[m.end():].startswith(r'{\arraycolsep}{1.4pt}'):return False
        if t in ('begin','end'):
            g=re.match(r'\{([^{}]+)\}',h[m.end():])
            if not g or g[1] not in ENVS:return False
            if t=='begin': stack.append(g[1])
            elif not stack or stack.pop()!=g[1]:return False
    return not stack

def accepted(document, holes):
    """Relation: same six source holes, unique boundaries, allowed hole lexemes."""
    if not isinstance(document,str) or len(holes)!=6:return False
    fs=DATA['fragments']; assembled=fs[0]
    for h,f in zip(holes,fs[1:]):assembled+=h+f
    if assembled!=document:return False
    pos=len(fs[0])
    for h,f in zip(holes,fs[1:]):
        if document.find(f,pos)!=pos+len(h) or document.find(f,pos+len(h)+1)>=0:return False
        pos+=len(h)+len(f)
    if not all(allowed(h) for h in holes[:-1]):return False
    return re.fullmatch(r'(?:[0-9]{1,100}\\par\n){12}',holes[-1]) is not None
