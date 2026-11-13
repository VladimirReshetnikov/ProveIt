#!/usr/bin/env python3
"""Generate and exactly check the beta>=2 AQ17-to-AQ16 elimination."""
from collections import Counter
from functools import lru_cache
import gzip,hashlib,json
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
P=ROOT/'research/aq22-positive-binding-survey/candidate17.json'
POLY=ROOT/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
PORT=ROOT/'reviews/aq22-pdf-historical-lean-binding-independent/receipt.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
parent=json.loads(P.read_text());carrier=json.loads(POLY.read_text());port=json.loads(PORT.read_text())
assert H(P)=='760b9e7babbb559b7175344915456fdc3d9bd8ce85382873d4915faf2cd76d81'
assert parent['fixed_numerals']==['beta','K0','MC','MF']
meta=carrier['coefficient_binding']['ports']['beta']; packed=(POLY.parent/'coefficients'/meta['file']).read_bytes()
assert hashlib.sha256(packed).hexdigest()==meta['gzip_sha256']
beta_bytes=gzip.decompress(packed);beta=int.from_bytes(beta_bytes,'big')
assert hashlib.sha256(beta_bytes).hexdigest()==meta['raw_sha256']==port['ports'][0]['integer_sha256'] and beta>=2
assert beta==(1<<94517)-1
rows={r[0]:r for r in parent['source']};assert rows['dDifference']==['dDifference','-','dValueVariable','DstarComputed']
factors=[x for x in parent['residuals'] if x!='dDifference']; assert len(factors)==7
replace={'dValueVariable':'DstarComputed'}
live=set();todo=list(factors)
while todo:
    n=todo.pop()
    if not isinstance(n,str):continue
    n=replace.get(n,n)
    if n in live:continue
    live.add(n)
    if n in rows:todo.extend(rows[n][2:])
source=[]
for n,op,a,b in parent['source']:
    if n in live:source.append([n,op,replace.get(a,a),replace.get(b,b)])
for i,n in enumerate(factors):source.append([f'aq16Square{i}','*',n,n])
prev='aq16Square0'
for i in range(1,len(factors)):
    target=f'aq16Sum{i}';source.append([target,'+',prev,f'aq16Square{i}']);prev=target
child={'scope':'Research candidate: beta>=2, exact finite arithmetic and ordinary positive witness reconstruction; no AQ16 Lean proof.',
       'witnesses':[n for n in parent['witnesses'] if n not in replace],
       'fixed_numerals':parent['fixed_numerals'],'source':source,'output':prev,'residuals':factors,
       'parent_sha256':H(P),'eliminated_bindings':replace,'port_hypotheses':{'beta_lower_bound':2}}
assert len(child['witnesses'])==len(set(child['witnesses']))==16
cr={r[0]:r for r in child['source']}; assert len(cr)==len(source)
# Symbolic sparse-polynomial arithmetic, with exponent vectors for witnesses and ports.
variables=child['witnesses']+child['fixed_numerals'];zero=(0,)*len(variables)
def add(a,b,sign=1):
    c=a.copy()
    for k,v in b.items():c[k]=c.get(k,0)+sign*v
    return {k:v for k,v in c.items() if v}
def mul(a,b):
    c={}
    for x,u in a.items():
        for y,v in b.items():
            k=tuple(i+j for i,j in zip(x,y));c[k]=c.get(k,0)+u*v
    return {k:v for k,v in c.items() if v}
def atom(n):
    k=list(zero);k[variables.index(n)]=1;return {tuple(k):1}
def evaluator(table,bindings):
    @lru_cache(None)
    def run(n):
        if isinstance(n,int):return {zero:n} if n else {}
        if n in bindings:return run(bindings[n])
        if n in variables:return atom(n)
        _,op,a,b=table[n];x=run(a);y=run(b)
        return add(x,y) if op=='+' else add(x,y,-1) if op=='-' else mul(x,y)
    return run
p=evaluator(rows,replace);c=evaluator(cr,{})
for n in parent['residuals']:assert p(n)==({} if n=='dDifference' else c(n)),n
# Dstar = U*(X+a*eta) + (U*a*Y-H)*k + H*(U*gamma+E*q+rank+1).
# Expand both sides independently, including integer subtraction, not truncated subtraction.
positive_first=mul(p('U'),add(atom('X'),mul(p('a'),atom('eta'))))
positive_coefficient=add(mul(mul(p('U'),p('a')),atom('Y')),p('H'),-1)
positive_last=mul(p('H'),add(add(add(mul(p('U'),atom('gamma')),mul(p('E'),p('q'))),atom('rankVariable')),{zero:1}))
assert p('DstarComputed')==add(add(positive_first,mul(positive_coefficient,p('k'))),positive_last)
# Expression-shape checks justify U*a*Y >= 9*a > 4*a+3=H
# for all positive assignments with beta>=2, not only sampled points.
for n,expected in {'q':['q','+',1,'qm'],'qm':['qm','*','J','beta'],'U':['U','*','Y','q2'],
                   'q2':['q2','*','q','q'],'a':['a','+','E','Y'],'E':['E','*','X','Y'],
                   'H':['H','+',3,'g15'],'g15':['g15','*',4,'a'],
                   'k':['k','+','eta','zeta']}.items():assert rows[n]==expected

def squares(table,out,expected):
    def go(n):
        _,op,a,b=table[n]
        if op=='+':return go(a)+go(b)
        assert op=='*' and a==b and a in expected
        return [a]
    assert Counter(go(out))==Counter(expected)
squares(rows,parent['output'],parent['residuals']);squares(cr,child['output'],factors)
degrees={n:max((sum(k[:16]) for k in c(n)),default=-1) for n in factors}
w={n:0 for n in variables};w.update(J=8,X=2,Y=4,eta=2,beta=8)
mon=tuple(w[n] for n in variables);coeff={k[16:]:v for k,v in c('A0').items() if k[:16]==mon[:16]}
assert degrees['A0']==max(degrees.values())==16 and coeff=={(8,0,0,0):-1}
# Mutation controls: wrong sign in reconstructed expression, residual and sum.
assert p('DstarComputed')!=add(add(positive_first,mul(positive_coefficient,p('k'))),positive_last,-1)
mut=dict(cr);mut['g61']=['g61','+','DstarComputed','DstarComputed'];bad=evaluator(mut,{})
assert bad('A1')!=p('A1')
mut=dict(cr);name=child['output'];mut[name]=[name,'-',mut[name][2],mut[name][3]]
try:squares(mut,name,factors)
except AssertionError:pass
else:raise AssertionError('output-sign mutation survived')
path=HERE/'candidate16.json';encoded=json.dumps(child,indent=2)+'\n'
if path.exists() and path.read_text()!=encoded:raise ValueError('refusing to overwrite changed candidate')
if not path.exists():path.write_text(encoded)
print('PASS_AQ16',len(child['witnesses']),'variables',len(source),'operations',len(factors),'squares degree',2*max(degrees.values()),'beta >= 2')
print('candidate_sha256',H(path));print('residual_degrees',json.dumps(degrees,sort_keys=True))
