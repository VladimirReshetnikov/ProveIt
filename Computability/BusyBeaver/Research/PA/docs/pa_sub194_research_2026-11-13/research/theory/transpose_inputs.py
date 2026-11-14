#!/usr/bin/env python3
"""Generate exact 190-token atomic-orientation AX search seeds.

The generated words are explicit formula emitters, not certified machines.
Every new seed preserves the baseline binary association occurrence by
occurrence while substituting the new equal-length word.
"""
from pathlib import Path
import argparse, hashlib, itertools, json
from types import SimpleNamespace

HERE=Path(__file__).resolve().parent
def isnode(t):return isinstance(t,tuple) and len(t)==2
def read_grammar(path):
    data=json.loads(Path(path).read_text());rules=data['rules']
    def rec(x):
        if isinstance(x,list):return tuple(x)
        if x in rules:return tuple(rec(y) for y in rules[x])
        return x
    return rec(data['root'])
def expanded(t):
    inc=('leaf','inc',1)
    if t=='node60':return inc,inc
    if t=='node61':return (inc,inc),(inc,inc)
    return tuple(map(expanded,t)) if isnode(t) else t
def word(t):return word(t[0])+word(t[1]) if isnode(t) else [t]
MACROS={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,
        'node72':69,'node75':213,'node142':194,'node150':221,
        ('leaf','inc',1):61,'node60':99,'node61':190}
c=SimpleNamespace(isnode=isnode,read_grammar=read_grammar,MACROS=MACROS,BREAK=('leaf','breakTo',1))
b=SimpleNamespace(expanded=expanded,word=word)
INC=('leaf','inc',1)
TOK={'D':'node55','H':'node58','A':'node70'}
ONE='1'
def I(a,b):return (0,a,b)
def M(a,b):return (1,a,b)
def U(a,b):return (2,b,a)
def E(a,b):return (3,a,b)
def N(a):return I(a,ONE)
def AND(a,b):return N(I(a,N(b)))
def EX(a,b):return N(U(a,N(b)))
def orient(f,mode):
    if isinstance(f,str):return f
    tag,a,d=f
    a,d=orient(a,mode),orient(d,mode)
    if (tag==3 and mode&1) or (tag==1 and mode&2):a,d=d,a
    return tag,a,d
def emit(f):
    if isinstance(f,str):return ['node49',INC] if f==ONE else [TOK[f]]
    tag,a,d=f
    return emit(a)+emit(d)+['node65']+[INC]*tag
def heads(flags):
    d,h,a='DHA'
    hs=[I(EX(d,U(d,h)),h),I(U(d,U(a,h)),U(a,U(d,h))),
        I(M(h,d),I(E(h,a),M(a,d))),
        I(E(h,d),I(M(a,h),M(a,d))),EX(d,E(h,d)),
        I(U(d,a),I(U(d,I(a,h)),U(d,h)))]
    for bit,j in enumerate([2,3,5]):
        if flags>>bit&1:
            _,x,(_,y,z)=hs[j]
            hs[j]=I(y,I(x,z))
    return hs
def gate(commute,swap):
    a,d,p='HDA'
    v=I(M(a,d),U(p,M(a,d)))
    point=I(p,M(p,d))
    left=I(p,I(M(a,d),M(p,d))) if commute else I(M(a,d),I(p,M(p,d)))
    right=I(M(p,d),p)
    matrix=AND(right,left) if swap else AND(left,right)
    sep=U(d,matrix)
    return N(I(v,U(p,I(sep,N(point)))))
def replace_word(tree,word):
    it=iter(word)
    def walk(t):
        if c.isnode(t):return walk(t[0]),walk(t[1])
        return next(it)
    result=walk(tree)
    assert next(it,None) is None
    return result
def grammar(tree):
    ids={};rules={}
    def visit(t):
        if not c.isnode(t):return t
        if t not in ids:
            a,d=visit(t[0]),visit(t[1]);k='g'+str(len(ids))
            ids[t]=k;rules[k]=[a,d]
        return ids[t]
    root=visit(tree)
    return {'root':root,'rules':rules}
def serialize(tree):
    ns=[];ix={}
    def visit(t):
        if t in ix:return ix[t]
        if c.isnode(t):row=(1,visit(t[0]),visit(t[1]),0)
        else:row=(0,-1 if t==c.BREAK else c.MACROS[t],-1,-1)
        i=len(ns);ix[t]=i;ns.append(row);return i
    root=visit(tree)
    return ns,root
def main(output):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    tree=b.expanded(c.read_grammar(HERE/'baseline.grammar.json'))
    word=b.word(tree)
    gamma=I('A',U('A','A'))
    assert sum((emit(h) for h in heads(0)),[])==word[18:121]
    assert emit(gamma)==word[121:128]
    assert emit(gate(0,0))==word[128:-3]
    lines=(HERE/'fixed_readers.txt').read_text().splitlines()
    fixed=lines[:int(lines[0])+1]
    metadata=[]
    for mode in range(4):
        templates=[]
        for exchange,commute,swap in itertools.product(range(8),range(2),range(2)):
            newword=word[:18]+sum((emit(orient(h,mode)) for h in heads(exchange)),[])+emit(gamma)+emit(orient(gate(commute,swap),mode))+word[-3:]
            assert len(newword)==190
            t=replace_word(tree,newword)
            ns,root=serialize(t)
            meta={'id':len(templates),'mode':mode,'exchange':exchange,'commute':commute,'swap':swap,
                  'word_sha256':hashlib.sha256(json.dumps(newword,separators=(',',':')).encode()).hexdigest()}
            metadata.append(meta);templates.append((ns,root))
        out=fixed+[str(len(templates))]
        for i,(ns,root) in enumerate(templates):
            out.append(f'{i} {len(ns)} {root}')
            out+=[' '.join(map(str,row)) for row in ns]
        (output/f'mode{mode}.txt').write_text('\n'.join(out)+'\n')
    (output/'transpose_inputs.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps({'modes':4,'variants_per_mode':32,'tokens':190,'exact_baseline_emitter_agrees':True}))
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=HERE)
    main(parser.parse_args().output)
