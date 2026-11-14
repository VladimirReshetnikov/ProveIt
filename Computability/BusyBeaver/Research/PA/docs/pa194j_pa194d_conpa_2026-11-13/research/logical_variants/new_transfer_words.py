#!/usr/bin/env python3
"""Exact 190- and 191-token AX words for new diagonal-head transfers.

Scratch research, not a literal TM certificate. Checks complete emitter effect
in an independent free term algebra, and compares baseline to archived PA194.
"""
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parent
GRAMMAR=ROOT.parents[1]/'construction/inputs/pa194.grammar.json'
TOKENS={'node49':['push'],'node55':['copyD'],'node58':['copyH'],
        'node70':['copyA'],'node65':['cons'],'node72':['readH'],
        'node75':['readDCons'],'node142':['copyGuard'],'node150':['compareGuard'],
        'node60':['incT']*2,'node61':['incT']*4}
SHORT={'push':'P','copyD':'D','copyH':'H','copyA':'A','cons':'C','incT':'i',
       'readH':'r','readDCons':'s','copyGuard':'g','compareGuard':'j','close':'z'}
NODE={v[0]:k for k,v in TOKENS.items() if len(v)==1}
NODE['incT']=['leaf','inc',1]
NODE['close']=['leaf','breakTo',1]

def decode_grammar(path):
    data=json.loads(path.read_text()); rules=data['rules']
    def rec(x):
        if isinstance(x,str):
            return TOKENS[x] if x in TOKENS else rec(rules[x])
        if x==['leaf','inc',1]:return ['incT']
        if x==['leaf','breakTo',1]:return ['close']
        assert len(x)==2,x
        return rec(x[0])+rec(x[1])
    return rec(data['root'])

# Formula trees keep raw I=4pair and successor tags separate in the verifier.
def I(a,b):return (0,a,b)
def M(a,b):return (1,a,b)
def U(a,b):return (2,b,a)
def E(a,b):return (3,a,b)
def N(a):return I(a,1)
def And(a,b):return N(I(a,N(b)))
def Ex(a,b):return N(U(a,N(b)))
def Gamma(a):return I(a,U(a,a))
def emit(x):
    if isinstance(x,str):return ['copy'+x]
    if isinstance(x,int):return ['push']+['incT']*x
    r,a,b=x
    return emit(a)+emit(b)+['cons']+['incT']*r

def source_formulae():
    A,D,H='ADH'
    heads=[I(Ex(D,U(D,H)),H),I(U(D,U(A,H)),U(A,U(D,H))),
           I(M(H,D),I(E(H,A),M(A,D))),I(E(H,D),I(M(A,H),M(A,D))),
           Ex(D,E(H,D)),I(U(D,A),I(U(D,I(A,H)),U(D,H)))]
    point=I(A,M(A,D)); V=I(M(H,D),U(A,M(H,D)))
    S=U(D,And(I(M(H,D),point),I(M(A,D),A)))
    Q=U(A,I(S,N(point)))
    return heads,N(I(V,Q))

HEADS,GATE=source_formulae()
BASE=decode_grammar(GRAMMAR)
TAIL=sum((emit(x) for x in HEADS+[Gamma('A'),GATE]),[])+['copyGuard','compareGuard','close']
assert BASE[-len(TAIL):]==TAIL
PREFIX=BASE[:-len(TAIL)]


def formulas(variant):
    heads=list(HEADS)
    A,D,H='ADH'
    if variant=='h1D':heads[0]=I(I(Gamma(D),Ex(D,U(D,H))),H)
    elif variant=='h2D':heads[1]=I(I(Gamma(D),U(D,U(A,H))),U(A,U(D,H)))
    elif variant=='h6outerD':heads[5]=I(I(Gamma(D),U(D,A)),I(U(D,I(A,H)),U(D,H)))
    # Reference controls: h1A, h2A and h6innerD already appear in corpus.
    elif variant=='h1A':heads[0]=I(I(Gamma(A),Ex(D,U(D,H))),H)
    elif variant=='h2A':heads[1]=I(I(Gamma(A),U(D,U(A,H))),U(A,U(D,H)))
    elif variant=='h6innerD':heads[5]=I(U(D,A),I(I(Gamma(D),U(D,I(A,H))),U(D,H)))
    elif variant=='separateD':heads.append(Gamma(D))
    elif variant=='separateH':heads.append(Gamma(H))
    else:raise ValueError(variant)
    return heads,GATE

ZERO=('zero',)
def SUCC(x):return ('succ',x)
def RAWI(a,b):return ('I',a,b)
def raw_expr(x,env):
    if isinstance(x,str):return env[x]
    if isinstance(x,int):
        out=ZERO
        for _ in range(x):out=SUCC(out)
        return out
    r,a,b=x
    out=RAWI(raw_expr(a,env),raw_expr(b,env))
    for _ in range(r):out=SUCC(out)
    return out


def check(word,heads,gate):
    t,a,d,h,x,y=[('parameter',v) for v in ['t','a','d','h','x','y']]
    top,D,H,stack=t,d,h,[]
    fields=iter((y,x));reads=[]
    for token in word[:-3]:
        if token=='push':stack.append(top);top=ZERO
        elif token in ('copyD','copyH','copyA'):
            stack.append(top);top={'copyD':D,'copyH':H,'copyA':a}[token]
        elif token=='incT':top=SUCC(top)
        elif token=='cons':top=RAWI(stack.pop(),top)
        elif token=='readH':
            z=next(fields);reads.append(z);H=('add',H,z)
        elif token=='readDCons':
            z=next(fields);reads.append(z);D=('add',D,z);top=RAWI(top,D)
        else:raise ValueError(token)
    env={'A':a,'D':D,'H':H}
    rho=RAWI(RAWI(RAWI(H,d),D),RAWI(RAWI(D,H),RAWI(a,H)))
    gen=SUCC(SUCC(RAWI(h,d)))
    expected=[t,gen,rho]+[raw_expr(x,env) for x in heads]
    assert stack==expected,(stack,expected)
    assert top==raw_expr(gate,env)
    assert reads==[y,x]
    assert word[-3:]==['copyGuard','compareGuard','close']
    assert len(stack)==len(heads)+3
    return {'tokens':len(word),'pushed_items':len(heads)+3,'complete_stack':True,
            'complete_gate':True,'unchanged_guard_and_parameter_reads':True,
            'all_parameters_symbolic':True}


def left_association(tokens):
    nodes=[NODE[x] for x in tokens]
    t=nodes[0]
    for x in nodes[1:]:t=[t,x]
    return {'root':'root','rules':{'root':t}}


def main():
    records=[]
    for name in ['h1D','h2D','h6outerD','h1A','h2A','h6innerD','separateD','separateH']:
        heads,gate=formulas(name)
        word=PREFIX+sum((emit(x) for x in heads+[gate]),[])+['copyGuard','compareGuard','close']
        assert len(word)==(190 if name.startswith('separate') else 191)
        receipt=check(word,heads,gate)
        record={'variant':name,'novel_relative_to_inspected_corpus':name in ['h1D','h2D','h6outerD','separateD','separateH'],
                'word':word,'short_word':''.join(SHORT[x] for x in word),
                'node_word':[NODE[x] for x in word],'heads':heads,'gate':gate,'check':receipt}
        records.append(record)
        (ROOT/(name+'.word.json')).write_text(json.dumps(record,indent=2)+'\n')
        (ROOT/(name+'.tokens.txt')).write_text(record['short_word']+'\n')
    (ROOT/'transfer_words.json').write_text(json.dumps(records,indent=2)+'\n')
    print(json.dumps({'baseline_tokens':len(BASE),'prefix':PREFIX,'variants':[
        {'name':r['variant'],**r['check']} for r in records]},indent=2))

if __name__=='__main__':main()
