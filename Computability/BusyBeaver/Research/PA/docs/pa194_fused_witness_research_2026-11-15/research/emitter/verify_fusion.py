#!/usr/bin/env python3
"""Independently check the complete PA194FW AX emitter as a free-term identity.

No finite numerical substitution stands in for the arbitrary six parameters.
The atom contracts are inherited; physical execution is checked separately.
"""
import argparse, hashlib, json
from pathlib import Path

Z=('zero',)
def S(x):return ('S',x)
ONE=S(Z)
def I(x,y):return ('I',x,y)
def U(i,b):return S(S(I(b,i)))
def M(x,y):return S(I(x,y))
def E(x,y):return S(S(S(I(x,y))))
def N(x):return I(x,ONE)
def And(x,y):return N(I(x,N(y)))
def Ex(i,b):return N(U(i,N(b)))
TOKENS={'node49':['push'],'node55':['copyD'],'node58':['copyH'],
        'node70':['copyA'],'node65':['cons'],'node72':['readH'],
        'node75':['readDCons'],'node142':['copyGuard'],
        'node150':['compareGuard'],'node60':['incT']*2,'node61':['incT']*4}
def need(x,msg):
    if not x:raise ValueError(msg)
def flatten(t):
    if isinstance(t,str):return TOKENS[t]
    if t==['leaf','inc',1]:return ['incT']
    need(isinstance(t,list) and len(t)==2,'unrecognized syntax atom')
    return flatten(t[0])+flatten(t[1])
def check(path):
    data=path.read_bytes();ww=flatten(json.loads(data))
    t,a,d,h,x,y=(('parameter',q)for q in('t','a','d','h','x','y'))
    T,D,H,stack=t,d,h,[];fields=iter((y,x))
    need(ww[-3:]==['copyGuard','compareGuard','push'],'gate suffix')
    for token in ww[:-3]:
        if token=='push':stack.append(T);T=Z
        elif token in('copyD','copyH','copyA'):
            stack.append(T);T={'copyD':D,'copyH':H,'copyA':a}[token]
        elif token=='cons':T=I(stack.pop(),T)
        elif token=='incT':T=S(T)
        elif token=='readH':H=('add',H,next(fields))
        elif token=='readDCons':D=('add',D,next(fields));T=I(T,D)
        else:raise ValueError(token)
    need(next(fields,None)is None,'unconsumed AX operand')
    h1=I(Ex(D,U(D,H)),H)
    h2=I(U(D,U(a,H)),U(a,U(D,H)))
    h3=I(M(H,D),I(E(H,a),M(a,D)))
    h4=I(E(H,D),I(M(a,H),M(a,D)))
    h6=I(U(D,a),I(U(D,I(a,H)),U(D,H)))
    fused=N(I(h4,U(D,N(E(H,D)))))
    rho=I(I(I(H,d),D),I(I(D,H),I(a,H)))
    expected=[t,U(a,h),rho,h1,h2,h3,fused,h6,I(a,U(a,a))]
    need(stack==expected,'stack expression mismatch')
    point=I(a,M(a,D));vac=I(M(H,D),U(a,M(H,D)))
    sep=U(D,And(I(M(H,D),point),I(M(a,D),a)))
    gate=N(I(vac,U(a,I(sep,N(point)))))
    need(T==gate,'gate input mismatch')
    return {'status':'PASS','grammar_sha256':hashlib.sha256(data).hexdigest(),
       'atom_word_length':len(ww),'saved_stack_terms_before_gate_push':len(stack),
       'total_entries_after_gate_push':len(stack)+1,
       'fused_head_exact':True,'all_other_stack_terms_exact':True,'guard_input_exact':True,
       'scope':'Free-term emitter identity. Atom implementation, logical translations, and physical simulation are separate obligations.'}
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('grammar',type=Path);ap.add_argument('--output',type=Path);a=ap.parse_args()
    r=json.dumps(check(a.grammar),indent=2)+'\n'
    if a.output:a.output.write_text(r)
    print(r,end='')
