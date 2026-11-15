#!/usr/bin/env python3
"""Exact free-term binding for AX emitter variants.

This binds source words to formulas; it is not a proof of their logical equivalence.
Logical proof certificates are provided separately by the report's theory component.
"""
from pathlib import Path
from itertools import permutations
import argparse,json,hashlib,sys
if not __debug__ or sys.flags.optimize:raise RuntimeError("Run with assertions enabled; do not use -O.")

TOKENS={'node49':['push'],'node55':['copyD'],'node58':['copyH'],'node70':['copyA'],'node65':['cons'],'node72':['readH'],'node75':['readDCons'],'node142':['copyGuard'],'node150':['compareGuard'],'node60':['incT']*2,'node61':['incT']*4}
def word(t):
 if isinstance(t,str):return TOKENS[t]
 if t==['leaf','inc',1]:return['incT']
 assert isinstance(t,list) and len(t)==2
 return word(t[0])+word(t[1])
Z=('zero',)
def S(x):return('S',x)
ONE=S(Z)
def I(x,y):return('I',x,y)
def U(x,b):return S(S(I(b,x)))
def M(x,y):return S(I(x,y))
def E(x,y):return S(S(S(I(x,y))))
def N(x):return I(x,ONE)
def Aand(x,y):return N(I(x,N(y)))
def Ex(x,b):return N(U(x,N(b)))
def head(k,D,A,H):
 if k=='BA':return I(N(H),U(D,I(U(D,H),A)))
 if k=='BP':return I(H,U(D,I(U(D,N(H)),A)))
 if k=='h1':return I(Ex(D,U(D,H)),H)
 if k=='J':return I(I(U(D,N(U(D,H))),H),H)
 if k=='B':return I(N(H),U(D,N(U(D,H))))
 if k=='h2':return I(U(D,U(A,H)),U(A,U(D,H)))
 if k=='h3':return I(M(H,D),I(E(H,A),M(A,D)))
 if k=='h4':return I(E(H,D),I(M(A,H),M(A,D)))
 if k=='h5':return Ex(D,E(H,D))
 if k=='h5X':return I(U(D,N(E(H,D))),A)
 if k=='h6':return I(U(D,A),I(U(D,I(A,H)),U(D,H)))
 if k=='h6Q':return I(U(D,I(A,H)),I(U(D,A),U(D,H)))
 raise ValueError(k)

def inspect(path):
 data=json.loads(path.read_text())
 def expand(v):
  if isinstance(v,str) and v in data['rules']:return [expand(x) for x in data['rules'][v]]
  return v
 tree=expand(data['root']);ww=word(tree)
 t,a,d,h,x,y=map(lambda q:('parameter',q),('t','a','d','h','x','y'))
 T,D,H,stack=t,d,h,[];fields=iter((y,x))
 assert ww[-3:]==['copyGuard','compareGuard','push']
 for token in ww[:-3]:
  if token=='push':stack.append(T);T=Z
  elif token in ('copyD','copyH','copyA'):
   stack.append(T);T={'copyD':D,'copyH':H,'copyA':a}[token]
  elif token=='cons':T=I(stack.pop(),T)
  elif token=='incT':T=S(T)
  elif token=='readH':H=('add',H,next(fields))
  elif token=='readDCons':D=('add',D,next(fields));T=I(T,D)
  else:raise ValueError(token)
 assert len(stack)==10 and stack[0]==t and stack[1]==U(a,h)
 rho=I(I(I(H,d),D),I(I(D,H),I(a,H)))
 assert stack[2]==rho
 actual=stack[3:9];matches=[]
 for j,f in enumerate(actual):
  choices=[]
  for k in ('BA','BP','h2','h3','h4','h5X','h6','h6Q'):
   for pp in permutations(range(3)):
    args=[(D,a,H)[i]for i in pp]
    if f==head(k,*args):choices.append({'schema':k,'DAH_argument_indices':list(pp)})
  assert choices,(j,f)
  matches.append(choices)
 schemas=[v[0]['schema']for v in matches]
 assert len(set(schemas))==6
 assert {'h2','h3','h4','h5X'}.issubset(schemas)
 assert sum(k in schemas for k in ('BA','BP'))==1
 assert ('h6'in schemas)^('h6Q'in schemas)
 gamma=I(a,U(a,a));assert stack[9]==gamma
 point=I(a,M(a,D));vac=I(M(H,D),U(a,M(H,D)))
 sep=U(D,Aand(I(M(H,D),point),I(M(a,D),a)))
 gate=N(I(vac,U(a,I(sep,N(point)))))
 assert T==gate
 assert len(ww)==188
 return {'status':'PASS','macro_tokens':len(ww),'schema_order':schemas,'schema_matches':matches,
 'generalization':'U(c,h)','rho':'((H->d)->D)->((D->H)->(A->H)), D=d+x',
 'diagonal':'Gamma(A)','gate_unchanged':True,'final_suffix':'copyGuard; compareGuard; push',
 'logical_claim':'Exact source term identity only; logical equivalence uses separate iPRA proof constructors.',
 'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('candidate',type=Path);p.add_argument('--output',type=Path);a=p.parse_args();r=inspect(a.candidate)
 s=json.dumps(r,indent=2)+'\n'
 if a.output:a.output.write_text(s)
 print(s,end='')
