#!/usr/bin/env python3
"""Free-algebra check of the exact changed AX formula and unchanged stack."""
from pathlib import Path
import json,re
BASE=Path(__file__).resolve().parents[1]
I=lambda a,b:('I',a,b)
M=lambda a,b:('+',I(a,b),1)
U=lambda a,b:('+',I(b,a),2)
E=lambda a,b:('+',I(a,b),3)
N=lambda a:I(a,1)
AND=lambda a,b:N(I(a,N(b)))
def inc(x):
 if isinstance(x,int):return x+1
 if isinstance(x,tuple)and x[0]=='+':return('+',x[1],x[2]+1)
 return('+',x,1)
def effect(tokens):
 t='initial_top';stack=[];d='initial_d';h='initial_h'
 for k in tokens:
  if k in('copyA','copyD','copyH'):
   stack.append(t);t={'copyA':'A','copyD':d,'copyH':h}[k]
  elif k=='push':stack.append(t);t=0
  elif k=='cons':t=I(stack.pop(),t)
  elif k=='incT':t=inc(t)
  elif k=='readH':h='H'
  elif k=='readDCons':d='D';t=I(t,d)
  elif k in('copyGuard','compareGuard','close'):pass
  else:raise ValueError(k)
 return t,stack
src=(BASE/'reference/pa196/PA196/Source/AXProgram.lean').read_text()
old=re.findall(r'\(\.(\w+), \d+, \d+\)',src.split('def program')[0])
new=old[:121]+['copyA']*3+['cons','incT','incT','cons']+old[138:]
oldtop,oldstack=effect(old);newtop,newstack=effect(new)
a,b,c='H','D','A'
delta=I(E(a,b),U(c,E(a,b)));gamma=I(c,U(c,c))
v=I(M(a,b),U(c,M(a,b)));p=I(c,M(c,b))
sep=U(b,AND(I(M(a,b),p),I(M(c,b),c)));q=U(c,I(sep,N(p)))
assert oldtop==N(I(delta,I(v,q)))
assert newtop==N(I(gamma,I(v,q)))
assert newstack==oldstack and len(newstack)==9
assert len(old)==201 and len(new)==191
receipt=json.loads((BASE/'diagonal199/diagonal_semantics_receipt.json').read_text())
assert receipt['new_tokens_expanded']==new
if __name__=='__main__':
 print(json.dumps({'old_macro_items':len(old),'new_macro_items':len(new),
 'unchanged_stack_items':len(newstack),'exact_new_gate':True,'guard_and_cleanup':'unchanged; covered by macro/control-flow audit'},indent=2))
