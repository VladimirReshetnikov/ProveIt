#!/usr/bin/env python3
"""Exact implication-code conjugacy, fixed macro scaffold and direct MP pairer.

No runtime claim. MP microcode is independently checked on finite source stencils.
"""
from pathlib import Path
import os
import sys,json,itertools,time
HERE=Path(__file__).resolve().parent;Z=Path(os.environ.get('PROVEIT_ZFC_ROOT', str(HERE.parent/'ProveIt/Computability/BusyBeaver/Research/ZFC'))).resolve();sys.path.insert(0,str(Z/'k218-quantifier-stability/pricing'))
import source_language as s,build221 as b,measure_pinned as m
root=s.tree(json.loads((Z/'candidate-k218/sites218.json').read_text()));tab=b.read_table((Z/'candidate-k218/k218.native.tm').read_bytes());g,_=b.decoder_map(tab,root);q=lambda k:b.sole(g,k)
macros={'a':q(98),'b':q(12),'c':q(166),'I':q(90),'F':q(184)[0],'push':q(19),'readU':q(104),'to1':q(81),'+1':('CI',1)};rev={v:k for k,v in macros.items()}
ranges=[('rho8',135,486),('G',486,895),('rho6',895,1178),('rho5',1178,1474),('rho4',1474,1773),('rho3',1773,2069),('rho2',2069,2419),('rho1',2419,2650),('bundle',2650,4563)]
positions=[]
def record(t,lo=0,p=''):
 hi=lo+len(s.sites(t))
 if hi<=135 or lo>=4563:return
 if t in rev and lo>=135 and hi<=4563:positions.append((p,rev[t],lo,hi));return
 if s.leaf(t):raise ValueError((p,t,lo,hi))
 record(t[0],lo,p+'0');record(t[1],lo+len(s.sites(t[0])),p+'1')
record(root)
words=[];asts=[]
def parse(w):
 stack=[];i=0
 while i<len(w):
  a=w[i];i+=1
  if a=='push':
   assert w[i:i+2]==['readU','to1'];i+=2;stack.append('u')
  elif a in 'abcF':stack.append(a)
  elif a=='I':
   k=0
   while i<len(w)and w[i]=='+1':k+=1;i+=1
   y=stack.pop();x=stack.pop();stack.append(('IRQE'[k],x,y))
  else:raise ValueError((a,w))
 assert len(stack)==1,stack
 return stack[0]
def emit(t,revimp=False):
 if isinstance(t,str):return ['push','readU','to1']if t=='u'else[t]
 k,x,y=t
 if k=='I'and revimp:x,y=y,x
 return emit(x,revimp)+emit(y,revimp)+['I']+['+1']*'IRQE'.index(k)
for name,lo,hi in ranges:
 w=[n for p,n,a,bb in positions if lo<=a and bb<=hi];words.append(w);asts.append(parse(w));assert emit(asts[-1])==w
 print('AST',name,asts[-1],flush=True)
# NB 'IRQE' tags: I=0,R=1,Q=2,E=3 is only an internal naming mnemonic here.
# Only tag0 is reversed, so the nonzero spelling does not affect the transformation.

def rebuild(word):
 assert len(word)==len(positions)
 edits={p:macros[x]for(p,*_),x in zip(positions,word)}
 def change(t,p=''):
  if p in edits:return edits[p]
  if s.leaf(t):return t
  return change(t[0],p+'0'),change(t[1],p+'1')
 return change(root)
revroot=rebuild(sum((emit(t,True)for t in asts),[]))
# Copy D4 to X6 while preserving D4, using zero Y7.
copy46=((('CD',4),(('CI',7),(('CI',6),('CC',3)))),(('CD',7),(('CI',4),('CC',2))))
mprev=(copy46,q(106))
# For normal orientation first move T1 to X6, then copy D4 to T1 via Y7.
copy41=((('CD',4),(('CI',7),(('CI',1),('CC',3)))),(('CD',7),(('CI',4),('CC',2))))
mpold=(q(28),(copy41,q(106)))
assert s.boundary(mprev)==s.boundary(mpold)==(0,0,False)
for mode,macro in [('reversed',mprev),('ordinary',mpold)]:
 for a,bb,ws in itertools.product(range(7),range(7),range(3)):
  rr=[7,a,ws,0,bb,2,0,0,11];out,_=m.run_macro(s,macro,rr)
  x,y=(bb,a)if mode=='reversed'else(a,bb);rr[1]=4*((x+y)*(x+y+1)//2+y)
  assert out==rr,(mode,a,bb,ws,out,rr)
print('MPFINITE',294,'PASS',len(s.sites(mprev)),len(s.sites(mpold)),flush=True)
out=HERE/'reversed-implication-price';out.mkdir(exist_ok=True);records=[]
for mode,t,mp in [('reversed-direct',revroot,mprev),('reversed-oldMP',revroot,None),('ordinary-direct',root,mpold)]:
 if mp is not None:t=m.splice(s,t,4652,4705,mp)
 rr=s.sites(t);assert s.graph_intervals(rr)==s.graph_arithmetic(rr)[0];met=s.metrics(t);d=out/mode;d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(rr));info=dict(mode=mode,metrics=met,correct_MP=mode!='reversed-oldMP',finite_MP_cases=147)
 try:tt,cm=m.compile_tree(s,b,tab,root,t);info['compiler']=cm;(d/'raw.tm').write_bytes(b.table_bytes(tt))
 except(ValueError,KeyError,AssertionError)as e:info['compiler_error']=repr(e)
 (d/'result.json').write_text(json.dumps(info,indent=2));records.append(info);print('RESULT',info,flush=True)
(out/'result.json').write_text(json.dumps(records,indent=2))
