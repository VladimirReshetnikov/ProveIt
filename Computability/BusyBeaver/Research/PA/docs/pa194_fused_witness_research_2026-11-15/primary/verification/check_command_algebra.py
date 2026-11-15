#!/usr/bin/env python3
"""Symbolic AX10 word identities, using total Cantor projections.

The code never assumes pair constructors are disjoint or injective beyond
hd(pair(a,w))=a and tl(pair(a,w))=w, which remain valid at pair(0,0)=0.
Head symbols have certified residue0; U has residue2. MP_0 at offset0 is
zero on both branches. Offsets use I(0,i)=0 iff i=0.
"""
import json,argparse
from pathlib import Path
T=('v','t');W=('v','w');D=('v','d');H=('v','h')
A=('v','a');B=('v','b');C=('v','c');X=('v','x');Y=('v','y');Z=('v','z');U0=('v','u');I0=('v','i')
def plus(a,b):
 if a==0:return b
 if b==0:return a
 if isinstance(b,tuple)and b[0]=='sub' and b[2]==a:return b[1] # hypothesis a<=b[1]
 return ('+',a,b)
def pair(a,w):return 0 if a==w==0 else ('p',a,w)
def hd(w):return 0 if w==0 else w[1]if w[0]=='p'else('hd',w)
def tl(w):return 0 if w==0 else w[2]if w[0]=='p'else('tl',w)
def imp(a,b):return 0 if a==b==0 else ('I',a,b)
def uni(i,a):return ('U',i,a)
def pushlist(items,w):
 for a in reversed(items):w=pair(a,w)
 return w

def heads(a,d,h,old_d,old_h):
 return [('q',j,a,d,h,old_d)for j in range(8)]+[uni(a,old_h)]
def ax(c,x,y,z):return ('AX',c,x,y,z)
S=('S',)
def mp(x):return('MP',x)
A0=ax(0,0,0,0)
PUSH=[A0]+[S]*9+[mp(0)]
POP=[A0]+[S]*11
DISCARD=[mp(0)]
def known_nonone(a,nonunit):
 if a in nonunit:return True
 if isinstance(a,int):return a!=1
 return a[0]in('q','I','U')
def run(word,state,nonunit=frozenset()):
 if state=='HALT':return state
 for command in word:
  if state=='HALT':break
  t,w,d,h=state
  if command[0]=='AX':
   _,a,x,y,z=command
   qs=heads(a,plus(d,x),plus(h,y),d,h)
   state=(0,pushlist(qs+[t],w),z,0)
  elif command[0]=='S':
   if h==1:state='HALT'
   else:
    assert known_nonone(h,nonunit),('undischarged cache !=1',h)
    state=(h,tl(w),d,hd(w))
  else:
   b=plus(d,command[1])
   if b==0:r=0 # both comparison outcomes agree
   elif h==imp(t,b):r=b
   elif t==0 and h==0:r=0 # I(0,b)=0 implies b=0, which also returns0
   else:raise AssertionError(('unproved MP branch',t,b,h))
   state=(r,w,b,0)
 return state

def main(out):
 checks=[]
 def check(name,word,start,end,nonunit=frozenset()):
  actual=run(word,start,nonunit);assert actual==end,(name,actual,end)
  checks.append(dict(name=name,commands=word,input=start,output=end,nonunit=sorted(nonunit,key=repr)))
 check('Push',PUSH,(T,W,D,H),(0,pair(T,W),0,0))
 check('Pop_nonunit',POP,(T,pair(A,W),D,H),(T,W,0,A),frozenset([T]))
 check('Pop_unit',POP,(1,pair(A,W),D,H),'HALT')
 check('Discard',DISCARD,(T,W,0,H),(0,W,0,0))
 check('Offset',[mp(I0)],(0,W,0,0),(0,W,I0,0))
 q=heads(A,D,H,0,0)
 for j in range(8):
  word=DISCARD+[ax(A,D,H,0)]+[S]*(j+2)+POP*(8-j)
  check('Selector_'+str(j),word,(T,W,0,0),(q[j],W,0,0))
 qr=heads(A,D,H,U0,0)[7]
 check('Restricted_rho',DISCARD+[mp(U0),ax(A,('sub',D,U0),H,0)]+[S]*9+POP,(T,W,0,0),(qr,W,0,0))
 check('Gen',PUSH+[S,ax(I0,0,0,0)]+[S]*10,(A,W,0,0),(uni(I0,A),W,0,0))
 check('Gen_contradiction',PUSH+[S,ax(I0,0,0,0)]+[S]*10,(1,W,0,0),(uni(I0,1),W,0,0))
 suffix=[S,S,mp(B)]+POP
 check('MP_suffix_nonunit',suffix,(0,pushlist([A,imp(A,B),0],W),0,0),(B,W,0,0),frozenset([A,B]))
 check('MP_suffix_unit_minor',[S,S,mp(B)]+POP,(0,pushlist([1,imp(1,B),0],W),0,0),'HALT')
 check('MP_suffix_unit_conclusion',[S,S,mp(1)]+POP,(0,pushlist([A,imp(A,1),0],W),0,0),'HALT',frozenset([A]))
 rec=dict(status='PASS',symbolic_word_contracts=len(checks),AX_entries=10,axiom_heads=8,generalization_index=8,contracts=checks,scope='Universal symbolic command identities; the written proof supplies QF induction and residue facts.')
 out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(rec,indent=2)+'\n')
 print(json.dumps({k:v for k,v in rec.items()if k!='contracts'},indent=2))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();main(a.output)
