#!/usr/bin/env python3
"""Fixed syntactic fusion proofs, checked with K, S, Peirce and h1 only.

K/S/Peirce are the inherited derived implicational basis from restricted rho8.
No semantic tautology oracle, hidden explosion axiom, or sample valuation.
"""
import json,argparse
from pathlib import Path
A=('var','A');B=('var','B');F=('const',1);ZERO=('const',0)
def I(a,b):return ('I',a,b)
def U(d,a):return ('U',d,a)
def N(a):return I(a,F)
def K(a,b):return I(a,I(b,a))
def S(a,b,c):return I(I(a,I(b,c)),I(I(a,b),I(a,c)))
def peirce(a,b):return I(I(I(a,b),a),a)
def h1(d,h):return I(N(U(d,N(U(d,h)))),h)
class Proof:
 def __init__(self):self.rows=[]
 def add(self,f,rule,*args):
  self.rows.append([f,rule,list(args)]);return len(self.rows)-1
 def assume(self,f):return self.add(f,'assumption')
 def ax(self,tag,*args):
  f={'K':K,'S':S,'Peirce':peirce,'h1':h1}[tag](*args)
  return self.add(f,tag,*args)
 def mp(self,p,q):
  a=self.rows[p][0];imp=self.rows[q][0]
  assert imp[0]=='I' and imp[1]==a,(a,imp)
  return self.add(imp[2],'MP',p,q)
 def extend(self,p):
  base=len(self.rows)
  for f,r,a in p.rows:self.add(f,r,*([base+x for x in a]if r=='MP'else a))
  return len(self.rows)-1
 def identity(self,a):
  k1=self.ax('K',a,I(a,a));k2=self.ax('K',a,a)
  ss=self.ax('S',a,I(a,a),a)
  return self.mp(k2,self.mp(k1,ss))
 def discharge(self,x):
  q=Proof();mapped=[]
  for f,r,args in self.rows:
   if f==x:ind=q.identity(x)
   elif r=='MP':
    p,imp=args;ante=self.rows[p][0]
    ss=q.ax('S',x,ante,f)
    ind=q.mp(mapped[p],q.mp(mapped[imp],ss))
   else:
    base=q.add(f,r,*args)
    kk=q.ax('K',f,x)
    ind=q.mp(base,kk)
   mapped.append(ind)
  return q

def explosion(a):
 p=Proof();one=p.assume(F);y=U(ZERO,N(U(ZERO,a)))
 kk=p.ax('K',F,y);hy=p.mp(one,kk);oo=p.ax('h1',ZERO,a)
 p.mp(hy,oo);return p.discharge(F)
def verify(p,goal):
 for j,(f,r,a)in enumerate(p.rows):
  if r=='MP':
   u,v=a;assert 0<=u<j and 0<=v<j
   assert p.rows[v][0]==I(p.rows[u][0],f)
  else:
   assert r in ('K','S','Peirce','h1'),r
   assert f=={'K':K,'S':S,'Peirce':peirce,'h1':h1}[r](*a)
 assert p.rows[-1][0]==goal
 return dict(lines=len(p.rows),axioms={r:sum(x[1]==r for x in p.rows)for r in ('K','S','Peirce','h1')},MP=sum(x[1]=='MP' for x in p.rows))
def build():
 fused=N(I(A,B))
 # A, not B entail not(A -> B).
 p=Proof();a=p.assume(A);nb=p.assume(N(B));ab=p.assume(I(A,B));b=p.mp(a,ab);p.mp(b,nb)
 join=p.discharge(I(A,B)).discharge(N(B)).discharge(A)
 # not(A -> B) entails A, using the explicitly supplied h1 explosion proof.
 p=Proof();ex=p.extend(explosion(A));g=p.assume(fused);ab=p.assume(I(A,B));bot=p.mp(ab,g);p.mp(bot,ex)
 p=p.discharge(I(A,B));pc=p.ax('Peirce',A,B);p.mp(len(p.rows)-2,pc)
 left=p.discharge(fused)
 # not(A -> B) entails not B using K only.
 p=Proof();g=p.assume(fused);b=p.assume(B);kk=p.ax('K',B,A);ab=p.mp(b,kk);p.mp(ab,g)
 right=p.discharge(B).discharge(fused)
 data={}
 for name,p,goal in [('join',join,I(A,I(N(B),fused))),('left_projection',left,I(fused,A)),('right_projection',right,I(fused,N(B)))]:
  data[name]=dict(goal=goal,**verify(p,goal),proof=p.rows)
 return data
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
 data=build();args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(data,indent=2)+'\n')
 print(json.dumps({k:{p:v for p,v in x.items()if p!='proof'}for k,x in data.items()},indent=2))
