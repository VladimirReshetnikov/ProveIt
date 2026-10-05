"""Exact Wick contractions for the first two balanced-cut corrections."""
from collections import Counter
from functools import lru_cache
from pathlib import Path
import json,sympy as s
m=s.symbols('m',positive=True)
@lru_cache(None)
def pairings(seq):
 if not seq:return ((),)
 a=seq[0];out=[]
 for k in range(1,len(seq)):
  b=seq[k];rest=seq[1:k]+seq[k+1:]
  for p in pairings(rest):out.append(((a,b),)+p)
 return tuple(out)
def moment(powers):
 N=sum(powers)
 if N%2:return s.Integer(0)
 nxt=[];start=0
 for p in powers:
  nxt+=list(range(start+1,start+p))+[start];start+=p
 coeff=Counter()
 for matching in pairings(tuple(range(N))):
  for bits in range(1<<(N//2)):
   parent=list(range(N))
   def root(i):
    while parent[i]!=i:parent[i]=parent[parent[i]];i=parent[i]
    return i
   def join(i,j):parent[root(i)]=root(j)
   singles=bits.bit_count()
   for k,(i,j) in enumerate(matching):
    if bits>>k&1:join(i,nxt[i]);join(j,nxt[j])
    else:join(i,nxt[j]);join(nxt[i],j)
   loops=len({root(i) for i in range(N)});coeff[loops-singles]+=(-1)**singles
 return s.factor(sum(c*m**e for e,c in coeff.items())/s.Integer(4)**(N//2))
E2=moment((2,));E4=moment((4,));E6=moment((6,));E22=moment((2,2));E24=moment((2,4));E44=moment((4,4))
a=(4-m*m)/(12*m)-m/4
c1=s.factor(a+m*E2-s.Rational(4,3)*E4)
EL2=-s.Rational(4,3)*E2+m*E4/2-s.Rational(32,15)*E6+s.Rational(3,2)*E22
EL1sq=a*a+m*m*E22+s.Rational(16,9)*E44+2*a*m*E2-s.Rational(8,3)*a*E4-s.Rational(8,3)*m*E24
c2=s.factor(EL2+EL1sq/2)
if c1.subs(m,2)!=s.Rational(3,8) or c2.subs(m,2)!=s.Rational(25,128):raise RuntimeError('Catalan regression')
out={'moments':{str(p):str(moment(p)) for p in ((2,),(4,),(6,),(2,2),(2,4),(4,4))},'c1':str(c1),'c2':str(c2),'m5':[str(c1.subs(m,5)),str(c2.subs(m,5))],'status':'formal balanced-cut expansion; analytic error and all-n extension need proof'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
