#!/usr/bin/env python3
"""Price 14 existing-subtree endings admitted by a finite symbolic stack screen."""
import argparse
from common import *
allsub = subtrees(G)
from itertools import product

def I(a,b):return 0 if a==b==0 else('I',a,b)
def succ(a):
 if isinstance(a,int):return a+1
 if isinstance(a,tuple)and a[0]=='I':return('M',a[1],a[2])
 if isinstance(a,tuple)and a[0]=='M':return('U',a[2],a[1])
 if isinstance(a,tuple)and a[0]=='U':return('E',a[2],a[1])
 return('succ',a)
def decode(a):
 if not isinstance(a,int)or a==0:return a
 n,r=divmod(a,4);s=0
 while(s+1)*(s+2)//2<=n:s+=1
 b=n-s*(s+1)//2;aa=s-b
 return('I',aa,b)if r==0 else('M',aa,b)if r==1 else('U',b,aa)if r==2 else('E',aa,b)
def atoms(a):
 a=decode(a)
 if a in(0,'g'):return set()
 if isinstance(a,tuple):
  if a[0]=='I':return atoms(a[1])|atoms(a[2])
  if a[0]=='E'and a[1]==a[2]:return set()
  if a[0]=='U'and valid(a[2]):return set()
 return{a}
def truth(a,vals):
 a=decode(a)
 if a in(0,'g'):return True
 if isinstance(a,tuple):
  if a[0]=='I':return not truth(a[1],vals)or truth(a[2],vals)
  if a[0]=='E'and a[1]==a[2]:return True
  if a[0]=='U'and valid(a[2]):return True
 return vals[a]
def valid(a):
 aa=sorted(atoms(a),key=repr)
 if len(aa)>12:return False
 return all(truth(a,dict(zip(aa,vs)))for vs in product([False,True],repeat=len(aa)))
def eff(t):
 top='g';st=[]
 for x in word(t):
  if x in ('node49','node55','node58'):st.append(top);top=0
  elif x=='node70':st.append(top);top='a'
  elif x=='node65':
   if not st:return None
   top=I(st.pop(),top)
  elif x==inc:top=succ(top)
  elif x in('node60','node61'):
   for _ in range(2 if x=='node60' else 4):top=succ(top)
  else:return None
 if 'g'not in st or not all(valid(x)for x in st):return None
 return st,top
out=[]
for t in sorted(allsub,key=lambda t:(len(word(t)),repr(t))):
 e=eff(t)
 if e is None:continue
 g=replace_last(G,t);raw,index,shape=c.build(g);ops=c.opportunities_fast(raw,shape);mm=c.max_matching(ops)
 out.append(dict(terminal=t,word=word(t),saved=e[0],top=e[1],raw=len(raw)//2,folds=len(mm),price=len(raw)//2-len(mm)))
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path)
a=ap.parse_args();O=output_dir(a.output,'ax11g-safe-terminal-')
(O/'prices.json').write_text(json.dumps(out,indent=2)+'\n')
print('candidates',len(out),'best',min(x['price']for x in out))
for x in out:print(x['price'],len(x['word']),x['word'],x['saved'])

print('output',O)
