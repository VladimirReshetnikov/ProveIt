#!/usr/bin/env python3
"""Price 49 terminal padding candidates using maximum matching (an optimistic score)."""
import argparse
from common import *
allsub = subtrees(G)
def effect(t):
 top='g';stack=[]
 for x in word(t):
  if x in ('node49','node55','node58'):
   stack.append(top);top=0
  elif x=='node70':stack.append(top);top='a'
  elif x=='node65':
   if not stack:return None
   a=stack.pop();top=0 if a==0 and top==0 else('I',a,top)
  else:return None
 if top!=0 or 'g' not in stack or any(x not in (0,'g')for x in stack):return None
 return len(stack)
def replace_last(t,x):
 if c.isnode(t):return t[0],replace_last(t[1],x)
 assert t=='node49';return x
for x in ('node55','node58','node70','node49'):
 for n in range(1,17):
  def balanced(w):
   if len(w)==1:return w[0]
   m=len(w)//2;return balanced(w[:m]),balanced(w[m:])
  allsub.add(balanced([x]*n))
terms=[x for x in allsub if effect(x) is not None]
results=[];seeds=[]
for t in sorted(terms,key=lambda t:(len(word(t)),repr(t))):
 g=replace_last(G,t);raw,index,shape=c.build(g);ops=c.opportunities_fast(raw,shape);matching=c.max_matching(ops)
 score=len(raw)//2-len(matching)
 r=dict(term=t,word=word(t),pushes=effect(t),raw=len(raw)//2,readers=len(shape),folds=len(matching),optimistic=score)
 results.append(r)
 if score<=194:seeds.append((r,g))
print(json.dumps(results,indent=2))
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path)
a=ap.parse_args();O=output_dir(a.output,'ax11g-padding-')
(O/'prices.json').write_text(json.dumps(results,indent=2)+'\n')
(O/'seeds.json').write_text(json.dumps(seeds,indent=2)+'\n')
print('best',min(r['optimistic']for r in results),'seeds',len(seeds),'candidates',len(results))

print('output',O)
