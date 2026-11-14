#!/usr/bin/env python3
"""Prepare Brouwer plus explosion templates; source-level equivalence only.

A changed eleven-head emitter also requires new proof-word selectors and
physical validation. No compiled consistency machine is supplied by this file.
"""
from pathlib import Path
exec(Path(__file__).with_name('make_brouwer.py').read_text().split('variants=[];info=[]')[0])
V=[];info=[]
def add_head(t,index,seq):
 i=0
 def bal(xs):
  if len(xs)==1:return names[xs[0]]
  k=len(xs)//2;return bal(xs[:k]),bal(xs[k:])
 def go(x):
  nonlocal i
  if isnode(x):return go(x[0]),go(x[1])
  j=i;i+=1
  return bal(seq+[rev[x]])if j==index else x
 ans=go(t);return ans
for flags in itertools.product([0,1],repeat=4):
 v=w[:];v[18:35]=B
 for part,(a,z) in zip(words(*flags),[(54,70),(70,86),(86,102),(102,121)]):v[a:z]=part
 for shape,t in enumerate([old,other]):
  tv=reword(t,v)
  for loc in [18,35,121]:
   for variable in ['H','D','A']:
    new=add_head(tv,loc,['P','+',variable,'C']);assert len(word(new))==194
    V.append(new);info.append({'id':len(info),'H1':'Brouwer plus explosion','flags':flags,'shape':shape,'explosion_position':loc,'explosion_consequent':variable,'tokens':word(new)})
texts.append(str(len(V)))
for i,t in enumerate(V):
 ts,r=tarray(t);texts.append(f'{i} {len(ts)} {r}');texts.extend(' '.join(map(str,x))for x in ts)
(OUT/'brouwer_explosion_inputs.txt').write_text('\n'.join(texts)+'\n');(OUT/'brouwer_explosion_variants.json').write_text(json.dumps(info,indent=2)+'\n')
cpp=(OUT/'logic_anneal.cpp').read_text()
# All head names are already instantiated in input variants; suppress length-sensitive renamings.
cpp=cpp.replace('if(cycle++%2==1)', 'if(false)').replace('if(cycle%100==0)', 'if(false)').replace('if(pick(1000)<3)', 'if(false)').replace('if(pick(1000)<12)', 'if(false)')
(OUT/'brouwer_explosion.cpp').write_text(cpp)
print('valid B+explosion templates',len(V),'word length194')
