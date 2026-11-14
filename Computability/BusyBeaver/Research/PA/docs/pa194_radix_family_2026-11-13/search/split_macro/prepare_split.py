from pathlib import Path
from functools import lru_cache
import json,sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"construction"))
import compiler as c
BASE=Path(__file__).resolve().parent;OUT=BASE;OUT.mkdir(exist_ok=True)
root=c.read_grammar(ROOT/'construction/inputs/pa194.grammar.json')
split={'node65':('node17','node64'),'node49':('node37','node48'),'node58':('node49','node57'),'node55':('node49','node54'),'node70':('node49','node69')}
extra={'node17':105,'node48':29,'node57':20,'node54':114,'node69':179,'node37':28,'node64':106}
def expose(t):
 if isinstance(t,str)and t in split:return tuple(expose(x)for x in split[t])
 return tuple(expose(x)for x in t)if c.isnode(t)else t
root=expose(root);mp=dict(c.MACROS);mp.update(extra)
base,_=c.machine();base={k:v for k,v in base.items()if k[0]<1300}
arr=[];seen={}
def conv(t):
 if t in seen:return seen[t]
 if c.isnode(t):
  a,b=conv(t[0]),conv(t[1]);val=[1,a,b,0]
 else:val=[0,-1 if t==c.BREAK else mp[t],-1,-1]
 idx=len(arr);arr.append(val);seen[t]=idx;return idx
rt=conv(root)
lines=[str(len(base)//2)]
for q in sorted({q for q,b in base}):lines.append(' '.join(map(str,[q,*base[q,0],*base[q,1]])).replace('True','1').replace('False','0'))
lines+=['1',f'0 {len(arr)} {rt}']+[' '.join(map(str,row))for row in arr]
(OUT/'primary194_split.txt').write_text('\n'.join(lines)+'\n')
ns=c.raw_nodes()
@lru_cache(None)
def attrs(t):
 if isinstance(t,str):return attrs(ns[t])
 if not c.isnode(t):return (0,0,0,0,int(t[:2]==('leaf','inc')))
 a,b=map(attrs,t);return(1+max(a[0],b[0]),a[1]+1,max(a[1]+1,a[2],b[2]),max(a[3],b[3],1+a[1]if a[4]else 0),a[4])
leafs={(-1 if t==c.BREAK else mp[t]):attrs(t)for t in seen if not c.isnode(t)}
lines=[str(len(leafs))]+[' '.join(map(str,[q,*a]))for q,a in sorted(leafs.items())]
(OUT/'leaf_attrs.txt').write_text('\n'.join(lines)+'\n')
text=(ROOT/'search/search_global.cpp').read_text()
text=text.replace('#include "screen_global.cpp"','#include "screen_split.cpp"')
text=text.replace('if(cycle++%1000==999)','if(false&&cycle++%1000==999)').replace('if(pick(1000)<3)','if(false&&pick(1000)<3)')
replacement='case 105:return "\\\"node17\\\"";case 106:return "\\\"node64\\\"";case 28:return "\\\"node37\\\"";case 29:return "\\\"node48\\\"";case 20:return "\\\"node57\\\"";case 114:return "\\\"node54\\\"";case 179:return "\\\"node69\\\"";'
text=text.replace('case -1:return',replacement+'case -1:return')
(OUT/'search_split.cpp').write_text(text)
text=(ROOT/'search/screen_global.cpp').read_text()
text=text.replace('if(l==61&&r==61)', 'if(l==28&&r==29){value[i]=19;continue;}\n  if(l==19&&r==20){value[i]=12;continue;}\n  if(l==19&&r==114){value[i]=98;continue;}\n  if(l==19&&r==179){value[i]=166;continue;}\n  if(l==105&&r==106){value[i]=90;continue;}\n  if(l==61&&r==61)')
(OUT/'screen_split.cpp').write_text(text)
print('prepared',len(arr),len(leafs))
