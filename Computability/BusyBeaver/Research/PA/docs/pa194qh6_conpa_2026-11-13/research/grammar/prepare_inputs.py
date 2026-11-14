#!/usr/bin/env python3
"""Generate exact fixed-word QH6 search input and radix-six leaf attributes."""
from pathlib import Path
import json,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent.parent
sys.path.insert(0,str(ROOT/'construction'))
import compiler as c,support as b
raw=b.read_table(ROOT/'machine/raw.native.tm')
fixed=sorted({q for q,bit in raw if q<1300})
g=c.read_grammar(ROOT/'construction/inputs/q.grammar.json')
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
ns={k:tup(v)for k,v in json.loads((ROOT/'construction/inputs/h6.nodes.json').read_text()).items()}
term=dict(c.MACROS);term[c.BREAK]=-1
entries=[];idx={}
def encode(t):
 if t in idx:return idx[t]
 if t in term:v=(0,term[t],-1,-1)
 else:v=(1,encode(t[0]),encode(t[1]),0)
 i=len(entries);entries.append(v);idx[t]=i;return i
r=encode(g)
lines=[str(len(fixed))]
for q in fixed:
 lines.append(' '.join(map(str,[q,*[int(x)for bit in(0,1)for x in raw[q,bit]]])))
lines+=['1',f'0 {len(entries)} {r}']+[' '.join(map(str,x))for x in entries]
(HERE/'qh6.seed.txt').write_text('\n'.join(lines)+'\n')
def attr(t):
 if isinstance(t,str):return attr(ns[t])
 if t[0]=='leaf':return(0,0,0,0,int(t[1]=='inc'))
 a,b=attr(t[0]),attr(t[1])
 return(1+max(a[0],b[0]),a[1]+1,max(a[1]+1,a[2],b[2]),max(a[3],b[3],1+a[1] if a[4] else 0),a[4])
attrs=[(q,*attr(t))for t,q in term.items()]
(HERE/'leaf_attrs.txt').write_text(str(len(attrs))+'\n'+'\n'.join(' '.join(map(str,x))for x in attrs)+'\n')
print(json.dumps({'fixed':len(fixed),'seed_nodes':len(entries),'attributes':len(attrs),'AX_attribute':attr(g)}))
