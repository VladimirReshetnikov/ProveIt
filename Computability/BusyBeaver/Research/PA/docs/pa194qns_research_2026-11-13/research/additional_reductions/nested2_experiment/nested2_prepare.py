#!/usr/bin/env python3
"""Search inputs for a nested-tag binary formula coding, not an accepted machine."""
from pathlib import Path
from collections import Counter
import random,json,shutil
import compiler as c
import support as s
HERE=Path(__file__).resolve().parent
OUT=HERE/'nested2';OUT.mkdir(exist_ok=True)
INC=('leaf','inc',1);BREAK=('leaf','breakTo',1)
names={'node49':19,'node55':98,'node58':12,'node70':166,'node65':90,'node72':69,'node75':213,'node142':194,'node150':221,INC:61,BREAK:-1}
def word(t):
 if t=='node60':return[61]*2
 if t=='node61':return[61]*4
 if c.isnode(t):return word(t[0])+word(t[1])
 return[names[t]]
old=word(c.read_grammar(HERE/'grammar.json'));new=[];i=0;tags=Counter()
while i<len(old):
 if old[i]!=90:new.append(old[i]);i+=1;continue
 j=i+1
 while j<len(old)and old[j]==61:j+=1
 n=j-i-1;assert 0<=n<=3;tags[n]+=1
 new += [[90],[90,19,90,61],[61,90,61],[90,61,19,90,61]][n]
 i=j
(OUT/'word.json').write_text(json.dumps(new))
raw=s.read_table(HERE/'raw201.native.tm')
raw={k:(w,d,99 if t==190 else t) for k,(w,d,t) in raw.items() if k[0]<1300 and k[0]!=190}
raw[164,1]=(1,True,114)
(OUT/'fixed.native.tm').write_text(s.table_text(raw))
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
ns={k:tup(v)for k,v in json.loads((HERE/'parent6.nodes.json').read_text()).items()}
ns['node61']=(INC,INC);ns['node163']=('node6','node54')
(OUT/'nodes.json').write_text(json.dumps(ns))
def free_pair(a,b):
 if a==61 and b==61:return 99
 return(a,b)
def repair(seed):
 rnd=random.Random(seed);seq=list(new)
 while True:
  pairs=Counter(zip(seq,seq[1:]));m=max(pairs.values())
  if m==1:break
  opts=[p for p,v in pairs.items()if v==m]
  p=rnd.choice(opts);q=free_pair(*p);r=[];i=0
  while i<len(seq):
   if i+1<len(seq) and (seq[i],seq[i+1])==p:r.append(q);i+=2
   else:r.append(seq[i]);i+=1
  seq=r
 def brack(ss):
  if len(ss)==1:return ss[0]
  # A right-heavy final tree respects the bounded decoder left scanner.
  split=1 if seed%3 else rnd.randint(1,min(3,len(ss)-1))
  return free_pair(brack(ss[:split]),brack(ss[split:]))
 return brack(seq)
def treecode(t):
 vals=[];ids={}
 def go(t):
  if t in ids:return ids[t]
  if isinstance(t,int):x=(0,t,-1,-1)
  else:x=(1,go(t[0]),go(t[1]),0)
  ids[t]=len(vals);vals.append(x);return ids[t]
 root=go(t);return vals,root
seeds=[];seen=set()
for i in range(200):
 t=repair(i)
 if t not in seen:seen.add(t);seeds.append(t)
lines=[str(len(raw)//2)]
for q in sorted({q for q,b in raw}):
 lines.append(' '.join(map(str,[q,*raw[q,0],*raw[q,1]])).replace('True','1').replace('False','0'))
lines.append(str(len(seeds)))
for i,t in enumerate(seeds):
 vals,root=treecode(t);lines.append(f'{i} {len(vals)} {root}')
 lines.extend(' '.join(map(str,v))for v in vals)
(OUT/'templates.txt').write_text('\n'.join(lines)+'\n')
SRC=HERE/'upstream_search'
shutil.copy(SRC/'inputs/leaf_attrs.txt',OUT/'leaf_attrs.txt')
screen=(SRC/'screen.cpp').read_text().replace('if(l==99&&r==99)','if(fixedstate[190]&&l==99&&r==99)')
(OUT/'screen.cpp').write_text(screen)
search=(SRC/'search_plateau.cpp').read_text()
search=search.replace('if(cycle++%1000==999)','if(false)').replace('if(pick(1000)<3)','if(false)')
search=search.replace('if(ns.score<=62','if(ns.score<=74').replace('if(ns.eff<=60','if(ns.eff<=61')
(OUT/'search.cpp').write_text(search)
rec={'formula_coding':'I=2p;M=2p(2p(a,b),0)+1;E=2p(2p(a,b)+1,0)+1;U=2p(B,a+1)+1','old_tokens':len(old),'new_tokens':len(new),'constructor_tag_counts':dict(tags),'fixed_controls':len(raw)//2,'seed_trees':len(seeds),'scope':'Experimental grammar search; no accepted TM claimed.'}
(OUT/'prepare.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps(rec,indent=2))
