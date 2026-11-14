import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'verification'))
from words import *
from layout import *
from collections import defaultdict
import random,time
start=time.time();random.seed(176)
conf=json.loads(Path('config.json').read_text());S=[tuple(s)if isinstance(s,list)else s for s in conf['symbols']]
def mk(meta):
 f,sw,perm,roles=meta;v=conf['prefix'][:]
 for j in perm:v+=conf['heads'][f][j][roles[j]]
 return tuple(S[x]for x in v+conf['gate'][f][sw]+conf['suffix'])
def assign(t,word):
 it=iter(word)
 def rec(t):return (rec(t[0]),rec(t[1]))if isnode(t)else next(it)
 return rec(t)
trees=[];ids={};words=[];masks=[]
def intern(t):
 if t in ids:return ids[t]
 if isnode(t):
  a,b=map(intern,t);word=words[a]+words[b];mask=masks[a]|masks[b]
 else:word=(t,);mask=0
 q=len(trees);ids[t]=q;trees.append(t);words.append(word);masks.append(mask|(1<<q)if isnode(t)else 0);return q
base=(0,0,tuple(range(6)),(0,)*6)
metas=[base]
for j in range(6):
 for v in range(1,len(conf['heads'][0][j])):
  roles=[0]*6;roles[j]=v;metas.append((0,0,tuple(range(6)),tuple(roles)))
for sw in [1]:metas.append((0,sw,tuple(range(6)),(0,)*6))
for t in [initial]:intern(t)
for meta in metas:intern(assign(initial,mk(meta)))
print('dictionary',len(trees),'metas',len(metas),flush=True)
# Deduplicate word options by their structural cost masks (one tuple per equal word)
lookup=defaultdict(list)
for q,ww in enumerate(words):lookup[ww].append(q)
for ww,qs in lookup.items():
 lookup[ww]=sorted(qs,key=lambda q:masks[q].bit_count())[:4]

def parse(word,B=64):
 n=len(word);options=[]
 for i in range(n):
  oo=[]
  for j in range(i+1,n+1):
   for q in lookup.get(word[i:j],[]):oo.append(q)
  options.append(oo)
 dp=[{}for _ in range(n+1)];dp[0][0]=()
 for i in range(n):
  beam=sorted(dp[i].items(),key=lambda t:t[0].bit_count()+len(t[1]))[:B];dp[i]={}
  for mask,parts in beam:
   for q in options[i]:
    j=i+len(words[q]);m=mask|masks[q];p=parts+(q,)
    if m not in dp[j] or len(p)<len(dp[j][m]):dp[j][m]=p
 m,p=min(dp[n].items(),key=lambda t:t[0].bit_count()+len(t[1]));return m.bit_count()+len(p)-1,p

best=999;selected=[]
for i,meta in enumerate(metas):
 ww=mk(meta);c,parts=parse(ww,128)
 if c<best:best=c;print('BEST',best,meta,'parts',len(parts),'seconds',time.time()-start,flush=True)
 if c<=69:
  selected.append({'cost':c,'meta':meta,'parts':[encode(trees[q])if isnode(trees[q])else{'terminal':trees[q]}for q in parts]})
  Path('dictionary_candidates.json').write_text(json.dumps(selected,indent=2))
 print('meta',i,'cost',c,'seconds',time.time()-start,flush=True)
print('DONE',len(metas),'best',best,flush=True)
