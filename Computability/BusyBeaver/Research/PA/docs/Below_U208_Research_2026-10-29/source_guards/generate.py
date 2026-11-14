"""Product category fixed point: each mask denotes a subset of {0,1,2,>=3}."""
from pathlib import Path
from collections import deque
import json,hashlib,argparse

def graph(rows):
 leaves={p:i for i,(p,op,a)in enumerate(rows)};bounds={}
 def visit(p):
  if p in leaves:r=(leaves[p],leaves[p]+1)
  else:
   l,h=visit(p+'0'),visit(p+'1')
   if l[1]!=h[0]:raise ValueError('order')
   r=l[0],h[1]
  bounds[p]=r;return r
 if visit('')!=(0,len(rows)):raise ValueError('root')
 def jump(p,e,k):
  for j in range(len(p)-1,-1,-1):
   if p[j]==e:
    k-=1
    if not k:return bounds[p[:j]][int(e=='0')]%len(rows)
  return 0
 return [[jump(p,'0',1),(i+1)%len(rows)]if op=='CD'else[jump(p,'0',a)]if op=='CB'else[jump(p,'1',a)]if op=='CC'else[(i+1)%len(rows)]if op=='CI'else[]for i,(p,op,a)in enumerate(rows)]
def transfer(rows,g,i,s):
 _,op,a=rows[i]
 if op=='CI':
  t=s.copy();t[a]=sum(1<<k for k in set(min(j+1,3)for j in range(4)if s[a]>>j&1));return [(g[i][0],t)]
 if op=='CD':
  out=[]
  if s[a]&1:
   t=s.copy();t[a]=1;out.append((g[i][0],t))
  if s[a]&14:
   t=s.copy();t[a]=(1 if s[a]&2 else 0)|(2 if s[a]&4 else 0)|(12 if s[a]&8 else 0);out.append((g[i][1],t))
  return out
 return [(j,s.copy())for j in g[i]]
def main(src,out):
 raw=src.read_bytes();rows=json.loads(raw);g=graph(rows);states=[None]*len(rows);seed=[1,0,13,0,0,1,0,0,1];states[136]=[1<<min(v,3)for v in seed];q=deque([136]);queued={136};steps=0
 while q:
  i=q.popleft();queued.remove(i)
  for j,t in transfer(rows,g,i,states[i]):
   new=t if states[j]is None else[a|b for a,b in zip(states[j],t)]
   if new!=states[j]:
    states[j]=new
    if j not in queued:q.append(j);queued.add(j)
  steps+=1
 cert={'source_sha256':hashlib.sha256(raw).hexdigest(),'seed_ordinal':136,'seed_registers':seed,'domain':['0','1','2','>=3'],'states':states,'graph':g}
 out.write_text(json.dumps(cert,indent=2));print(json.dumps({'status':'GENERATED','iterations':steps,'reachable_sites':sum(s is not None for s in states),'dead':[i for i,s in enumerate(states)if s is None],'always_zero_CD':[i for i,(p,op,a)in enumerate(rows)if op=='CD'and states[i]is not None and states[i][a]==1]}))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('output',type=Path);a=p.parse_args();main(a.source,a.output)
