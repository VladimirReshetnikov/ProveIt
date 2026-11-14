from collections import defaultdict
from functools import lru_cache
from pathlib import Path
import json,sys
sys.dont_write_bytecode=True
import source_inventory as I
L=I.L
ID=tuple(tuple(int(i==j)for j in range(10))for i in range(9))
def compose(a,b):return tuple(tuple(sum(a[i][j]*b[j][k]for j in range(9))+(a[i][9]if k==9 else 0)for k in range(10))for i in range(9))
def modify(r,delta=0,zero=False):
 m=[list(x)for x in ID]
 if zero:m[r]=[0]*10
 else:m[r][9]+=delta
 return tuple(map(tuple,m))
def graph(n):
 rows=L.sites(n);N=len(rows);ints={}
 for i,(p,o,a)in enumerate(rows):
  for k in range(len(p)+1):
   key=p[:k]
   if key not in ints:ints[key]=[i,i+1]
   else:ints[key][1]=i+1
 def unwind(p,bit,count):
  for k in range(len(p)-1,-1,-1):
   if p[k]==bit:
    count-=1
    if count==0:return ints[p[:k]][int(bit=='0')]
  raise ValueError('unclosed')
 edges=[]
 for i,(p,o,a)in enumerate(rows):
  if o=='CI':e=[i+1]
  elif o=='CD':e=[unwind(p,'0',1),i+1]
  elif o=='CB':e=[unwind(p,'0',a)]
  elif o=='CC':e=[unwind(p,'1',a)]
  else:raise ValueError('halt')
  edges.append(e)
 return rows,edges

def components(edges):
 N=len(edges);ind={};low={};stack=[];on=set();out=[]
 def visit(v):
  ind[v]=low[v]=len(ind);stack.append(v);on.add(v)
  for w in edges[v]:
   if w==N:continue
   if w not in ind:visit(w);low[v]=min(low[v],low[w])
   elif w in on:low[v]=min(low[v],ind[w])
  if low[v]==ind[v]:
   comp=[]
   while True:
    w=stack.pop();on.remove(w);comp.append(w)
    if w==v:break
   out.append(comp)
 for v in range(N):
  if v not in ind:visit(v)
 return out
@lru_cache(None)
def effect(n):
 if L.boundary(n)!=(0,0,False):return None
 rows=L.sites(n)
 if len(rows)>500:return None
 try:rows,edges=graph(n)
 except ValueError:return None
 N=len(rows);comps=components(edges);membership={v:i for i,c in enumerate(comps)for v in c};models={}
 for i,vs in enumerate(comps):
  C=set(vs)
  if len(vs)==1 and vs[0]not in edges[vs[0]]:continue
  tests=[v for v in vs if rows[v][1]=='CD']
  if len(tests)!=1:return None
  test=tests[0];r=rows[test][2]
  if edges[test][0]in C or edges[test][1]not in C:return None
  def path(start):
   v=start;seen=set();inc=[0]*9
   while v!=test:
    if v in seen or v not in C:raise ValueError('cycle')
    seen.add(v);o,a=rows[v][1:]
    if o=='CI':inc[a]+=1
    elif o not in('CB','CC'):raise ValueError('branch')
    v=edges[v][0]
   return inc,seen
  try:
   cyc,seen=path(edges[test][1])
   if seen|{test}!=C or cyc[r]:return None
   for entry in vs:
    pre,_=path(entry);m=[list(x)for x in ID]
    m[r]=[0]*10
    for j in range(9):
     if j!=r:m[j][r]+=cyc[j];m[j][9]+=pre[j]
    models[entry]=(tuple(map(tuple,m)),edges[test][0])
  except ValueError:return None
 processing=set();cache={N:ID}
 def solve(v):
  if v in cache:return cache[v]
  if v in processing:return None
  processing.add(v);o,a=rows[v][1:]
  if v in models:
   m,z=models[v];after=solve(z);ans=compose(after,m)if after is not None else None
  elif o=='CD':
   z=solve(edges[v][0]);p=solve(edges[v][1]);p=compose(p,modify(a,-1))if p is not None else None
   if z is not None and p is not None and all(z[i][j]==p[i][j]for i in range(9)for j in range(10)if j!=a):ans=p
   else:ans=None
  else:
   after=solve(edges[v][0]);ans=compose(after,modify(a,1))if after is not None and o=='CI'else after
  processing.remove(v);cache[v]=ans;return ans
 return solve(0)

def main():
 b=I.base;all=[]
 for cls,tp,sp in [('A',b/'machine/variant_plain/u208.native.tm',b/'machine/variant_plain/u208.sites.json'),('B',b/'machine/u208.native.tm',b/'machine/u208.sites.json')]:
  t=I.read(tp);ss=json.loads(sp.read_text());root,occ,_=I.inventory(t,ss);groups=defaultdict(list);records=[]
  for q,os in occ.items():
   sigs=set(effect(n)for _,n in os)
   if None in sigs or len(sigs)!=1:continue
   sig=next(iter(sigs));groups[sig].append(q);records.append({'state':q,'primitives':len(L.sites(os[0][1])),'matrix':sig})
  donors=[{'states':qs,'matrix':m}for m,qs in groups.items()if len(qs)>1]
  print(cls,'recognized',[(x['state'],x['primitives'])for x in records],'donors',[x['states']for x in donors],flush=True)
  all.append({'class':cls,'recognized':records,'donors':donors})
 Path('analysis/comparison/linear_donors.json').write_text(json.dumps(all,indent=2)+'\n')
if __name__=='__main__':main()
