import json,functools,itertools
from pathlib import Path
exec(open('/tmp/k219_probe.py').read().split('# finite Cartesian')[0])
def leafcount(t):return 1 if leaf(t) else leafcount(t[0])+leafcount(t[1])
def nset(t):
 s=set()
 def go(t):
  if t in s:return
  s.add(t)
  if not leaf(t):go(t[0]);go(t[1])
 go(t);return s
states=json.load(open('/tmp/k219-probe.json'))['states'];results=[]
for removed in ({4606,4607},{4718,4719,4720},{4606,4607,4718,4719,4720}):
 keep=[i for i in range(len(rows)) if i not in removed];mp={i:j for j,i in enumerate(keep)}
 def skip(i):
  seen=set()
  while i in removed:
   assert i not in seen;seen.add(i)
   o,r,ts=G[i]
   assert states[i] is None or o=='CD' and states[i][r]==1
   i=ts[0]
  return mp[i]
 counter=iter(range(len(rows)))
 def prune(t):
  if leaf(t):return None if next(counter) in removed else t
  a,b=prune(t[0]),prune(t[1]);return b if a is None else a if b is None else (a,b)
 t=prune(tree);rs=leaves(t)
 # Retarget only explicit break/continue to exact old quotient, preserving op kind.
 adjusted=[];changes=[];ok=True
 for ni,(p,o,r) in enumerate(rs):
  want=tuple(skip(j) for j in G[keep[ni]][2]);gg=graph(rs)[ni]
  if o in ('CB','CC') and gg[2]!=want:
   found=False
   for k in range(1,9):
    alt=rs.copy();alt[ni]=(p,o,k)
    if graph(alt)[ni][2]==want:
     changes.append([keep[ni],o,r,k]);rs=alt;found=True;break
   if not found:ok=False;break
  elif gg[2]!=want:ok=False;changes.append(['BAD',keep[ni],gg[2],want]);break
 if ok:
  dd={p:(o,r) for p,o,r in rs}
  def parse(p=''):return dd[p] if p in dd else (parse(p+'0'),parse(p+'1'))
  t=parse();score=len(nset(t))
 else:score=None
 result={'removed':sorted(removed),'quotient_exact':ok,'dag':score,'changes':changes,'sites':rs if ok else None};results.append(result)
 print({k:v for k,v in result.items() if k!='sites'},flush=True)
Path('/tmp/k219-prune-result.json').write_text(json.dumps(results,indent=2)+'\n')
