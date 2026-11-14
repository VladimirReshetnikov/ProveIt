"""Project the inductive radius-six blank closure to nine cells.

Intersect its central five cells with a separately justified source invariant.
"""
from collections import deque
from pathlib import Path
import argparse,json,hashlib
ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);a=ap.parse_args()
table={}
for l in (a.directory/'table.txt').read_text().splitlines():
 q,b,w,d,t=l.split();table[int(q),int(b)]=int(w),1 if d=='R' else -1,int(t)
N=len(table)//2
small={q:set()for q in range(N)}
for l in (a.directory/'contexts.txt').read_text().splitlines():
 q,b,m=map(int,l.split());small[q].add(m)
seen={(0,0)};todo=deque(seen);wide={q:set()for q in range(N)}
mask=(1<<13)-1
while todo:
 q,m=todo.popleft();read=(m>>6)&1
 if ((m>>4)&31) in small[q]:wide[q].add((m>>2)&511)
 w,d,t=table[q,read]
 if t==N:continue
 m=(m&~64)|(w<<6)
 for b in (0,1):
  nm=((m>>1)|(b<<12)) if d==1 else ((m<<1)&mask)|b
  x=t,nm
  if x not in seen:seen.add(x);todo.append(x)
data=''.join(f'{q} {(m>>4)&1} {m}\n'for q in range(N)for m in sorted(wide[q]))
(a.directory/'contexts9.txt').write_text(data)
rec=dict(closure_windows=len(seen),five_cell_contexts=sum(map(len,small.values())),nine_cell_contexts=sum(map(len,wide.values())),sha256=hashlib.sha256(data.encode()).hexdigest())
(a.directory/'contexts9.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps(rec))
