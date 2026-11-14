import sys,json,collections
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1] / "verification"))
known_blank = "--known-blank" in sys.argv
from core import *
rows,labels=machine();cs=contracts();RAD=12
contexts=collections.defaultdict(set)
def take(segs,n):
 uncertain=False
 out=[]
 for x in segs:
  if x[0]=='b':out.append(x[1])
  elif x[0]=='r':
   out += [x[1]] * min(n-len(out),x[3])
   if x[2] and len(out)<n:uncertain=True;break
  else:out.append(0);uncertain=True;break
  if len(out)>=n:break
 return tuple(out[:n])+((0 if known_blank and not uncertain else -1),)*max(0,n-len(out))
def observe(s):
 q,onl,l,r=s
 if q not in BOXSTATES and not onl and r and r[0][0]=='b':
  contexts[q,r[0][1]].add(tuple(reversed(take(l,RAD)))+take(r,RAD+1))
assert validate(rows,cs,observe)['ok']
idx={q:i for i,q in enumerate(labels)}
states=[q for q in labels[:-1] if q not in BOXSTATES and q!=84 and all((q,b) in contexts for b in (0,1))]
with open('experiments/contexts.dat','w') as f:
 print(len(labels)-1,RAD,len(states),file=f)
 print(*[idx[q] for q in states],file=f)
 for q in labels[:-1]:
  for b in (0,1):
   w,d,n=rows[q,b];print(w,int(d),idx[n],file=f)
 for q in labels[:-1]:
  for b in (0,1):
   ts=sorted(contexts.get((q,b),[]));print(len(ts),file=f)
   for t in ts:print(*t,file=f)
Path('experiments/labels.json').write_text(json.dumps(labels))
print('exported',len(states),sum(map(len,contexts.values())))
