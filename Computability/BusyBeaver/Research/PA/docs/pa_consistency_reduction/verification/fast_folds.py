"""Bounded safe fold selection for optimizer objectives (never overcounts)."""
from pathlib import Path
import sys,collections,random
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'math_reduction/folding'))
import compatible_folds as F

def select(m,options):
 pairs=collections.defaultdict(list)
 for q,r,ds in options:pairs[q,r].append((q,r,ds))
 if len(pairs)<=12 and len(options)<=30:return F.best_subset(m,options)
 pp=list(pairs);degree=collections.Counter(q for qr in pp for q in qr)
 orders=[sorted(pp,key=lambda qr:(degree[qr[0]]+degree[qr[1]],qr)),list(reversed(pp)),pp]
 best=[];tested=0
 for order in orders:
  picked=[];used=set()
  for qr in order:
   if set(qr)&used:continue
   for x in pairs[qr]:
    tested+=1
    if F.check_local(m,picked+[x])[0]:picked.append(x);used.update(qr);break
  if len(picked)>len(best):best=picked
 return best,tested
