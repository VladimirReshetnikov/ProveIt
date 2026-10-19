from pathlib import Path
from itertools import combinations,product
import json,argparse,hashlib
B=Path(__file__).resolve().parent
P=B.parent/'reference/zfc240_old.tm'
a=argparse.ArgumentParser();a.add_argument('--table',type=Path,default=P);a.add_argument('--output',type=Path,default=B/'permutation_quotient_screen.json');args=a.parse_args()
rows={}
for line in args.table.read_text().splitlines():
 if line and not line.startswith('#'):
  q,b,w,d,t=line.split();rows[int(q),int(b)]=(int(w),d,int(t))
SKIP=(60,44,31,56,38,40,28,64,69)
MUTABLE={18,21,25,47,49,53,65,70,93,169,173,201}
assert len(rows)==480 and {q for q,b in rows}.issuperset(MUTABLE)
assert all(rows[q,1][2]in SKIP for q in MUTABLE)
qs=sorted({q for q,b in rows}|{254})
pairs={(a,b)for a in qs for b in qs if(a==254)==(b==254)and(a==254 or all(rows[a,s][:2]==rows[b,s][:2]for s in(0,1)))}
initial=len(pairs)
iterations=0
while True:
 iterations+=1;nextp=set()
 for a,b in pairs:
  if a==b:nextp.add((a,b));continue
  good=True
  for s in(0,1):
   ta,tb=rows[a,s][2],rows[b,s][2]
   ma=(s==1 and a in MUTABLE);mb=(s==1 and b in MUTABLE)
   if not ma and not mb:ok=(ta,tb)in pairs
   elif ma and not mb:ok=any((x,tb)in pairs for x in SKIP)
   elif mb and not ma:ok=any((ta,y)in pairs for y in SKIP)
   elif ta==tb:ok=True
   else:ok=any(x!=y and(x,y)in pairs for x in SKIP for y in SKIP)
   if not ok:good=False;break
  if good:nextp.add((a,b))
 if nextp==pairs:break
 pairs=nextp
candidates=sorted((a,b)for a,b in pairs if a<b)
result=dict(status='GREATEST_RELATION_OVERAPPROXIMATION_COMPLETE',table_sha256=hashlib.sha256(args.table.read_bytes()).hexdigest(),initial_pairs=initial,iterations=iterations,possible_state_pairs=candidates,mutable_rows=[[q,1]for q in sorted(MUTABLE)],skip_states=SKIP,interpretation='Any exact step bisimulation quotient after any physical permutation is included. Selector images may vary independently at different occurrences in this overapproximation, so surviving pairs would still require solving one global bijection. No survivors rules out exact transition bisimulation savings in this permutation family, not context-dependent sharing or new initialization.')
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
