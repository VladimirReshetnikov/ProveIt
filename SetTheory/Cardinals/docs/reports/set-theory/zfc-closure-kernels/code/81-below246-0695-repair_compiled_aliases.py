from pathlib import Path
import json,collections,sys,itertools
sys.path.insert(0,str(Path(__file__).parent))
import check_decoder as c
HERE=Path(__file__).parent
T=c.table(HERE/'compiled24_raw.tm');roles={int(n):q for n,q in json.load(open(HERE/'compiled24_raw_roles.json'))['roles'].items()}
E={int(n):v for n,v in json.load(open(HERE.parent/'agent_logic/rotation_zero_candidate_24.json'))['entries'].items()}
hints=json.load(open(HERE.parent/'agent_logic/rotation_zero_physical_hints.json'))['entries']
C=collections.defaultdict(set)
for e in hints:
 q=roles[e['grammar_node']]
 for b in (0,1):
  child=e['children'][b]
  if E[child][0]!='N':continue
  target=roles[child]
  for oc in e['occurrences']:C[q,b].add((oc['path'],target))

def valid(q,b,entry):
 for p,target in C[q,b]:
  for right in range(4):
   word='1'+p+str(b)+f'{right:02b}';tape={i-len(p)-1:1 for i,x in enumerate(word) if x=='1'};old=tape.copy();state=q;h=0
   for tick in range(20):
    if tick and state==target and h==1 and tape==old:break
    if h<-len(p)-1 or h>3:return False
    r=(state,tape.get(h,0))
    if r not in T:return False
    w,d,state=entry if r==(q,b) else T[r]
    if w:tape[h]=1
    else:tape.pop(h,None)
    h+=d
   else:return False
 return True
for row in [(183,1),(250,1),(244,0),(244,1)]:
 good=[]
 for w,d,t in itertools.product(range(2),(-1,1),sorted({q for q,b in T})):
  entry=(w,d,t)
  if valid(*row,entry):good.append(entry)
 print(row,'survivors',good)
 if good:T[row]=good[0]
(HERE/'compiled24_repairable.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {t}\n' for (q,b),(w,d,t) in sorted(T.items())))
