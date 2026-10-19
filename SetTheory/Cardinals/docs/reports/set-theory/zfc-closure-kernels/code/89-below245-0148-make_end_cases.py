from pathlib import Path
import json
BASE=Path(__file__).resolve().parents[1]
T={}
for line in (BASE/'inputs/routing245_old.tm').read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,t=line.split();T[int(q),int(b)]=int(w),1 if d=='R' else -1,int(t)
def B(v):return [0]+[1]*(v+1)
def C(v):return [1,0]+[1]*v
cases=[]
for kind in ['inc','zero','pos']:
 for pre in [[],[0],[1],[2],[0,1],[2,0],[0,0,2],[1,3,0]]:
  for y in ([0] if kind=='inc' else [0,1,3]):
   left=([0]*32+[1]+([0,1] if kind=='inc' else [])+sum(map(C,pre),[])+[1,0])
   right=[0] if kind=='inc' else ([0]+[1]*(y+1)+B(2)+B(0) if kind=='zero' else [1]*(y+1)+B(2)+B(0))
   ones={i for i,b in enumerate(left+right) if b};h=len(left);q=75;start=h;initial=set(ones)
   for tick in range(3000):
    w,d,q=T[q,int(h in ones)]
    if w:ones.add(h)
    else:ones.discard(h)
    h+=d
    if q==7:break
   else:raise AssertionError(('baseline failure',kind,pre,y))
   assert h>=0
   cases.append(dict(kind=kind,pre=pre,y=y,start=start,target_head=h,initial=sorted(initial),target=sorted(ones),steps=tick+1))
with (BASE/'inputs/end_cases.txt').open('w') as f:
 print(len(T),file=f)
 for(q,b),(w,d,t)in sorted(T.items()):print(q,b,w,d,t,file=f)
 print(len(cases),file=f)
 for c in cases:
  print(int(c['kind']=='inc'),c['start'],c['target_head'],len(c['initial']),*c['initial'],len(c['target']),*c['target'],file=f)
(BASE/'results/end_cases.json').write_text(json.dumps(cases,indent=2)+'\n')
print(len(cases),'cases; maximum',max(c['steps'] for c in cases),'steps')
