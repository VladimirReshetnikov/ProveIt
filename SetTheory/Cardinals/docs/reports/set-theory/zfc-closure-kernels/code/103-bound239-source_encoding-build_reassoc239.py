from pathlib import Path
from collections import Counter
import json,hashlib
HERE=Path(__file__).resolve().parent;BASE=HERE.parent/'baseline/rotation240'
raw=(BASE/'zfc_rotation240_old.tm').read_text();rows={}
for line in raw.splitlines():
 if line.startswith('#'):continue
 q,b,w,d,t=line.split();rows[int(q),int(b)]=int(w),d,int(t)
assert rows[98,0]==(0,'R',23) and rows[98,1]==(1,'R',74)
new=dict(rows);new[98,0]=(0,'R',113);new[98,1]=(1,'R',16)
del new[74,0];del new[74,1]
assert all(t!=74 for w,d,t in new.values());assert len(new)==478
text='#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(new.items()))
(HERE/'reassoc239_old.tm').write_text(text)
D=json.loads((HERE/'mapping.json').read_text());S=D['structures'];occ=[p for p,n in D['pathnode'].items() if n==69]
oldsites=json.loads((BASE/'sites_logical.json').read_text());newsites=[]
for p,op,r in oldsites:
 for pre in occ:
  if p.startswith(pre):
   pp=p[len(pre):]
   assert pp.startswith(('0','10','11'))
   p=pre+('00'+pp[1:] if pp.startswith('0') else '01'+pp[2:] if pp.startswith('10') else '1'+pp[2:])
   break
 newsites.append([p,op,r])
newsites.sort();assert len(newsites)==6455
(HERE/'reassoc239_sites.json').write_text(json.dumps(newsites,indent=2)+'\n')
def boot(table):
 q,h,T=95,0,set();used=Counter()
 for t in range(2000000):
  if t and q==96 and h==-5 and T==target:return dict(status='EXACT_TARGET',steps=t,used_98=used[98],used_74=used[74])
  if q==254:return dict(status='HALT',steps=t,head=h,ones=len(T))
  used[q]+=1;w,d,q=table[q,int(h in T)]
  if w:T.add(h)
  else:T.discard(h)
  h+=1 if d=='R' else -1
 return dict(status='LIMIT',steps=t+1,state=q,head=h,ones=len(T),used_98=used[98],used_74=used[74])
q,h,target=95,0,set()
for t in range(409691):
 w,d,q=rows[q,int(h in target)]
 if w:target.add(h)
 else:target.discard(h)
 h+=1 if d=='R' else -1
assert q==96 and h==-5 and len(target)==351
result={'rows':478,'states':239,'deleted':74,'patch':[{'state':98,'read':b,'old':rows[98,b],'new':new[98,b]} for b in (0,1)],'source_roots':occ,'leaves':len(newsites),'zero_run':max(max(map(len,p.split('1'))) for p,_,_ in newsites),'max_depth':max(map(len,[p for p,o,r in newsites])),'boot':boot(new),'table_sha256':hashlib.sha256(text.encode()).hexdigest()}
(HERE/'reassoc239_build.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
