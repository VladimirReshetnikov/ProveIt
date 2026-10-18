from pathlib import Path
from collections import Counter
import hashlib,json,sys
if not __debug__ or sys.flags.optimize:raise RuntimeError("Assertions required")
base=Path(__file__).resolve().parent.parent/'runtime/candidate_1_old.tm'
def read(p):
 t={}
 for s in p.read_text().splitlines():
  if s and not s.startswith('#'):
   q,b,w,d,r=s.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(r))
 return t
t=read(base); old=read(Path(__file__).resolve().parent.parent/'runtime/baseline242_old.tm')
def run(tab,n):
 q,h,ones,c=95,0,set(),Counter()
 for _ in range(n):
  b=int(h in ones);c[q,b]+=1;w,d,q=tab[q,b]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 return q,h,ones,c
q,h,ones,c=run(old,407979)
assert c[39,1]>=0
n=407979+4*c[17,0]+2*(c[17,1]+c[39,0]+c[39,1])
a,b,x,k=run(t,n)
assert (a,b,x)==(q,h,ones)
assert (a,b,len(x))==(96,-5,351)
r={'candidate_inherited_label_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'states':241,'rows':len(t),'counts':{str(k):c[k] for k in [(17,0),(17,1),(39,0),(39,1)]},'exact_blank_steps':n,'old_state':a,'head':b,'ones':len(x),'complete_tape_identical_to_verified242':True}
p=Path(__file__).parent/'boot_result.json';p.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
