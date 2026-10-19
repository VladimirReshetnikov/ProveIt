"""Independent exhaustive replay of arbitrary last-scanner-state replacements.
All steps are literal machine transitions. Exact repeated configurations reject;
no fuel bound is imposed. Reads outside each restored input cylinder reject.
"""
import pathlib,itertools,json,sys,time,hashlib
root=pathlib.Path(__file__).resolve().parent
path=root/'recovered/63/machine/zfc_prefix246_old.tm'
table={}
for line in path.read_text().splitlines():
 if not line.startswith('#'):
  q,b,w,d,s=line.split();table[int(q),int(b)]=int(w),1 if d=='R' else -1,int(s)
del table[74,0];del table[74,1]
labels=sorted({q for q,b in table});actions=list(itertools.product((0,1),(-1,1),labels))
borrow=int(sys.argv[1]) if len(sys.argv)>1 else 2
bases=[]
for k in (6,7):
 hi=12 if k==6 else 13;bases.append((k,-k,hi,{-k}|set(range(2,hi+1))))
for r in range(11):bases.append((8,-8,3+r,set(range(2,3+r))))
cases=[]
for k,lo,hi,ones in bases:
 for bits in itertools.product((0,1),repeat=2*borrow):
  cells=list(range(lo-borrow,lo))+list(range(hi+1,hi+borrow+1))
  initial=frozenset(ones|{j for j,b in zip(cells,bits) if b});cases.append((k,lo-borrow,hi+borrow,initial))
def run(c):
 k,lo,hi,initial=c;q=h=0;q=6;ones=set(initial);seen=set();steps=0
 while True:
  goal=(q==4 and h==-k-1) if k<8 else(q==84 and -8<=h<=1)
  if goal and ones==initial:return None,steps
  if not lo<=h<=hi:return 'exterior',steps
  if (q,int(h in ones)) not in table:return 'missing',steps
  cfg=(q,h,frozenset(ones))
  if cfg in seen:return 'cycle',steps
  seen.add(cfg);w,d,q=table[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d;steps+=1
counts={'cycle':0,'missing':0,'exterior':0};checks=0;survivors=[];maxsteps=0;began=time.monotonic()
for a,b in itertools.product(actions,repeat=2):
 table[58,0]=a;table[58,1]=b
 for c in cases:
  reason,steps=run(c);maxsteps=max(maxsteps,steps);checks+=1
  if reason:counts[reason]+=1;break
 else:survivors.append((a,b))
result=dict(baseline_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),recipes=len(actions)**2,checks=checks,cases=len(cases),borrow_each_side=borrow,rejections=counts,survivors=survivors,maximum_observed_steps=maxsteps,seconds=time.monotonic()-began,no_fuel_bound=True)
(root/f'last_state_python_borrow{borrow}.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
