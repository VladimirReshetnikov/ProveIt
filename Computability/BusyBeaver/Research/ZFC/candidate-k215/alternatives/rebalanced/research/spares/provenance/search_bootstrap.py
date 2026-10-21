from pathlib import Path
import sys,json,time,gzip,importlib.util
BASE=Path('/workspace/scratch/1d1a80d76be0/ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-k215')
sys.path.insert(0,str(BASE/'code/runtime-inputs/runtime'));import independent_runtime as r
m={int(k):int(v)for k,v in json.loads((BASE/'code/runtime-inputs/inputs/legacy_mapping.json').read_text()).items()}
T=r.table(BASE/'k215.native.tm');m.update({q:q+1000 for q,b in T if q not in m});inv={v:k for k,v in m.items()};L={(m[q],b):(w,d,m.get(z,z))for(q,b),(w,d,z)in T.items()};L[m[198],0]=(0,-1,m[40])
ss=json.loads((BASE/'sites215.json').read_text());cs=json.loads(gzip.decompress((BASE/'verification/root-run1/runtime/runtime_cases.json.gz').read_bytes()))
startup=json.load(open('experiments/spares/append-zero/startup-early.json'));changed=set((q,b)for q,h,b,w,d,z in startup['trace']);changed.add((startup['state'],0));changed.discard((198,0));changed=sorted(changed)
fixtures={}
for q,b in changed:
 hits=[c for c in cs if [m[q],b] in c['rows']]
 fixtures[q,b]=[]
 for c in hits[:1]+hits[-1:]:
  site=ss[c['site_index']];regs=[1]*9
  if site[1]=='CD':regs[site[2]]=1 if c['positive'] else 0
  sp=[1,2];want=r.expected(site,regs,sp)
  if site[1]=='CI':
   nr=regs.copy();nr[site[2]]+=1;pc,shift=r.inc(site[0]);want=((96,-shift,{v-shift for v in r.frame(pc,nr,sp+[0],shift)}),{})
  fixtures[q,b].append((site,regs,sp,want[0] if want else None))
def seed(T,limit=300000):
 q=0;h=0;ones=set()
 for tick in range(limit):
  if q==84 and ones and min(ones)==h-1:
   right=[x for x in sorted(ones)if x>h-1]
   if right and right[0]>=h+64:
    header=right[0];p=header+1;last=max(ones);vals=[]
    while p<=last and p not in ones and p+1 in ones:
     p+=1;n=0
     while p in ones:n+=1;p+=1
     vals.append(n-1)
    if p>last and len(vals)>=10 and vals[0]==vals[2]==vals[7]==0:return dict(status='SEED',steps=tick,head=h,gap=header-h-64,registers=[vals[j]for j in r.PHY],spares=vals[9:],one_cells=sorted(ones))
  bit=int(h in ones)
  if(q,bit)not in T:return None
  w,d,z=T[q,bit]
  if bit==0 and z==q and(not ones or(d==1 and h>max(ones))or(d==-1 and h<min(ones))):return None
  if w:ones.add(h)
  else:ones.discard(h)
  q=z;h+=d
 return None
survivors=[];n=0;fpass=0;t=time.monotonic();N=dict(T);N[198,0]=(0,-1,40)
for q,b in changed:
 key=(m[q],b);old=L[key]
 for w in (0,1):
  for d in (-1,1):
   for target in sorted({q for q,b in T}):
    n+=1;act=(w,d,m[target])
    if act==old:continue
    L[key]=act
    ok=True
    for site,regs,sp,want in fixtures[q,b]:
     conf,ticks,_=r.run(L,site[0],regs,sp,limit=3500)
     if (conf[0]!=254 if want is None else conf!=want):ok=False;break
    if not ok:continue
    fpass+=1;N[q,b]=(w,d,target);st=seed(N);N[q,b]=T[q,b] if(q,b)!=(198,0)else(0,-1,40)
    if st:
     record=dict(row=[q,b,w,d,target],seed=st);survivors.append(record);print('FOUND',record,flush=True)
    L[key]=old
 L[key]=old
 print('ROW',q,b,'trials',n,'finitepasses',fpass,'found',len(survivors),'sec',round(time.monotonic()-t,2),flush=True)
Path('experiments/spares/bootstrap-search.json').write_text(json.dumps(dict(tested=n,finite_pass=fpass,survivors=survivors,seconds=time.monotonic()-t),indent=2))
