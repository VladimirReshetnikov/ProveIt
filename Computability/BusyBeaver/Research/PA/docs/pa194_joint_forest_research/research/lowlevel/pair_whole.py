from pathlib import Path
import sys,json,itertools,time,collections,random
B=Path(__file__).parent;sys.path.insert(0,str(B/'baseline'));import symbolic_runtime as r
labels=json.loads((B/'baseline/tables/pa194.labels.json').read_text());rows={}
for line in (B/'baseline/tables/pa194.tm').read_text().splitlines():
 q,b,w,d,n=line.split();rows[labels[int(q)],int(b)]=int(w),d=='R',labels[int(n)]
sites=json.loads((B/'baseline/source/pa194.sites.json').read_text());ins=json.loads((B/'baseline/source/pa194.instructions.json').read_text());cs=[]
def frame(i,extra=0,effect=r.PLAIN):return r.frame(tuple(map(int,sites[i][0])),extra,effect)
def target(i,extra=0,effect=r.PLAIN):return r.canonical(frame(i,extra,effect))
for i,c in enumerate(ins):
 s=frame(i)
 if c[0]=='inc':_,n,j=c;cs.append((i,None,s,target(j,0,('x','inc',r.PHYSICAL[n]))))
 elif c[0]=='dec':_,n,z,j=c;cs.extend([(i,(r.PHYSICAL[n],True),s,target(z)),(i,(r.PHYSICAL[n],False),s,target(j,1,('x','dec',r.PHYSICAL[n])))] )
 elif c[0]=='jump':cs.append((i,None,s,target(c[1])))
 else:cs.append((i,None,s,None))
order=list(range(len(cs)));random.Random(237).shuffle(order);order[:0]=[0,8,20,80,100,200,300,400,1000,2000,3000,4000]
qs=sorted({q for q,b in rows}-r.BOXSTATES-{84,74});hist=collections.Counter();hits=[];n=0;t=time.monotonic()
for a,b in itertools.combinations(qs,2):
 for choose in itertools.product((a,b),repeat=2):
  rr={ (q,bit):(w,d,b if target==a else target) for(q,bit),(w,d,target)in rows.items() if q!=a}
  for bit,q in enumerate(choose):
   w,d,target=rows[q,bit];rr[b,bit]=w,d,b if target==a else target
  failed=None
  for j,k in enumerate(order):
   if r.run(rr,cs[k],fuel=1500) is None:failed=j;break
  hist[min(j,100000)]+=1;n+=1
  if failed is None:
   out=B/f'pair_hit_{a}_{b}_{choose[0]}_{choose[1]}.tm';out.write_text(''.join(f'{q} {bit} {w} {"R" if d else "L"} {target}\n'for(q,bit),(w,d,target)in sorted(rr.items())))
   rec={'a':a,'b':b,'choose':choose,'path':str(out)};hits.append(rec);print('HIT',rec,flush=True)
  elif j>0:
   k=order.pop(j);order.insert(0,k)
 if n%1000==0:print(n,'elapsed',time.monotonic()-t,'hits',len(hits),flush=True)
(B/'pair_whole_results.json').write_text(json.dumps({'trials':n,'elapsed':time.monotonic()-t,'hits':hits,'fail_order_hist':dict(hist)},indent=2));print('DONE',n,time.monotonic()-t,len(hits),flush=True)
