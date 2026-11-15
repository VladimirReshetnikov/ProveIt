from forest_common import *
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
