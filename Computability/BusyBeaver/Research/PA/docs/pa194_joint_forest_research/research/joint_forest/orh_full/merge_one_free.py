from common import *
order=list(range(len(cs)));random.Random(722).shuffle(order);order[:0]=[0,8,20,80,100,200,300,400,1000,2000,3000,4000]
qs=sorted({q for q,b in rows}-r.BOXSTATES-{84,74});allqs=sorted({q for q,b in rows});hist=collections.Counter();hits=[];n=0;t=time.monotonic();pairs=0
for a,b in itertools.combinations(qs,2):
 for common in(0,1):
  if rows[a,common]!=rows[b,common]:continue
  pairs+=1
  rr={ (q,bit):(w,d,b if target==a else target) for(q,bit),(w,d,target)in rows.items() if q!=a}
  for act in itertools.product((0,1),(False,True),(q for q in allqs if q!=a)):
   rr[b,1-common]=act;failed=None
   for j,k in enumerate(order):
    if r.run(rr,cs[k],fuel=1500) is None:failed=j;break
   hist[min(j,100000)]+=1;n+=1
   if failed is None:
    out=B/f'free_hit_{a}_{b}_{common}_{act[0]}{int(act[1])}_{act[2]}.tm';out.write_text(''.join(f'{q} {bit} {w} {"R" if d else "L"} {target}\n'for(q,bit),(w,d,target)in sorted(rr.items())))
    rec={'a':a,'b':b,'common':common,'new_action':act,'path':str(out)};hits.append(rec);print('HIT',rec,flush=True)
   elif j>0:
    k=order.pop(j);order.insert(0,k)
  print('pair',pairs,a,b,'trials',n,'elapsed',time.monotonic()-t,'hits',len(hits),flush=True)
(B/'merge_one_free_results.json').write_text(json.dumps({'pairs':pairs,'trials':n,'elapsed':time.monotonic()-t,'hits':hits,'fail_order_hist':dict(hist)},indent=2));print('DONE',n,time.monotonic()-t,len(hits),flush=True)
