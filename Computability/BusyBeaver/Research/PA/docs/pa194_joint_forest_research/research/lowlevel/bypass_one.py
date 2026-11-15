from common import *
order=list(range(len(cs)));random.Random(4837).shuffle(order);order[:0]=[0,8,20,80,100,200,300,400,1000,2000,3000,4000]
allqs=sorted({q for q,b in rows});incoming=collections.defaultdict(list)
for k,a in rows.items():
 if k[0]!=a[2]:incoming[a[2]].append(k)
qs=[q for q in allqs if q not in r.BOXSTATES|{84,74} and len(incoming[q])==1];hist=collections.Counter();hits=[];n=0;t=time.monotonic()
for q in qs:
 key=incoming[q][0]
 if key[0] in r.BOXSTATES:continue
 rr={k:a for k,a in rows.items() if k[0]!=q}
 for act in itertools.product((0,1),(False,True),(p for p in allqs if p!=q)):
  rr[key]=act;failed=None
  for j,k in enumerate(order):
   if r.run(rr,cs[k],fuel=1500) is None:failed=j;break
  hist[min(j,100000)]+=1;n+=1
  if failed is None:
   out=B/f'bypass_hit_{q}_{key[0]}_{key[1]}_{act[0]}{int(act[1])}_{act[2]}.tm';out.write_text(''.join(f'{p} {bit} {w} {"R" if d else "L"} {target}\n'for(p,bit),(w,d,target)in sorted(rr.items())))
   rec={'delete':q,'key':key,'new_action':act,'path':str(out)};hits.append(rec);print('HIT',rec,flush=True)
  elif j>0:
   k=order.pop(j);order.insert(0,k)
 print('delete',q,'trials',n,'elapsed',time.monotonic()-t,'hits',len(hits),flush=True)
(B/'bypass_one_results.json').write_text(json.dumps({'eligible_states':qs,'trials':n,'elapsed':time.monotonic()-t,'hits':hits,'fail_order_hist':dict(hist)},indent=2));print('DONE',n,time.monotonic()-t,len(hits),flush=True)
