from forest_common import *
P=B/'runtime193.native.tm'
rows={}
for l in P.read_text().splitlines():
 q,b,w,d,n=l.split();rows[int(q),int(b)]=int(w),d=='R',int(n)
affected=collections.defaultdict(list);started=time.monotonic()
for i,c in enumerate(cs):
 seen=set();assert r.run(rows,c,observe=lambda s:seen.add(s[0]),fuel=1500)is not None
 for q in seen:affected[q].append(i)
allqs=sorted({q for q,b in rows});counts={};neutral=[];hits=[];trials=0
# exact source-frame detector, allowing arbitrary work and spare values at sites25--44.
paths={i:tuple(map(int,sites[i][0]))for i in range(25,45)}
def checkframe(h,ones):
 if not ones or min(ones)!=h-1:return None
 markers=[k for k in ones if k>=h+48 and k-1 not in ones]
 if not markers:return None
 marker=min(markers)
 if any(h+max(map(len,paths.values()))<=k<marker for k in ones):return None
 matches=[]
 for i,p in paths.items():
  if all(int(h+k in ones)==x for k,x in enumerate(p)) and not any(h+len(p)<=k<marker for k in ones):matches.append(i)
 if not matches:return None
 pos=marker+1;values=[];last=max(ones)
 while pos<=last:
  if pos in ones:return None
  pos+=1;n=0
  while pos in ones:pos+=1;n+=1
  if n==0:return None
  values.append(n-1)
 if len(values)<10:return None
 return {'sites':matches,'registers':values,'gap':marker-h,'head':h}
def startup(rr,cap=200000):
 q,h,ones=74,0,set();lo=hi=0
 for t in range(cap):
  if q==84:
   f=checkframe(h,ones)
   if f:return t,f
  if q==254:return None
  bit=int(h in ones);w,d,n=rr[q,bit]
  if not bit and n==q and ((d and h>=hi)or(not d and h<=lo)):return None
  if w:ones.add(h);lo=min(lo,h);hi=max(hi,h)
  else:ones.discard(h)
  q=n;h+=1 if d else -1
 return None
for q in allqs:
 if q in r.BOXSTATES:continue
 order=affected[q][:];random.Random(q).shuffle(order)
 for bit in(0,1):
  original=rows[q,bit];nn=0;tested=0
  for act in itertools.product((0,1),(False,True),allqs):
   if act==original:continue
   rows[q,bit]=act;failed=None
   for j,k in enumerate(order):
    if r.run(rows,cs[k],fuel=1500)is None:failed=j;break
   trials+=1;tested+=1
   if failed is not None:
    if j>0:k=order.pop(j);order.insert(0,k)
    continue
   nn+=1;rec={'key':[q,bit],'action':act,'affected_contracts':len(order)};neutral.append(rec)
   st=startup(rows)
   if st is not None:
    rec=dict(rec,startup=st);hits.append(rec);print('HIT',rec,flush=True)
    dest=B/f'startup_hit_{q}_{bit}_{act[0]}{int(act[1])}_{act[2]}.tm';dest.write_text(''.join(f'{p} {b} {w} {"R" if d else "L"} {n}\n'for(p,b),(w,d,n)in sorted(rows.items())))
  rows[q,bit]=original;counts[str((q,bit))]=[tested,nn,len(order)]
 print('q',q,'affected',len(order),'trials',trials,'neutrals',len(neutral),'hits',len(hits),'seconds',time.monotonic()-started,flush=True)
 (B/'global_neutral_progress.json').write_text(json.dumps({'counts':counts,'neutral':neutral,'hits':hits,'trials':trials,'seconds':time.monotonic()-started},indent=2))
(B/'global_neutral_result.json').write_text(json.dumps({'counts':counts,'neutral':neutral,'hits':hits,'trials':trials,'seconds':time.monotonic()-started},indent=2));print('DONE',trials,len(neutral),len(hits),flush=True)
