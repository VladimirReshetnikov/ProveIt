from search_folds import *
rows=read_table(BASE/'sources/bb196/data/pa196.tm')
k=4;reach=reachable(rows,k);H=197;n=196
start=time.time();opts=[]

def find_options(a,b,x,c):
    # Prove the altered branch for all windows reading a particular history bit.
    rs=[set(),set()]
    for q in (a,b):
      for v in reach[q]:
        if ((v>>k)&1)==x and ((v>>(k-1))&1)==c:rs[q==b].add(v)
    if not any(rs):return []
    rr=[set() for _ in reach];rr[a]=rs[0];rr[b]=rs[1]
    found=[]
    for w,d,t in itertools.product((c,1-c),(-1,1),range(n)):
      if t==b:continue
      replacement={(a,x):(x,-1,H),(H,c):(w,d,t)}
      lens=local_check(rows,a,b,replacement,rr,k,branches=(x,),limit=31)
      if lens:found.append((w,d,t))
    return found

# Our checker needs the helper rows present; the opposite row is an invalid halt.
rows[H,0]=(0,1,196);rows[H,1]=(1,1,196)
for a in range(1,n):
  for b in range(a+1,n):
    diff=[x for x in (0,1) if rows[a,x]!=rows[b,x]]
    if len(diff)!=1:continue
    x=diff[0]
    for aa,bb in ((a,b),(b,a)):
      o0=find_options(aa,bb,x,0)
      if not o0:continue
      o1=find_options(aa,bb,x,1)
      if not o1:continue
      option={'a':aa,'b':bb,'symbol':x,'zero':o0,'one':o1};opts.append(option)
      print('OPTION',aa,bb,x,len(o0),len(o1),flush=True)
  if a%30==0:print('progress',a,len(opts),time.time()-start,flush=True)
(BASE/'research/twohelper_options.json').write_text(json.dumps(opts,indent=2))
hits=[]
for p,s in itertools.combinations(opts,2):
  a,b,c,d=p['a'],p['b'],s['a'],s['b']
  if len({a,b,c,d})<4:continue
  zero=set(map(tuple,p['zero']))&set(map(tuple,s['zero']))
  one=set(map(tuple,p['one']))&set(map(tuple,s['one']))
  if not zero or not one:continue
  print('COMPATIBLE',a,b,c,d,len(zero),len(one),flush=True)
  # Global double-mapping handled by canonicalizing both source/table and invariant.
  for z,o in itertools.product(zero,one):
    def mp(q):return a if q==b else c if q==d else q
    changed={key:(w,dr,mp(t)) for key,(w,dr,t) in rows.items() if key[0] not in (b,d)}
    changed[a,p['symbol']]=(p['symbol'],-1,H)
    changed[c,s['symbol']]=(s['symbol'],-1,H)
    changed[H,0]=(z[0],z[1],mp(z[2]));changed[H,1]=(o[0],o[1],mp(o[2]))
    ok=True;lengths={}
    for q in (a,b,c,d):
      for v in reach[q]:
        tp={j-k:(v>>j)&1 for j in range(2*k+1)};dst=tp.copy()
        w,dr,t=rows[q,tp[0]];dst[0]=w;tar=mp(t);newq=mp(q);h=0
        for st in range(1,42):
          if h not in tp or (newq,tp[h]) not in changed:break
          w,dd,newq=changed[newq,tp[h]];tp[h]=w;h+=dd
          if newq==tar and h==dr and tp==dst:
            lengths.setdefault(str((q,(v>>k)&1)),set()).add(st);break
        else:ok=False
        if not (newq==tar and h==dr and tp==dst):ok=False
        if not ok:break
      if not ok:break
    if ok:
      hit={'pairs':[p,s],'helper':[z,o],'lengths':{s:sorted(t) for s,t in lengths.items()}}
      hits.append(hit);print('HIT',hit,flush=True)
(BASE/'research/twohelper_hits.json').write_text(json.dumps(hits,indent=2))
print('DONE',len(opts),len(hits),time.time()-start,flush=True)
