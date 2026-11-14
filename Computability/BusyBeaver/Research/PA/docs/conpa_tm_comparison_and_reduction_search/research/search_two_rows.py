from search_folds import *
rows=read_table(BASE/'sources/bb196/data/pa196.tm')
k=4;reach=reachable(rows,k);n=196;start=time.time();hits=[];candidates=[]

for a in range(1,n):
  for b in range(a+1,n):
    if any(rows[a,x]==rows[b,x] for x in (0,1)):continue
    # Two pure decoder states; require their left contexts to distinguish
    # both branches, allowing conditional facts beyond direct predecessor tags.
    if any(rows[q,x][0]!=x for q in (a,b) for x in (0,1)):continue
    ctx={}
    for q in (a,b):
      for x in (0,1):
        ctx[q,x]={(v&((1<<k)-1)) for v in reach[q] if ((v>>k)&1)==x}
    if any(ctx[a,x]&ctx[b,x] for x in (0,1)):continue
    for aa,bb in ((a,b),(b,a)):
      opts=[]
      for x in (0,1):
        ox=[]
        for h in range(n):
          if h==bb:continue
          repl={(aa,x):(x,-1,h)}
          lens=local_check(rows,aa,bb,repl,reach,k,branches=(x,),forbid=(aa,1-x))
          if lens:ox.append(h)
        opts.append(ox)
        if not ox:break
      if len(opts)<2 or not all(opts):continue
      candidates.append([aa,bb,*opts]);print('CAND',aa,bb,opts,flush=True)
      for h0,h1 in itertools.product(*opts):
        repl={(aa,0):(0,-1,h0),(aa,1):(1,-1,h1)}
        lens=local_check(rows,aa,bb,repl,reach,k)
        if lens:
          hit={'a':aa,'b':bb,'h0':h0,'h1':h1,'lengths':lens};hits.append(hit);print('HIT',hit,flush=True)
  if a%20==0:print('progress',a,len(candidates),len(hits),time.time()-start,flush=True)
(BASE/'research/two_rows.json').write_text(json.dumps({'candidates':candidates,'hits':hits},indent=2))
print('DONE',time.time()-start,flush=True)
