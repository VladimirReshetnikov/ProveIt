from search_folds import *
import sys
rows=read_table(BASE/'sources/bb196/data/pa196.tm')
k=int(sys.argv[1]) if len(sys.argv)>1 else 4
reach=reachable(rows,k)
n=max(q for q,b in rows)+1
start=time.time();pairs=[];hits=[]
for a in range(1,n):
  for b in range(1,n):
    if a==b:continue
    check=local_check(rows,a,b,{},reach,k)
    if check:
        hit={'a':a,'b':b,'replacements':{},'lengths':check};hits.append(hit);print('NOEDIT',hit,flush=True)
    for x in (0,1):
      if rows[a,1-x]==rows[b,1-x]:continue
      check=local_check(rows,a,b,{},reach,k,branches=(1-x,),forbid=(a,x))
      if not check:continue
      pairs.append([a,b,x]);print('PAIR',a,b,x,flush=True)
      for helper,w,d in itertools.product(range(n),(x,1-x),(-1,1)):
        if helper==b:continue
        repl={(a,x):(w,d,helper)}
        chk=local_check(rows,a,b,repl,reach,k)
        if chk:
          hit={'a':a,'b':b,'symbol':x,'helper':helper,'write':w,'move':d,'lengths':chk}
          hits.append(hit);print('HIT',hit,flush=True)
  if a%20==0:print('progress',a,len(pairs),len(hits),time.time()-start,flush=True)
(BASE/f'research/general_k{k}.json').write_text(json.dumps({'pairs':pairs,'hits':hits},indent=2))
print('DONE',time.time()-start,flush=True)
