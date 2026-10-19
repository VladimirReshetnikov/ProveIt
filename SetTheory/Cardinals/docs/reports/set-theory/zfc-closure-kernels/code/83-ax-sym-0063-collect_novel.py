from pathlib import Path
import sys,json,random,time,hashlib
from collections import Counter
import seeded_order as s
rng=random.Random(246202);out=Path(__file__).with_name('novel_candidates');out.mkdir(exist_ok=True)
original=s.a.PREFIX+sum(s.a.ROW_WORDS,())+s.a.SUFFIX
seen=set();best=(1000,1000,1000);records=[];champ=(list(range(8)),[0]*8,False);start=time.monotonic()
# Optional one-read u/b exchange in the Luk row, followed by a,b,c permutation.
def swap_ub(f):
 if f=='u':return 'b'
 if f=='b':return 'u'
 if isinstance(f,tuple):return f[0],swap_ub(f[1]),swap_ub(f[2])
 return f
luk=[]
for perm in s.ROLE_PERMS:
 f=s.subst(swap_ub(s.a.ROWS[1]),perm)
 macros=s.a.theory.emit(f)
 assert macros.count(158)==1 and macros.count(208)==1
 word=tuple(t for m in macros for t in s.a.MACROS[m])
 luk.append(tuple(s.a.ENCODE[s.a.map_normal(t)] for t in word))
for trial in range(12000):
 if trial<40:order=list(range(8));roles=[0]*8;roles[trial//5%8]=trial%5+1;uswap=False
 elif rng.random()<.85:
  order,roles,uswap=list(champ[0]),list(champ[1]),champ[2]
  z=rng.random()
  if z<.35:x,y=rng.sample(range(8),2);order[x],order[y]=order[y],order[x]
  elif z<.9:roles[rng.randrange(8)]=rng.randrange(6)
  else:uswap=not uswap
 else:order=rng.sample(range(8),8);roles=[rng.randrange(6) for _ in range(8)];uswap=bool(rng.randrange(2))
 rows=[s.role_rows[i][roles[i]] for i in range(8)]
 if uswap:rows[0]=luk[roles[0]]
 w=s.a.PREFIX+sum((rows[i] for i in order),())+s.a.SUFFIX
 if w==original:continue
 digest=hashlib.sha256(json.dumps(w).encode()).hexdigest()
 nodes,r,m,pieces=s.compile_word(w,rng,noise=0 if trial%3 else .8)
 if m[0]<=best[0] or rng.random()<.02:champ=order,roles,uswap
 if digest not in seen and (m<best or m[0]<=204):
  seen.add(digest)
  row=dict(trial=trial,order=order,roles=roles,u_b_swap=uswap,metrics=m,root=r,nodes=nodes,ax_word=w,ax_pieces=pieces,seconds=time.monotonic()-start)
  if m<best:best=m;print('BEST',trial,m,order,roles,uswap,flush=True)
  if m[0]<=208 or len(records)<4:
   file=out/f'candidate_{trial}_{m[0]}.json';file.write_text(json.dumps(row,indent=2)+'\n');records.append(dict(file=str(file),metrics=m,order=order,roles=roles,u_b_swap=uswap))
summary=dict(trials=12000,best=best,records=records,seconds=time.monotonic()-start)
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print('DONE',best,len(records),flush=True)
