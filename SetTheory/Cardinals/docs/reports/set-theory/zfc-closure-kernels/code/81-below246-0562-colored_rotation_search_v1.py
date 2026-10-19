"""Bounded source reassociation with transported physical decoder colors.

Accepted output still needs independent universal instruction and blank audits.
"""
from pathlib import Path
import sys,json,functools,collections,time,hashlib
HERE=Path(__file__).parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'agent_logic'));sys.path.insert(0,str(HERE))
import rotation_search as r
import grammar_stats as gs
import compile_rotated as c
from compile_roles import compile_roles
raw=(c.BASE/'sources/Prog254.v').read_bytes();base=r.load(raw)
assert c.oldroot==base and c.entries==r.entries
leaves,cases,by,first=r.a.read_program(raw)
colors0={s:next(iter(c.sigq[s])) for s in c.oldsigs};assert all(len(c.sigq[s])==1 for s in c.oldsigs)
F={tuple(e['row']) for e in json.load(open(HERE/'original_terminal_dependencies.json'))['rows']}
shared={q for q,ss in c.qsig.items() if len(ss)>1}
seen=set();records=[];counters=collections.Counter();began=time.monotonic()

def colored_rotate(root,colors,pivot,direction,swap):
 p=r.entries[pivot];inner=p[2 if direction=='left' else 1]
 if r.entries[inner][0]!='N':return
 if colors[pivot] in shared or colors[inner] in shared:return
 qp,qi=colors[pivot],colors[inner]
 if qp==qi:return
 x=r.entries[inner]
 if direction=='left':newinner=r.mk(('N',p[1],x[1]));replacement=r.mk(('N',newinner,x[2]))
 else:newinner=r.mk(('N',x[2],p[2]));replacement=r.mk(('N',x[1],newinner))
 newcolors={};memo={};bad=False
 def add(s,q):
  nonlocal bad
  if s in newcolors and newcolors[s]!=q:bad=True
  newcolors[s]=q
 def rec(s):
  if s in memo:return memo[s]
  e=r.entries[s]
  if e[0]!='N':return s
  if s==pivot:
   add(newinner,qp if swap else qi);add(replacement,qi if swap else qp)
   # Register colors in the reused descendant subtrees as well.
   for d in [p[1],x[1],x[2]] if direction=='left' else [x[1],x[2],p[2]]:
    keep(d)
   ans=replacement
  else:
   ans=r.mk(('N',rec(e[1]),rec(e[2])));add(ans,colors[s])
  memo[s]=ans;return ans
 def keep(s):
  e=r.entries[s]
  if e[0]=='N':
   add(s,colors[s]);keep(e[1]);keep(e[2])
 result=rec(root)
 reachable=set(r.reachable(result))
 newcolors={s:q for s,q in newcolors.items() if s in reachable}
 if bad or len(reachable)!=203 or set(newcolors)!=reachable or set(newcolors.values())!=set(colors.values()):return
 # Rows not belonging to source decoders retain their support roles.
 E={str(s):r.entries[s] for s in reachable}
 for s in list(reachable):
  for d in r.entries[s][1:]:E[str(d)]=r.entries[d]
 graph={'root':result,'entries':E}
 try:T,conflicts=compile_roles(graph,newcolors)
 except (IndexError,KeyError):return
 # Uniform CI6 terminator when a previously absent leaf parent is compiled.
 for s,q in newcolors.items():
  for b in (0,1):
   if r.entries[r.entries[s][b+1]]==('CI',6) and (q,b) not in F:
    T[q,b]=(b,'R',39)
 if any(T[row]!=c.T[row] for row in F):return
 return result,newcolors,T,graph

def metric(root):
 stat=gs.stats(root);hist=stat[5]
 return (sum(hist[7:]),)+tuple(hist[j] if j<len(hist) else 0 for j in range(6,-1,-1))+(stat[3],)

def neighbors(state,allow_worse=False):
 root,colors,T,graph=state;old=metric(root);out=[]
 for pivot in r.reachable(root):
  for direction in ('left','right'):
   for swap in (False,True):
    counters['recipes']+=1
    candidate=colored_rotate(root,colors,pivot,direction,swap)
    if candidate is None:continue
    nr,nc,nt,ng=candidate;score=metric(nr);stat=gs.stats(nr)
    key=(nr,tuple(sorted(nc.items())))
    if key in seen:continue
    seen.add(key);counters['colored_admitted']+=1
    if stat[4]>7 or stat[3]>46 or (not allow_worse and score>old):continue
    counters['semantic_checks']+=1
    check=r.check(nr,leaves,cases,set())
    if check is None:continue
    counters['source_exact']+=1
    out.append((score,(pivot,direction,swap),candidate))
 out.sort(key=lambda x:x[0]);return out

def save(state,step,move):
 root,colors,T,graph=state;stat=gs.stats(root);meta={'unique_pairs':203,'maximum_depth':stat[3],'maximum_zero_run':stat[4],'cd_trailing_zero_histogram':stat[5],'exact_all_guard_successors':True,'register_arguments_preserved':True,'frozen_borrowed_rows':len(F),'working_states':len({q for q,b in T}),'step':step,'move':move,'status':'compiled candidate; not yet audited'}
 graph=dict(graph,metadata=meta)
 p=HERE/f'colored_candidate_{step:03}.json';p.write_text(json.dumps(graph,separators=(',',':'))+'\n');c.save_table(T,HERE/f'colored_candidate_{step:03}.tm');(HERE/f'colored_candidate_{step:03}_roles.json').write_text(json.dumps({'roles':colors},separators=(',',':'))+'\n')
 print('SAVED',step,metric(root),'move',move,'counts',dict(counters),'seconds',time.monotonic()-began,flush=True)
 records.append(meta)

E={str(s):r.entries[s] for s in set(range(len(r.entries)))}
state=(base,colors0,c.T.copy(),{'root':base,'entries':E});save(state,0,None)
for step in range(1,45):
 ns=neighbors(state)
 if ns:
  best=ns[0]
  if best[0]<metric(state[0]):state=best[2];save(state,step,best[1])
  else:
   # Try at most twelve equal-score neighboring colorings for a second move.
   chain=[]
   for _,move,one in ns[:12]:
    for sc,mv,two in neighbors(one):
     if sc<metric(state[0]):chain.append((sc,[move,mv],two));break
   if not chain:print('STOP plateau',step,dict(counters),flush=True);break
   chain.sort(key=lambda x:x[0]);best=chain[0];state=best[2];save(state,step,best[1])
 else:
  print('STOP no neighbor',step,dict(counters),flush=True);break
 if metric(state[0])[0]==0:break
(HERE/'colored_search_summary.json').write_text(json.dumps({'seconds':time.monotonic()-began,'counts':dict(counters),'records':records,'stopping_bad_cd_tails':metric(state[0])[0]},indent=2)+'\n')
