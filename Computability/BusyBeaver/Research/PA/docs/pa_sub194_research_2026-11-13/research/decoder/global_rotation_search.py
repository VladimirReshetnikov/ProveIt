"""Explore fixed pure-reader rotations; filter exact source CFG identities.
Only symbolic-validated candidates are accepted as implementations.
"""
import sys,pathlib,json,collections,itertools,time,hashlib,heapq,copy,resource,gc
resource.setrlimit(resource.RLIMIT_AS,(350*1024**2,350*1024**2))
PK=pathlib.Path(__file__).resolve().parents[2]/'reference/haz'
sys.path.insert(0,str(PK/'vendor'));import compiler as c,symbolic_runtime as s
inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
NODES=c.raw_nodes();G=c.read_grammar(PK/'inputs/pa194.grammar.json');raw,idx,shape=c.build(G)
old,_=c.machine();hint={};todo=[('node172',84)]
while todo:
 n,q=todo.pop()
 if not isinstance(n,str) or n in hint:continue
 hint[n]=q
 for b,ch in enumerate(NODES[n]):
  w,d,t=old[q,b]
  if w==b and d:todo.append((ch,t))
BASE_S,BASE_I,BASE_C=c.source(G)
print('BASE_READY',len(raw)//2,flush=True)

def source(ns):
 sites=[];prefix={}
 def walk(t,p):
  prefix[p]=len(sites)
  if isinstance(t,str):return walk(G if t=='x67' else ns[t],p)
  if t[0]=='leaf':sites.append((p,t[1],t[2]));return
  walk(t[0],p+(0,));walk(t[1],p+(1,))
 walk('node172',())
 def loc(p):
  if p in prefix:return prefix[p]
  while p and not p[-1]:
   p=p[:-1]
   if p in prefix:return prefix[p]
  raise ValueError(p)
 def after(p):
  for i in range(len(p)-1,-1,-1):
   if p[i]==0:return loc(p[:i]+(1,))
  raise ValueError(p)
 def cut(p,b,k):
  for i in range(len(p)-1,-1,-1):
   if p[i]==b:
    k-=1
    if k==0:return p[:i]
  raise ValueError(p)
 ins=[]
 for p,op,r in sites:
  if op=='inc':ins.append(('inc',r,after(p)))
  elif op=='dec':ins.append(('dec',r,after(cut(p,0,1)),after(p)))
  elif op=='breakTo':ins.append(('jump',after(cut(p,0,r))))
  elif op=='continueTo':ins.append(('jump',loc(cut(p,1,r))))
  else:ins.append(('halt',))
 walk=None
 return sites,ins
assert source(NODES)==(BASE_S,BASE_I)
print('SOURCE_READY',flush=True)

def reach(rows):
 live={74};todo=[74]
 for q in todo:
  for b in (0,1):
   t=rows[q,b][2]
   if t!=254 and t not in live:live.add(t);todo.append(t)
 return {(q,b):a for (q,b),a in rows.items() if q in live}

def pure(rows):return {q:(rows[q,0][2],rows[q,1][2]) for q,b in rows if b==0 and rows[q,0][:2]==(0,True) and rows[q,1][:2]==(1,True)}
def fold(rows,fs):
 al={a:b for a,b,acts in fs};ac={b:acts for a,b,acts in fs}
 return {(q,b):(v[0],bool(v[1]),al.get(v[2],v[2])) for(q,b),old in rows.items() if q not in al for v in [ac[q][b] if q in ac else old]}
def score(rows):
 cand={q:None for q,b in rows if b==0 and q not in c.BOXSTATES|{74,84}}
 ops=c.opportunities_fast(rows,cand);pairs=c.max_matching(ops);dic={(a,b):o for a,b,o in ops}
 fs=[[a,b,[opts[0] for opts in dic[a,b]]]for a,b in pairs]
 return len(rows)//2-len(fs),fs

def key(rows):
 # rooted canonical list, with halt assigned -1
 ids={74:0,254:-1};order=[74];out=[]
 for q in order:
  pair=[]
  for b in (0,1):
   w,d,t=rows[q,b]
   if t not in ids:ids[t]=len(order);order.append(t)
   pair.append((w,d,ids[t]))
  out.append(pair)
 return hashlib.sha256(json.dumps(out,separators=(',',':')).encode()).hexdigest()

def contracts(sites,ins):
 cs=[]
 for i,code in enumerate(ins):
  st=c.frame(sites[i][0]);op=code[0]
  if op=='inc':
   _,r,n=code;cs.append((i,None,st,c.canonical(c.frame(sites[n][0],0,('x','inc',c.PHYSICAL[r])))))
  elif op=='dec':
   _,r,z,p=code;cs.append((i,(c.PHYSICAL[r],True),st,c.canonical(c.frame(sites[z][0]))));cs.append((i,(c.PHYSICAL[r],False),st,c.canonical(c.frame(sites[p][0],1,('x','dec',c.PHYSICAL[r])))))
  elif op=='jump':cs.append((i,None,st,c.canonical(c.frame(sites[code[1]][0]))))
  else:cs.append((i,None,st,None))
 return cs

limit=int(sys.argv[1])if len(sys.argv)>1 else 100
initial=score(raw);print('INITIAL_SCORE',initial[0],flush=True);Q=[(initial[0],0,0,NODES,hint,raw,[])];seen={key(raw)};counter=0;expanded=0;hist=collections.Counter();st=time.time();results=[]
while Q and expanded<limit:
 _,dep,_,ns,hn,rows,path=heapq.heappop(Q);expanded+=1;gc.collect()
 ps=pure(rows);providers=collections.defaultdict(list);qns=collections.defaultdict(list)
 for q,p in ps.items():providers[p].append(q)
 for n,q in hn.items():qns[q].append(n)
 for n,q in sorted(hn.items()):
  if q not in ps or len(qns[q])!=1 or n.startswith('x'):continue
  for side in (0,1):
   child=ns[n][side]
   if not isinstance(child,str)or child not in hn:continue
   cq=hn[child]
   if cq not in ps or len(qns[cq])!=1 or ps[q][side]!=cq:continue
   newq=max([3999,*[q for q,b in rows]])+1
   if side==0:
    a,b=ns[child];d=ns[n][1];pair=(ps[cq][1],ps[q][1]);outside=ps[cq][0]
   else:
    a=ns[n][0];b,d=ns[child];pair=(ps[q][0],ps[cq][0]);outside=ps[cq][1]
   # Reusing a physical reader is safe only after full symbolic validation.
   for pq in (providers.get(pair,[])or[newq]):
    if pq in(q,cq):continue
    rr=dict(rows);rr[q,0]=(0,True,outside if side==0 else pq);rr[q,1]=(1,True,pq if side==0 else outside)
    if pq==newq:rr[pq,0]=(0,True,pair[0]);rr[pq,1]=(1,True,pair[1])
    rr=reach(rr);ky=key(rr)
    if ky in seen:continue
    seen.add(ky);sc,fs=score(rr);hist[sc]+=1
    if sc>194 or dep>=5:continue
    nn=dict(ns);hh=dict(hn);newname='new'+str(newq)
    if newname in nn:continue
    nn[newname]=(b,d)if side==0 else(a,b);hh[newname]=pq
    nn[n]=(a,newname)if side==0 else(newname,d)
    try:sites,ins=source(nn)
    except (ValueError,KeyError):continue
    if ins!=BASE_I or max(len(p)for p,_,_ in sites)>48:continue
    route=path+[(n,side,pq,sc)];counter+=1
    # Cheap check physically unaffected contracts first, then full on promising 193.
    if sc<194:
     childrows=fold(rr,fs);valid=c.validate(childrows,contracts(sites,ins));print('HIT',route,valid,flush=True)
     rec={'path':route,'score':sc,'raw':len(rr)//2,'folds':fs,'validation':valid}
     results.append(rec)
     if valid['ok']:
      pref=pathlib.Path(__file__).parent/f'global_success_{sc}_{counter}'
      pref.with_suffix('.tm').write_text(''.join(f'{q} {b} {w} {"R"if d else"L"} {t}\n'for(q,b),(w,d,t)in sorted(childrows.items())))
      pref.with_suffix('.json').write_text(json.dumps({'result':rec,'sites':sites,'instructions':ins,'nodes':nn,'raw':[(q,b,*a)for(q,b),a in sorted(rr.items())]},indent=2));print('SUCCESS',pref,flush=True)
      raise SystemExit(0)
    heapq.heappush(Q,(sc,dep+1,counter,nn,hh,rr,route))
    if len(Q)>60: Q=heapq.nsmallest(50,Q);heapq.heapify(Q)
 print('PROGRESS',expanded,'queue',len(Q),'seen',len(seen),'hist',dict(hist),'sec',round(time.time()-st,2),flush=True)
pathlib.Path(__file__).with_suffix('.json').write_text(json.dumps({'expanded':expanded,'queue':len(Q),'seen':len(seen),'histogram':hist,'results':results,'elapsed':time.time()-st},indent=2))
