import json,pathlib,itertools,time,functools
import os
HERE=pathlib.Path(__file__).resolve().parent
BASE=pathlib.Path(os.environ.get('ZFC245_BASE',str(HERE.parent/'baseline245/zfc245-proof-20261018')))
OUT=HERE
gram=json.loads((BASE/'results/state_reduction/candidate-zero6-k128.json').read_text())
g={q:(a,b) for q,a,b in gram['rules']}
lines=(BASE/'inputs/state_reduction/route-grammar.txt').read_text().splitlines();nr,nrt,na=map(int,lines[0].split());roots=lines[nr+1:nr+nrt+1];allowed={c:int(v) for c,v in map(str.split,lines[nr+nrt+1:])}
ls=iter((BASE/'inputs/state_reduction/route-constraints.txt').read_text().splitlines());ng=int(next(ls));groups=[]
for _ in range(ng):
 source,read,word,n=next(ls).split();cs=[tuple(next(ls).split()) for j in range(int(n))];groups.append((int(source),int(read),cs))
routes={ (v['source'],v['read']):v['word'] for v in gram['routes']}
def allowed_side(w,b):return len(w)>1 or allowed[w]&(1<<b)
@functools.lru_cache(None)
def force(q,cs):
 if not cs:return ((),) if len(q)==1 or q in g else ()
 splits=set(range(1,len(q)));bc=[[],[]];has=False
 for prefix,target in cs:
  if not prefix:
   if target!=q:return ()
  else:
   has=True;bc[int(prefix[0])].append((prefix[1:],target))
   if set(prefix)=={'0'} and not q.startswith(target):return ()
   if set(prefix)=={'1'} and not q.endswith(target):return ()
   if len(prefix)==1:splits&={len(target) if prefix=='0' else len(q)-len(target)}
 if not has:return ((),) if len(q)==1 or q in g else ()
 ret=[]
 for k in sorted(splits):
  a,b=q[:k],q[k:]
  if not a or not b or not allowed_side(a,0) or not allowed_side(b,1):continue
  for pa in force(a,tuple(bc[0])):
   for pb in force(b,tuple(bc[1])):ret.append(pa+pb+((q,a,b),))
 return tuple(ret)
def match(d,w,cs):
 for bits,t in cs:
  x=w
  for b in bits:
   if x not in d:return False
   x=d[x][int(b)]
  if x!=t:return False
 return True
def close(d,rs):
 live=set();todo=list(roots)+list(rs.values())
 while todo:
  q=todo.pop()
  if len(q)==1 or q in live:continue
  if q not in d:return None
  live.add(q);todo.extend(d[q])
 return {q:d[q] for q in live}
choices={}
for key in [(153,1),(159,0)]:
 cs=next(cs for s,b,cs in groups if (s,b)==key)
 choices[key]=[(q,plan) for q in g for plan in force(q,tuple(cs))]
 print('CHOICES',key,len(choices[key]),flush=True)
count=0;best=128;started=time.monotonic();hist={}
for (a,pa),(b,pb) in itertools.product(choices[(153,1)],choices[(159,0)]):
 count+=1;d=g.copy();rs=routes.copy()
 for q,l,r in pa+pb:d[q]=(l,r)
 rs[153,1]=a;rs[159,0]=b
 good=True
 for source,read,cs in groups:
  if match(d,rs[source,read],cs):continue
  opts=[q for q in d if match(d,q,cs)]
  if not opts:good=False;break
  rs[source,read]=min(opts,key=lambda w:(len(w),w))
 if not good:continue
 d=close(d,rs)
 if d is None:continue
 n=len(d);hist[n]=hist.get(n,0)+1
 if n<best:
  best=n;out=dict(gram);out.update(rules_count=n,roots=roots,rules=[[q,*d[q]] for q in sorted(d)],routes=[dict(source=s,read=b,word=w) for(s,b),w in sorted(rs.items())],seed='exhaust_context',iterations=count,seconds=time.monotonic()-started)
  (OUT/f'exhaust-context-k{n}.json').write_text(json.dumps(out,indent=2)+'\n');print('BEST',n,count,flush=True)
res=dict(status='FINITE_SCREEN_ONLY',candidates=count,best_rules=best,histogram=hist,seconds=time.monotonic()-started,scope='Both eliminated177 callers rerouted to existing current128 grammar words using all top-level split plans whose unconstrained descendants are already active; no zero-run or full-machine theorem is inferred.')
(OUT/'exhaust-context-summary.json').write_text(json.dumps(res,indent=2)+'\n');print(res)
