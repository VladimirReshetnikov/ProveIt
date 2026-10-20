from search_folds import *
radius=int(sys.argv[1]) if len(sys.argv)>1 else 5
I={int(q):v for q,v in json.loads((out/f'invariant219_r{radius}.json').read_text()).items()};N=2*radius+1
found=[];start=time.monotonic();tested=0;eligible=0
for a,b in itertools.combinations(Q,2):
 phi=lambda z:a if z==b else z
 same=[c for c in(0,1)if (*T[a,c][:2],phi(T[a,c][2]))==(*T[b,c][:2],phi(T[b,c][2]))]
 if len(same)!=1:continue
 eligible+=1;c=1-same[0]
 new={(q,v):(w,d,phi(z)) for (q,v),(w,d,z) in T.items() if q!=b}
 cases=[]
 for oq in (a,b):
  for x in I[oq]:
   if (x>>radius&1)!=c:continue
   t=x;h=radius;q=oq;goals={};seen=set()
   for k in range(1,41):
    w,d,q=T[q,t>>h&1];t=(t&~(1<<h))|(w<<h);h+=d
    goals.setdefault((phi(q),h,t),k)
    if not 0<=h<N or q==254 or (q,h,t) in seen:break
    seen.add((q,h,t))
   cases.append((x,goals))
 for action in itertools.product((0,1),(-1,1),[x for x in Q if x!=b]+[254]):
  tested+=1;proof=[];new[a,c]=action
  for x,goals in cases:
   t=x;h=radius;q=a;seen=set();matched=False
   for k in range(1,41):
    w,d,q=new[q,t>>h&1];t=(t&~(1<<h))|(w<<h);h+=d
    sig=q,h,t
    if sig in goals:proof.append((goals[sig],k));matched=True;break
    if not 0<=h<N or q==254 or sig in seen:break
    seen.add(sig)
   if not matched:break
  if len(proof)==len(cases):
   item={'keep':a,'drop':b,'read':c,'row':action,'lengths':[[k[0],k[1],v] for k,v in collections.Counter(proof).items()],'radius':radius}
   found.append(item);print('FOUND',json.dumps(item),flush=True)
 if eligible%100==0:print('progress',eligible,tested,round(time.monotonic()-start,1),flush=True)
(out/f'diamonds219_r{radius}.json').write_text(json.dumps({'tested':tested,'found':found,'seconds':time.monotonic()-start},indent=2));print('DONE',len(found),tested,time.monotonic()-start)
