from search_folds import *
radius=int(sys.argv[1]) if len(sys.argv)>1 else 5
I={int(q):v for q,v in json.loads((out/f'invariant219_r{radius}.json').read_text()).items()};N=2*radius+1
ENGINE=[0,1,2,3,4,5,6,9,10,14,15,16,17,21,22,23,24,25,32,33,34,35,36,39,40,41,45,48,49,50,51,54,55,56,60,61,64,66,74,75,82,94,97,113,137,144,156,161,198,302]
found=[];start=time.monotonic();tested=0;eligible=0
for a,b in itertools.combinations(Q,2):
 if not({a,b}&set(ENGINE)):continue
 # Identical input tapes cannot be separated unless old futures merge; permit overlap.
 eligible+=1;phi=lambda z:a if z==b else z
 new={(q,v):(w,d,phi(z)) for (q,v),(w,d,z) in T.items() if q!=b}
 cases=[[],[]]
 for oq in(a,b):
  for x in I[oq]:
   t=x;h=radius;q=oq;goals={};seen=set()
   for k in range(1,41):
    w,d,q=T[q,t>>h&1];t=(t&~(1<<h))|(w<<h);h+=d
    goals.setdefault((phi(q),h,t),k)
    if not 0<=h<N or q==254 or(q,h,t)in seen:break
    seen.add((q,h,t))
   cases[x>>radius&1].append((x,goals))
 options=[]
 for c in(0,1):
  good=[]
  for action in itertools.product((0,1),(-1,1),[x for x in Q if x!=b]+[254]):
   tested+=1;proof=[]
   for x,goals in cases[c]:
    t=x;h=radius;q=a;seen=set();matched=False
    for k in range(1,41):
     w,d,q=action if k==1 else new[q,t>>h&1]
     t=(t&~(1<<h))|(w<<h);h+=d;sig=q,h,t
     if sig in goals:proof.append((goals[sig],k));matched=True;break
     if not 0<=h<N or q in(254,a) or sig in seen:break
     seen.add(sig)
    if not matched:break
   if len(proof)==len(cases[c]):good.append({'row':action,'lengths':[[k[0],k[1],v]for k,v in collections.Counter(proof).items()]})
  if not good:break
  options.append(good)
 if len(options)==2:
  item={'keep':a,'drop':b,'options':options,'radius':radius};found.append(item);print('FOUND',json.dumps(item),flush=True)
 if eligible%500==0:print('progress',eligible,tested,round(time.monotonic()-start,1),flush=True)
(out/f'double219_r{radius}.json').write_text(json.dumps({'tested':tested,'found':found,'seconds':time.monotonic()-start},indent=2));print('DONE',len(found),tested,time.monotonic()-start)
