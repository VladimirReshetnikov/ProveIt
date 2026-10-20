"""Delete a state by independently rewriting every incoming row.
Finite local proof search only: each positive old/new run must rejoin with the
same retained state, head, and window tape before either reads outside window.
Runs are cut at another rewritten entry row, making individual certificates
composable. The invariant is the sound blank-start overapproximation.
"""
from search_folds import *
radius=int(sys.argv[1]) if len(sys.argv)>1 else 7
I={int(q):v for q,v in json.loads((out/f'invariant219_r{radius}.json').read_text()).items()};N=2*radius+1
found=[];tested=0;beg=time.monotonic()
for drop in Q:
 if drop==0:continue
 incoming=[k for k,v in T.items()if v[2]==drop and k[0]!=drop]
 forbidden=set(incoming);choices={};proofsizes={}
 for source,bit in incoming:
  cases=[]
  for x in I[source]:
   if(x>>radius&1)!=bit:continue
   t=x;h=radius;q=source;goals={};seen=set()
   for k in range(1,41):
    w,d,q=T[q,t>>h&1];t=(t&~(1<<h))|(w<<h);h+=d
    if q!=drop:goals.setdefault((q,h,t),k)
    if not 0<=h<N or q==254 or(q,h,t)in seen:break
    seen.add((q,h,t))
   cases.append((x,goals))
  options=[]
  for action in itertools.product((0,1),(-1,1),[z for z in Q if z!=drop]+[254]):
   tested+=1;lengths=[]
   for x,goals in cases:
    t=x;h=radius;q=source;seen=set();matched=False
    for k in range(1,41):
     w,d,q=action if k==1 else T[q,t>>h&1]
     t=(t&~(1<<h))|(w<<h);h+=d;sig=q,h,t
     if sig in goals:lengths.append((goals[sig],k));matched=True;break
     if not 0<=h<N or q in(drop,254) or(q,t>>h&1)in forbidden or sig in seen:break
     seen.add(sig)
    if not matched:break
   if len(lengths)==len(cases):options.append({'action':action,'lengths':[[k[0],k[1],n]for k,n in collections.Counter(lengths).items()]})
  if not options:break
  choices[f'{source}/{bit}']=options
 if len(choices)==len(incoming):
  item={'drop':drop,'radius':radius,'choices':choices};found.append(item);print('FOUND',json.dumps(item),flush=True)
 if Q.index(drop)%50==0:print('PROGRESS',drop,tested,round(time.monotonic()-beg,3),flush=True)
r={'tested':tested,'radius':radius,'fuel':40,'found':found,'seconds':time.monotonic()-beg};(out/f'bypass219_r{radius}.json').write_text(json.dumps(r,indent=2));print('DONE',json.dumps(r),flush=True)
