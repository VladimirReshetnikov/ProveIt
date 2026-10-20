from invariant_search import *
radius=int(sys.argv[1])if len(sys.argv)>1 else 3
I={int(q):xs for q,xs in json.loads(Path(f'invariant_r{radius}.json').read_text()).items()}
N=2*radius+1;mask=(1<<N)-1
# Checks full tape agreement: no cells outside represented interval are read or written.
def check(new,a,b,c,action):
 phi=lambda q:a if q==b else q
 proof=[]
 for q in(a,b):
  w,d,z=T[q,c];z=phi(z)
  for x in I[q]:
   if (x>>radius&1)!=c:continue
   goal=(x&~(1<<radius))|(w<<radius)
   tape=x;h=radius;state=a;seen=set()
   for k in range(1,22):
    cell=tape>>h&1
    ww,dd,zz=action if state==a and cell==c else new[state,cell]
    tape=(tape&~(1<<h))|(ww<<h);h+=dd;state=zz
    if state==z and h==radius+d and tape==goal:proof.append(k);break
    if not (0<=h<N) or state==254:return False
    sig=(state,h,tape)
    if sig in seen:return False
    seen.add(sig)
   else:return False
 return proof
found=[];start=time.monotonic();tested=0
for a,b in itertools.combinations(Q,2):
 if not ({a,b}&ENGINE):continue
 phi=lambda z:a if z==b else z
 same=[c for c in(0,1)if (*T[a,c][:2],phi(T[a,c][2]))==(*T[b,c][:2],phi(T[b,c][2]))]
 if len(same)!=1:continue
 c=1-same[0]
 new={(q,v):(w,d,phi(z))for(q,v),(w,d,z)in T.items()if q!=b}
 for w,d,z in itertools.product((0,1),(-1,1),[x for x in Q if x!=b]+[254]):
  tested+=1;action=(w,d,z)
  proof=check(new,a,b,c,action)
  if proof:
   item={'keep':a,'drop':b,'read':c,'row':action,'lengths':dict(collections.Counter(proof)),'radius':radius}
   found.append(item);print('FOUND',json.dumps(item),flush=True)
 print('pair',a,b,'seconds',round(time.monotonic()-start,2),flush=True)if tested%25000<884 else None
Path(f'engine_folds_r{radius}.json').write_text(json.dumps({'tested':tested,'found':found,'seconds':time.monotonic()-start},indent=2))
print('DONE',len(found),tested,time.monotonic()-start)
