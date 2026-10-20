from invariant_search import *
radius=5;I={int(q):xs for q,xs in json.loads(Path(f'invariant_r{radius}.json').read_text()).items()};N=2*radius+1
pairs=json.loads(Path('disjoint_pairs.json').read_text())
def check(new,a,b,c,action):
 proof=[]
 for q in(a,b):
  w,d,z=T[q,c];z=a if z==b else z
  for x in I[q]:
   if (x>>radius&1)!=c:continue
   goal=(x&~(1<<radius))|(w<<radius)
   tape=x;h=radius;state=a;seen=set()
   for k in range(1,22):
    cell=tape>>h&1
    if k==1:ww,dd,zz=action
    else:ww,dd,zz=new[state,cell]
    tape=(tape&~(1<<h))|(ww<<h);h+=dd;state=zz
    if state==z and h==radius+d and tape==goal:proof.append(k);break
    if not(0<=h<N) or state in(254,a):return False
    sig=(state,h,tape)
    if sig in seen:return False
    seen.add(sig)
   else:return False
 return proof
found=[];start=time.monotonic();tested=0
for ix,(a,b)in enumerate(pairs):
 phi=lambda z:a if z==b else z
 new={(q,v):(w,d,phi(z))for(q,v),(w,d,z)in T.items()if q!=b}
 actions=[]
 for c in(0,1):
  choices=[]
  for w,d,z in itertools.product((0,1),(-1,1),[x for x in Q if x!=b]+[254]):
   tested+=1;action=(w,d,z);proof=check(new,a,b,c,action)
   if proof:choices.append((action,dict(collections.Counter(proof))))
  if not choices:break
  actions.append(choices)
 if len(actions)==2:
  item={'keep':a,'drop':b,'actions':actions,'radius':radius};found.append(item);print('FOUND',json.dumps(item),flush=True)
 if ix%200==0:print('pair',ix,a,b,'seconds',round(time.monotonic()-start,2),flush=True)
Path('engine_double_folds.json').write_text(json.dumps({'tested':tested,'found':found,'seconds':time.monotonic()-start},indent=2))
print('DONE',len(found),tested,time.monotonic()-start)
