import json,sys,itertools,collections,time
from pathlib import Path
BASE=(Path(__file__).resolve().parent/'data/k219')
sys.path.insert(0,str(BASE/'portable'))
from common import parse_table
T=parse_table((BASE/'machine/k219.native.tm').read_bytes());Q=sorted({q for q,b in T});out=(Path(__file__).resolve().parent/'output')
def inv(radius):
 n=2*radius+1;mask=(1<<n)-1;I={q:set() for q in Q};I[0]={0};todo=collections.deque([(0,0)])
 while todo:
  q,x=todo.popleft();v=x>>radius&1;w,d,z=T[q,v]
  if z not in I:continue
  y=(x&~(1<<radius))|(w<<radius)
  outs=[y>>1,(y>>1)|(1<<(n-1))] if d==1 else [y<<1&mask,(y<<1&mask)|1]
  for yy in outs:
   if yy not in I[z]:I[z].add(yy);todo.append((z,yy))
 return {q:sorted(v) for q,v in I.items()}
def run(radius):
 f=out/f'invariant219_r{radius}.json'
 if f.exists():I={int(q):v for q,v in json.loads(f.read_text()).items()}
 else:I=inv(radius);f.write_text(json.dumps(I))
 N=2*radius+1
 def check(new,a,b,c,action):
  proof=[]
  for q in(a,b):
   w,d,z=T[q,c];z=a if z==b else z
   for x in I[q]:
    if (x>>radius&1)!=c:continue
    goal=(x&~(1<<radius))|(w<<radius);tape=x;h=radius;state=a;seen=set()
    for k in range(1,31):
     cell=tape>>h&1
     ww,dd,zz=action if state==a and cell==c else new[state,cell]
     tape=(tape&~(1<<h))|(ww<<h);h+=dd;state=zz
     if state==z and h==radius+d and tape==goal:proof.append(k);break
     if not(0<=h<N) or state==254:return False
     sig=(state,h,tape)
     if sig in seen:return False
     seen.add(sig)
    else:return False
  return proof
 found=[];start=time.monotonic();tested=0;eligible=0
 for a,b in itertools.combinations(Q,2):
  phi=lambda z:a if z==b else z
  same=[c for c in(0,1)if (*T[a,c][:2],phi(T[a,c][2]))==(*T[b,c][:2],phi(T[b,c][2]))]
  if len(same)!=1:continue
  eligible+=1;c=1-same[0]
  new={(q,v):(w,d,phi(z)) for (q,v),(w,d,z) in T.items() if q!=b}
  for w,d,z in itertools.product((0,1),(-1,1),[x for x in Q if x!=b]+[254]):
   tested+=1;action=(w,d,z);proof=check(new,a,b,c,action)
   if proof:
    item={'keep':a,'drop':b,'read':c,'row':action,'lengths':dict(collections.Counter(proof)),'radius':radius}
    found.append(item);print('FOUND',json.dumps(item),flush=True)
  if eligible%100==0:print('progress',eligible,tested,round(time.monotonic()-start,1),flush=True)
 (out/f'folds219_r{radius}.json').write_text(json.dumps({'tested':tested,'found':found,'seconds':time.monotonic()-start},indent=2));print('DONE',len(found),tested,time.monotonic()-start)
if __name__=='__main__':run(int(sys.argv[1]) if len(sys.argv)>1 else 5)
