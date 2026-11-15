#!/usr/bin/env python3
"""Source-frame window envelopes, including arithmetic and list interiors.

This is an executable symbolic envelope, not a kernel theorem.  It uses the
independent literal row verifier's checked unary and one-block list identities.
Different affine parameters and list prefix/suffix lengths are deliberately
decoupled, making the finite windows an overapproximation.
"""
from pathlib import Path
import argparse, collections, functools, hashlib, itertools, json, sys, time, resource

ap=argparse.ArgumentParser()
ap.add_argument('machine',type=Path)
ap.add_argument('reference',type=Path)
ap.add_argument('output',type=Path)
ap.add_argument('--radius',type=int,default=6)
ap.add_argument('--marginals',type=Path,required=True)
args=ap.parse_args()
sys.path.insert(0,str(args.reference))
import symbolic_runtime as sym
import independent_runtime as runtime
sym.HEADER_BASE=48
K=args.radius
rows={}
for line in (args.machine/'machine.native.tm').read_text().splitlines():
 q,b,w,d,t=line.split();rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
states={q for q,b in rows}
mapping={int(k):v for k,v in json.loads((args.reference/'legacy_mapping.json').read_text()).items()}
for q in states|{254}:mapping.setdefault(q,q+10000)
inverse={v:k for k,v in mapping.items() if k in states|{254}}
assert len(inverse)==len(states)+1
table={(mapping[q],b):(w,d,mapping[t]) for(q,b),(w,d,t) in rows.items()}
runtime.PHY=(6,2,0,4,3,7,8,5,1)
lemmas,blocks=sym.prove_blocks(table)
patterns=collections.defaultdict(set)
observed=set();scan_keys=set();list_keys=set()
counts=collections.Counter()

def compress(atoms):
 out=[]
 for a in atoms:
  if a[0]=='run':
   _,b,n=a
   assert all(x>=0 for x in n)
   if not any(n):continue
   out.append(('r',b,min(n[0],2*K+1),int(any(n[1:]))))
  elif a[0]=='list':out.append(('l',a[1],a[3]))
  elif a==sym.BLANK:out.append(('z',))
  else:out.append(('a',))
 return tuple(out)

def prefix(atoms,k):
 # Discard unreachable suffix descriptors before memoization.  A long source
 # path must not remain in a cache key for a six-square observation.
 acc=[];minimum=0
 for a in atoms:
  acc.append(a)
  if a[0] in ('z','a'):break
  if a[0]=='r':minimum+=a[2]
  if minimum>=k:break
 return prefix_cached(tuple(acc),k)

@functools.lru_cache(maxsize=10000)
def prefix_cached(atoms,k):
 if k==0:return (0,)
 if not atoms:return (0,)
 a,*rest=atoms;rest=tuple(rest)
 if a[0]=='z':return (0,)
 if a[0]=='a':return tuple(range(1<<k))
 if a[0]=='r':
  _,b,c,v=a
  lengths=range(c,k+1) if v and c<k else (min(c,k),)
  out=set()
  for n in lengths:
   if n>=k:out.add((1<<k)-1 if b else 0)
   else:
    for suffix in prefix(rest,k-n):out.add(((1<<n)-1 if b else 0)|(suffix<<n))
  return tuple(sorted(out))
 assert a[0]=='l',a
 # An arbitrary finite list is empty or one block followed by another list.
 f,rev=a[1:]
 block=(('r',0,1,0),('r',1,1,1)) if f=='B' else (('r',1,1,0),('r',0,1,0),('r',1,0,1))
 if rev:block=tuple(reversed(block))
 return tuple(sorted(set(prefix(rest,k))|set(prefix(block+(a,)+rest,k))))

@functools.lru_cache(None)
def reverse(x,k):
 return sum(((x>>i)&1)<<(k-1-i) for i in range(k))

def windows(q,d,l,r):
 lp=prefix(l,K+(d==-1));rp=prefix(r,K+(d==1))
 key=(q,d,lp,rp)
 if key in observed:return
 observed.add(key)
 if d==1:patterns[inverse[q]].update(reverse(a,K)|(b<<K) for a,b in itertools.product(lp,rp))
 else:patterns[inverse[q]].update(reverse(a,K+1)|(b<<(K+1)) for a,b in itertools.product(lp,rp))

def observe(s,lists=True):
 q,d,left,right=s.key()
 l=compress(left);r=compress(right)
 windows(q,d,l,r)
 src=l if d==-1 else r
 if not src:return
 a=src[0]
 if a[0]=='r':
  _,b,c,v=a
  w,dr,nq=table[q,b]
  if (dr,nq)!=(d,q):return
  key=q,d,l,r
  if key in scan_keys:return
  scan_keys.add(key);counts['unary_sweeps']+=1
  lengths=range(c,2*K+2) if v and c<2*K+1 else (c,)
  for length in lengths:
   for used in range(length):
    rem=length-used
    if d==1:
     windows(q,d,(('r',w,used,0),)+l,(('r',b,rem,0),)+r[1:])
    else:
     windows(q,d,(('r',b,rem,0),)+l[1:],(('r',w,used,0),)+r)
 elif a[0]=='l' and lists:
  key=q,d,l,r
  if key in list_keys:return
  list_keys.add(key);counts['list_sweeps']+=1
  atom=(left if d==-1 else right)[0]
  before=atom[1];after=lemmas[q,d,before,atom[3]]
  block_before=sym.block(sym.var(2),before)
  block_after=sym.block(sym.var(2),after)
  tail=(left if d==-1 else right)[1:]
  dst=right if d==-1 else left
  # A selected internal block has arbitrary already processed and remaining
  # finite lists.  Their lengths are independent, which is conservative.
  pre=('list',after,'generic_prefix',d==1)
  post=('list',before,'generic_suffix',d==-1)
  if d==1:
   cur=sym.State(q,[pre]+dst,block_before+[post]+tail,1)
   target=sym.State(q,sym.rev(block_after)+[pre]+dst,[post]+tail,1)
  else:
   cur=sym.State(q,sym.rev(block_before)+[post]+tail,[pre]+dst,-1)
   target=sym.State(q,[post]+tail,block_after+[pre]+dst,-1)
  goal=target.key();clock=motion=sym.ZERO
  for i in range(60):
   if i and cur.key()==goal:break
   observe(cur,False)
   clock,motion,event=original_step(cur,table,{},clock,motion)
  else:raise AssertionError(('Generic list block did not close',key))
  assert clock==sym.add(sym.var(2),sym.num(2))

original_step=sym.State.step
def hooked(self,tab,lems,clock,motion):
 observe(self)
 return original_step(self,tab,lems,clock,motion)
sym.State.step=hooked
mapped=[]
names={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
for p,op,a in json.loads((args.machine/'sites.json').read_text()):
 if not isinstance(p,str):p=''.join(map(str,p))
 mapped.append([p,names[op],a])
abstract_data=json.loads(args.marginals.read_text())
marginals=abstract_data['register_values']
abstract_radix=abstract_data['radix']
assert abstract_radix in (3,4)
assert len(marginals)==len(mapped)
def abstract_value(mask,slot):
 assert mask
 minimum=(mask&-mask).bit_length()-1
 if mask==(1<<minimum) and minimum<abstract_radix-1:return sym.num(minimum)
 return sym.add(sym.num(minimum),sym.var(slot))
started=time.time();outcomes=total=maximum=0
removed=0
for i,site in enumerate(mapped):
 if not any(marginals[i]):
  removed+=2 if site[1]=='CD' else 1
  continue
 for positive in ([False,True] if site[1]=='CD' else [False]):
  allowed=list(marginals[i])
  if site[1]=='CD':
   allowed[site[2]] &= (1<<abstract_radix)-2 if positive else 1
   if not allowed[site[2]]:
    removed+=1
    continue
  values=[abstract_value(v,2+r)for r,v in enumerate(allowed)]
  ans=sym.case(table,lemmas,site,positive,values_override=values)
  outcomes+=1;total+=ans['symbolic_steps'];maximum=max(maximum,ans['symbolic_steps'])
  observed.clear();scan_keys.clear();list_keys.clear()
 if (i+1)%100==0:
  print('sites',i+1,'outcomes',outcomes,'windows',sum(map(len,patterns.values())), 'seconds',round(time.time()-started,2),'maxrss_kb',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,flush=True)

# The full finite blank startup is separately included.  The target is the
# exact initialized primary register file at source site 25.
head=-2
expected={head-1,head+48}
expected.update(head+i for i,b in enumerate(mapped[25][0]) if b=='1')
pos=head+49
for v in [0,0,0,0,0,0,2,0,0]+[1]*26:
 pos+=1;expected.update(range(pos,pos+v+1));pos+=v+1
q,head,ones=74,0,set()
for startup in range(300001):
 if (q,head,ones)==(84,-2,expected):break
 assert q!=254,('startup halt',startup)
 p=sum(int(head+x in ones)<<(x+K) for x in range(-K,K+1))
 patterns[q].add(p)
 w,d,q=rows[q,int(head in ones)]
 (ones.add if w else ones.discard)(head);head+=d
else:raise AssertionError('No whole-tape startup')
assert set(patterns)==states,(states-set(patterns))
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(''.join(f'{q} {p}\n' for q in sorted(patterns) for p in sorted(patterns[q])))
receipt={'radius':K,'abstract_radix':abstract_radix,'controls':len(patterns),'windows':sum(map(len,patterns.values())),
 'sites':len(mapped),'source_outcomes':outcomes,'abstractly_impossible_outcomes_removed':removed,'marginals_sha256':hashlib.sha256(args.marginals.read_bytes()).hexdigest(),'symbolic_steps':total,'max_symbolic_steps':maximum,
 'startup_steps':startup,'counts':dict(counts),'windows_per_control':{q:len(p) for q,p in patterns.items()},
 'native_sha256':hashlib.sha256((args.machine/'machine.native.tm').read_bytes()).hexdigest(),
 'elapsed_seconds':time.time()-started,'literal_list_lemmas':blocks,
 'scope':'Finite abstract invariant restricted affine source traces, accelerated unary interiors, arbitrary finite-list interiors, exact blank startup. Parameters are overapproximated independently. Executable certificate; not a new proof-assistant theorem.'}
args.output.with_suffix('.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ('literal_list_lemmas','windows_per_control')},indent=2),flush=True)
