#!/usr/bin/env python3
"""Source-reachable local windows with exact all-one spare-list invariants.

Each primary-register marginal comes from an audited global trit fixed point.
Disconnected finite unions are split into exact affine cases. Every spare has
value one; the tail has at least25 blocks. Generic list interiors are covered
by explicit periodic block traversals and their boundary cases. Exact blank
startup is included separately. Executable evidence, not a proof-assistant
kernel check. Only radii2 and4 are used by the packaged experiments.
"""
from pathlib import Path
from functools import lru_cache
from collections import deque,Counter
import argparse,hashlib,importlib.util,itertools,json,re,sys,time
import numpy as np
BASE=Path(__file__).resolve().parent
INP=BASE/'inputs'
sys.path.insert(0,str(INP))
import symbolic_runtime as s
s.HEADER_BASE=48

def need(x,msg):
 if not x:raise AssertionError(msg)

@lru_cache(None)
def anybits(k):return tuple(tuple((v>>i)&1 for i in range(k))for v in range(1<<k))
@lru_cache(None)
def prefixes(atoms,k):
 if k==0:return ((),)
 if not atoms:return anybits(k)
 a=atoms[0]
 if a[0]=='blank':return ((0,)*k,)
 if a[0]=='list':
  word=(0,1,1)if a[1]=='B'else(1,0,1)
  if a[3]:word=word[::-1]
  return (tuple(word[i%3]for i in range(k)),)
 if a[0]=='opaque':return anybits(k)
 need(a[0]=='run','Unknown atom')
 minimum=a[2][0];variable=any(a[2][1:]);need(minimum>=0 and all(x>=0 for x in a[2]),'negative run')
 out=set()
 for size in(range(min(minimum,k),k+1)if variable else(min(minimum,k),)):
  if size==k:out.add((a[1],)*k)
  else:out.update((a[1],)*size+t for t in prefixes(atoms[1:],k-size))
 return tuple(sorted(out))

class Collector:
 def __init__(self,mapping,radius,n):
  self.mapping=mapping;self.radius=radius;self.windows={q:set()for q in range(n)};self.steps=0;self.unary=0;self.list_calls=0;self.list_cases=set();self.list_literal_steps=0
 def collect(self,q,left,right,direction):
  if q==254:return
  q=self.mapping[q];R=self.radius
  l=prefixes(tuple(left),R if direction==1 else R+1);r=prefixes(tuple(right),R+1 if direction==1 else R)
  for ls in l:
   for rs in r:self.windows[q].add(sum(v<<i for i,v in enumerate(ls[::-1]+rs)))
 def observe(self,state,table,lemmas,clock,motion):
  state.key();self.steps+=1;self.collect(state.q,state.left,state.right,state.direction)
  src,dst=(state.right,state.left)if state.direction==1 else(state.left,state.right)
  if src[0][0]=='list':
   self.list_calls+=1;self.cover_list(state,table,lemmas,src,dst)
  elif src[0][0]=='run':
   a=src[0];w,d,q=table[state.q,a[1]]
   if q==state.q and d==state.direction:
    self.unary+=1;R=self.radius
    for n in(range(a[2][0],a[2][0]+2*(R+1)+1)if any(a[2][1:])else[a[2][0]]):
     for i in set(range(1,min(n,R+2)))|set(range(max(1,n-R-1),n)):
      first=[('run',a[1],s.num(n-i))]+src[1:];second=[('run',w,s.num(i))]+dst
      left,right=(second,first)if d==1 else(first,second)
      self.collect(state.q,left,right,d)
  return self.original(state,table,lemmas,clock,motion)
 def cover_list(self,state,table,lemmas,src,dst):
  # For all spare lengths M>=25, periodic interior windows equal those of
  # M=25. Only first/last ceil(R/3)+1 blocks can see exterior boundaries.
  R=self.radius;atom=src[0];entry=state.q;direction=state.direction
  signature=(entry,direction,atom[1],atom[3]);after=lemmas[signature]
  beforeword=(0,1,1)if atom[1]=='B'else(1,0,1)
  afterword=(0,1,1)if after=='B'else(1,0,1)
  if atom[3]:beforeword=beforeword[::-1];afterword=afterword[::-1]
  W=75;before=beforeword*25;expected=afterword*25
  for prior in prefixes(tuple(dst),R):
   for following in prefixes(tuple(src[1:]),R):
    key=(signature,prior,following)
    if key in self.list_cases:continue
    self.list_cases.add(key)
    tape={direction*i:b for i,b in enumerate(before)}
    tape.update({direction*(-1-i):b for i,b in enumerate(prior)})
    tape.update({direction*(W+i):b for i,b in enumerate(following)})
    q=entry;head=0
    for _ in range(W):
     self.windows[self.mapping[q]].add(sum(tape[head+j]<<(j+R)for j in range(-R,R+1)))
     w,d,q2=table[q,tape[head]]
     need(d==direction,'generic spare traversal changed direction')
     tape[head]=w;head+=d;q=q2;self.list_literal_steps+=1
    need(q==entry and head==direction*W,'generic spare traversal endpoint')
    need(tuple(tape[direction*i]for i in range(W))==expected,'generic spare traversal tape')

def blank(table,N,radius,projection):
 width=2*radius+1;mask=(1<<width)-1;seen={(0,0)};queue=deque(seen)
 while queue:
  q,x=queue.popleft();w,d,t=table[q,(x>>radius)&1];x=(x&~(1<<radius))|(w<<radius)
  if t==N:continue
  for b in(0,1):
   y=(x>>1)|(b<<(width-1))if d==1 else((x<<1)&mask)|b
   if(t,y)not in seen:seen.add((t,y));queue.append((t,y))
 out={q:set()for q in range(N)}
 for q,x in seen:out[q].add((x>>(radius-projection))&((1<<(2*projection+1))-1))
 return out,len(seen)

# Each pair is (least permitted value, whether arbitrary nonnegative is added).
CHOICES={1:((0,False),),2:((1,False),),3:((0,False),(1,False)),4:((2,True),),5:((0,False),(2,True)),6:((1,True),),7:((0,True),)}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('output',type=Path);ap.add_argument('--radius',type=int,default=2);ap.add_argument('--startup',type=int,default=58154);ap.add_argument('--only-sites',type=int,nargs='*');ap.add_argument('--base-contexts',type=Path);a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 sites=json.loads((a.input/'sites.json').read_text());labels=json.loads((a.input/'labels.json').read_text());N=len(labels)-1;table={}
 for ln in(a.input/'machine.tm').read_text().splitlines():
  if not ln or ln.startswith('#'):continue
  q,b,w,d,t=ln.split();table[int(q),int(b)]=int(w),1 if d=='R'else-1,int(t)
 need(len(table)==2*N,'table census')
 if a.base_contexts is not None or a.only_sites is not None:
  need(a.base_contexts is not None and a.only_sites is not None,'differential inputs must be supplied together')
  import closing_diff
  differential=closing_diff.verify()
  need(differential['base_context_sha256']==hashlib.sha256(a.base_contexts.read_bytes()).hexdigest(),'differential base context binding failed')
  need(differential['affected_source_sites']==sorted(a.only_sites),'differential source subset differs')
  current_hash=hashlib.sha256((a.input/'machine.tm').read_bytes()).hexdigest()
  admitted=[v for v in differential['variants'].values()if v['machine_sha256']==current_hash]
  need(len(admitted)==1,'table absent from differential certificate')
  need(admitted[0]['source_sha256']==hashlib.sha256((a.input/'sites.json').read_bytes()).hexdigest(),'differential source binding failed')
  need(admitted[0]['labels_sha256']==hashlib.sha256((a.input/'labels.json').read_bytes()).hexdigest(),'differential label binding failed')
 legacy={int(k):v for k,v in json.loads((INP/'legacy_mapping.json').read_text()).items()}
 for q in labels:legacy.setdefault(q,q+1000)
 mapping={legacy[q]:i for i,q in enumerate(labels)};rows={(legacy[labels[q]],b):(w,d,legacy[labels[t]])for(q,b),(w,d,t)in table.items()}
 audit=json.loads((a.input/'invariant_receipt.json').read_text())
 from fast_contexts import program
 _,instructions=program(sites)
 graph_lines=[str(len(sites))]
 for instruction in instructions:
  op=instruction[0]
  code=0 if op=='halt' else 1 if op=='jump' else 2 if op=='inc' else 3
  graph_lines.append(' '.join(map(str,(code,)+instruction[1:])))
 graph_bytes=('\n'.join(graph_lines)+'\n').encode()
 need(audit.get('closure_audited') is True,'fixed-point closure audit missing')
 need(audit.get('initial_site')==25 and audit.get('initial_exact_registers')==[2]+[0]*8,'wrong initial seed')
 need(hashlib.sha256(graph_bytes).hexdigest()==audit['graph_sha256'],'source-to-invariant graph binding failed')
 need(graph_bytes==(a.input/'source_graph.txt').read_bytes(),'stored source graph differs')
 buf=(a.input/'invariant.bin').read_bytes()
 need(hashlib.sha256(buf).hexdigest()==audit['bitset_sha256'],'fixed-point digest binding failed')
 n=len(sites);full=np.unpackbits(np.frombuffer(buf,dtype=np.uint8),bitorder='little')[:n*3**9].reshape(n,3**9)
 marginals=np.zeros((n,9),dtype=np.uint8)
 for j in range(9):marginals[:,j]=full.reshape(n,3**(8-j),3,3**j).any(axis=(1,3))@np.array([1,2,4],dtype=np.uint8)
 (a.output/'marginals.json').write_text(json.dumps(marginals.tolist())+'\n');need(int(full.sum())==4319427,'fixed point cardinality')
 del full
 collector=Collector(mapping,a.radius,N)
 if a.base_contexts:
  for ln in a.base_contexts.read_text().splitlines():
   q,b,m=map(int,ln.split());need((m>>a.radius)&1==b,'base context bit');collector.windows[q].add(m)
 collector.original=s.State.step;original_var=s.var
 lemmas,blocks=s.prove_blocks(rows);list_states={ev[1][0]for block in blocks for ev in block['trace']}
 s.State.step=lambda state,table,lemmas,clock,motion:collector.observe(state,table,lemmas,clock,motion)
 started=time.monotonic();contracts=0;branches=0;unreachable=[]
 for i,site in enumerate(sites):
  if a.only_sites is not None and i not in a.only_sites:continue
  masks=list(map(int,marginals[i]));pc,op,arg=site
  if masks[0]==0:unreachable.append(i);continue
  for positive in([False,True]if op=='CD'else[False]):
   ms=masks.copy()
   if op=='CD':ms[arg]&=6 if positive else 1
   if not all(ms):continue
   branches+=1
   for assignment in itertools.product(*(CHOICES[m]for m in ms)):
    def cv(j):
     if j==11:return s.num(1)
     if not 2<=j<=10:return original_var(j)
     minimum,variable=assignment[j-2]
     if op=='CD'and positive and j-2==arg:minimum-=1
     return s.add(original_var(j),s.num(minimum))if variable else s.num(minimum)
    s.var=cv
    try:s.case(rows,lemmas,site,positive)
    except BaseException as ex:raise RuntimeError((i,site,positive,masks,assignment))from ex
    contracts+=1
  if i%500==499:print('sites',i+1,'affine_cases',contracts,'windows',sum(map(len,collector.windows.values())),'seconds',round(time.monotonic()-started,1),flush=True)
 s.var=original_var
 tape=set();q=0;h=0;R=a.radius
 for _ in range(a.startup):
  collector.windows[q].add(sum(int(h+j in tape)<<(j+R)for j in range(-R,R+1)))
  w,d,q=table[q,int(h in tape)];(tape.add if w else tape.discard)(h);h+=d
 expected={h-1,h,h+48};p=h+49
 for v in[0,0,0,0,0,0,2,0,0]+[1]*26:expected.update(range(p+1,p+v+2));p+=v+2
 need(q==labels.index(84)and tape==expected,'startup')
 global_windows,closure=blank(table,N,6,R)
 source_raw=sum(map(len,collector.windows.values()))
 # Every generic-list interior was expanded over the exact all-one spare invariant.
 # Both are independently sound. Intersecting does not add engine windows.
 refined={q:collector.windows[q]&global_windows[q]for q in collector.windows}
 data=''.join(f'{q} {(m>>R)&1} {m}\n'for q in range(N)for m in sorted(refined[q]))
 (a.output/'source_contexts.txt').write_text(data)
 receipt=dict(differential_cases_reverified=bool(a.base_contexts),radius=a.radius,only_sites=a.only_sites,base_context_sha256=hashlib.sha256(a.base_contexts.read_bytes()).hexdigest()if a.base_contexts else None,machine_sha256=hashlib.sha256((a.input/'machine.tm').read_bytes()).hexdigest(),invariant_sha256=hashlib.sha256(buf).hexdigest(),source_sha256=hashlib.sha256((a.input/'sites.json').read_bytes()).hexdigest(),invariant_receipt_sha256=hashlib.sha256((a.input/'invariant_receipt.json').read_bytes()).hexdigest(),source_graph_sha256=audit['graph_sha256'],verified_invariant_digest_binding=True,source_branches=branches,affine_cases=contracts,unreachable_sites=unreachable,exact_startup_steps=a.startup,symbolic_steps=collector.steps,unary_events=collector.unary,list_calls=collector.list_calls,exact_spare_value=1,minimum_spare_tail_blocks=25,periodic_list_cases=len(collector.list_cases),periodic_list_literal_steps=collector.list_literal_steps,list_interior_states_dense=sorted(mapping[q]for q in list_states),source_and_startup_windows=source_raw,blank_window_closure=closure,windows=sum(map(len,refined.values())),context_sha256=hashlib.sha256(data.encode()).hexdigest(),seconds=time.monotonic()-started,scope='Source-reachable trit marginal Cartesian overapproximation; exact affine frame cases and blank startup; all spare values equal1, with25 or more tail blocks; periodic list interiors checked explicitly; no proof-assistant check')
 (a.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
