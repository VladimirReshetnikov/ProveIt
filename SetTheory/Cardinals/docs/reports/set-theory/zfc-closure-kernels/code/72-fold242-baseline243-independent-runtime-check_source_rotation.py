"""Own source-context, universal rotation induction and frame-closure checker.
Supplied source JSON is data; no repository code is imported or executed.
"""
from pathlib import Path
import hashlib,json,sys
if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions required')
import independent_runtime as r
import source_calibration as c
ROOT=Path(__file__).resolve().parent.parent;S=ROOT/'sources'
PRIOR=ROOT/'prior'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
op=PRIOR/'certificate__sites_logical.json';np=S/'candidate-combined243__sites_logical.json'
assert sha(op)=='f77a3fb9729382a0b8cd24d480639862b63ecb76bbc205542d1fc7077c025745'
assert sha(np)=='3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'
old=json.loads(op.read_text());new=json.loads(np.read_text())
physical=json.loads((S/'candidate-combined243__sites_physical.json').read_text())
assert physical==[[p,ins,r.PHY[arg] if ins in ('CI','CD') else arg] for p,ins,arg in new]
assert old[6:10]==[['01100','CD',6],['011010','CI',0],['011011','CC',2],['0111','CI',0]]
assert new[6:9]==[['0110','CI',0],['01110','CD',6],['01111','CC',2]]
assert old[:6]==new[:6] and old[10:]==new[9:]
def increment(p):
 if not p:return ''
 n=int(p,2)+1
 return format(n%(2**len(p)),'0'+str(len(p))+'b')
def trim(p,bit,count):
 for _ in range(count):
  j=p.rfind(bit)
  if j<0:return ''
  p=p[:j]
 return p
class Program:
 def __init__(self,ss):
  self.sites=ss;self.lookup={p:i for i,(p,op,arg) in enumerate(ss)}
  assert len(self.lookup)==len(ss)
  self.depth=max(map(len,self.lookup));prefixes={p[:i] for p in self.lookup for i in range(len(p))}
  assert not prefixes.intersection(self.lookup)
  assert all(p+b in self.lookup or p+b in prefixes for p in prefixes for b in '01')
  assert len(prefixes)==len(ss)-1
 def decode(self,p):
  ext=p+'0'*self.depth
  for i in range(1,self.depth+1):
   if ext[:i] in self.lookup:return self.lookup[ext[:i]]
  raise AssertionError(('Incomplete tree',p))
 def next(self,i,positive=False):
  p,op,arg=self.sites[i]
  if op=='CH':return None
  if op=='CI' or (op=='CD' and positive):nxt=increment(p)
  elif op=='CD':nxt=increment(trim(p,'0',1))
  elif op=='CB':nxt=increment(trim(p,'0',arg))
  elif op=='CC':nxt=trim(p,'1',arg)
  else:raise AssertionError(op)
  return self.decode(nxt)
a,b=Program(old),Program(new)
assert (len(old),len(new),a.depth,b.depth)==(6460,6459,51,51)
assert a.decode('')==b.decode('')==0
mapping={i:i if i<=6 else i-1 for i in range(len(old)) if i not in (7,8,9)}
edges=0;entries=[];haltpairs=[]
for i,site in enumerate(old):
 if 6<=i<=9:continue
 j=mapping[i];assert site==new[j]
 if site[1]=='CH':
  assert a.next(i) is b.next(j) is None;haltpairs.append((i,j));continue
 for positive in ((False,True) if site[1]=='CD' else (False,)):
  x=a.next(i,positive);y=b.next(j,positive)
  assert x not in (7,8,9),('Outside entry into loop interior',i,x)
  assert mapping[x]==y,(i,j,positive,x,y)
  if x==6:entries.append((i,positive,x,j,y))
  edges+=1
assert edges==8385 and entries==[(2,False,6,2,6)] and haltpairs==[(6324,6323)]

def local_symbolic(p,positive):
 # Nine independent natural entry variables plus integer offsets; X fixed0
 # or unbounded X>=1. Intervals force every test in a finite loop iteration.
 offsets=[0]*9;low=[0]*9;high=[None]*9
 low[6]=int(positive);high[6]=None if positive else 0
 q=6;trace=[];interior=set(range(6,10 if p is a else 9))
 for tick in range(8):
  if tick and (q==6 or q not in interior):break
  pc,op,arg=p.sites[q];guard=False
  if op=='CI':offsets[arg]+=1
  elif op=='CD':
   lo=low[arg]+offsets[arg];hi=None if high[arg] is None else high[arg]+offsets[arg]
   assert lo>=0
   if hi==0:guard=False
   else:assert lo>=1;guard=True;offsets[arg]-=1
  elif op!='CC':raise AssertionError(op)
  nxt=p.next(q,guard);trace.append({'site':q,'operation':op,'register_or_depth':arg,'positive':guard,'next':nxt,'offsets':offsets.copy()});q=nxt
 else:raise AssertionError('Local symbolic trace failed to finish')
 return q,offsets,trace
local=[]
for positive in (False,True):
 x,dx,tx=local_symbolic(a,positive);y,dy,ty=local_symbolic(b,positive)
 want=[0]*9;want[0]=1;want[6]=-int(positive)
 assert dx==dy==want and mapping[x]==y
 assert len(tx)==len(ty)==(3 if positive else 2)
 assert x==(6 if positive else 10) and y==(6 if positive else 9)
 local.append({'positive':positive,'old_trace':tx,'new_trace':ty,'endpoint_old':x,'endpoint_new':y,'offsets':dx})
# Fresh original constructor-site source -> previously calibrated routed tree.
orig=PRIOR/'original254-source-sites.json'
assert sha(orig)=='1e989801225be6a66477fe6c4f7dcc7c08751fc1c03cc65c321a08e8528625b0'
inherited_bisim=c.prove_bisimulation(json.loads(orig.read_text()),old)

# Whole-frame pointer identity closes every nonhalt runtime instruction result.
def pointer_equivalence(p):
 leaf=new[b.decode(p)][0]
 assert {i for i,z in enumerate(p) if z=='1'}=={i for i,z in enumerate(leaf) if z=='1'}
 assert max(len(p),len(leaf))<=64
 return leaf
pointer_equivalence('');closure=0;carry=0;gaps={}
for i,site in enumerate(new):
 for positive in ((False,True) if site[1]=='CD' else (False,)):
  vals=[0]*9
  if positive:vals[site[2]]=1
  out=r.expected(site,vals,[1])
  if out is None:continue
  nxt=out[1]['pc'];leaf=pointer_equivalence(nxt)
  assert b.lookup[leaf]==b.next(i,positive)
  delta=out[1]['gap_extra'];assert delta>=0
  gaps[delta]=gaps.get(delta,0)+1;carry+=int(out[0][1]==-1);closure+=1
assert closure==8389
result={'status':'UNIVERSAL_SOURCE_ROTATION_AND_FRAME_COMPOSITION_PASS','old_sites_sha256':sha(op),'new_sites_sha256':sha(np),'logical_physical_permutation':[int(x) for x in r.PHY],'source_leaves':6459,'guarded_cases':8390,'maximum_depth':51,'source_context':{'checked_outside_edges':edges,'sole_external_entry':entries,'halt_correspondence':haltpairs,'no_outside_interior_entry':True,'root_correspondence':True},'symbolic_iteration_cases':local,'arithmetic_induction':{'entry':'N=a, X=b, any other seven natural registers','zero_case':'Both take2 instructions, N+=1 and exit','positive_case':'Both take3 instructions, N+=1, X-=1, return to corresponding entry','exit':'N=a+b+1, X=0; all other registers preserved','exact_source_time':'3*b+2','termination':'Natural induction on b; no infinite fragment execution'},'original_to_routed_bisimulation':inherited_bisim,'frame_closure':{'nonhalting_guarded_successors':closure,'gap_extra_histogram':gaps,'carry_cases':carry,'arbitrary_gap':'64+n, n natural','nonempty_spare_preserved':True,'whole_pointer_tape_equivalence':True},'proof':'Outside fragments, corresponding source steps have identical guarded register effects and successor. Every possible fragment entry is matched and the terminating natural-number induction supplies identical exit registers. The sole halt corresponds. This is two-way root halting equivalence for all natural register vectors, without any consistency or source-reachability premise.','limitation':'Independent ordinary mathematical evidence, no freshly checked proof-assistant endpoint. The inherited original source consistency calibration is not reproved here.'}
(ROOT/'independent-runtime/source_rotation_and_composition.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='symbolic_iteration_cases'},indent=2))
