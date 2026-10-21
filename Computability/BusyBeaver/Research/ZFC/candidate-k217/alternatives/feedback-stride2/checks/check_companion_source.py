"""Owned independent CFG/closed-block audit for common-footer scratch bias."""
from pathlib import Path
from functools import lru_cache
import argparse, json, hashlib
if not __debug__: raise RuntimeError('Assertions must be enabled')
HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description='Exact source and CFG binding for global-bias companion; does not certify binary runtime.')
parser.add_argument('--old', type=Path, default=HERE/'context-root.reference.sites.json')
parser.add_argument('--baseline', type=Path, default=HERE/'composite-transfer.reference.sites.json')
parser.add_argument('--new', type=Path, default=HERE/'global_bias.sites.json')
parser.add_argument('--output', type=Path, default=HERE/'GLOBAL_BIAS_SOURCE_AUDIT.json')
args=parser.parse_args()
pold,pnew=args.old,args.new

def tree(rows):
 leaves={p:(op,k) for p,op,k in rows}
 assert len(leaves)==len(rows)
 used=[]
 def build(p):
  if p in leaves: used.append(p); return leaves[p]
  assert any(q.startswith(p) for q in leaves), ('incomplete tree',p)
  return build(p+'0'),build(p+'1')
 t=build(''); assert used==[r[0] for r in rows]; return t

def leaf(t):return isinstance(t[0],str)
@lru_cache(None)
def length(t):return 1 if leaf(t) else length(t[0])+length(t[1])
def at(t,p):
 for c in p:t=t[int(c)]
 return t
def nodes(t):
 out=set()
 def walk(x):
  if x in out:return
  out.add(x)
  if not leaf(x):walk(x[0]);walk(x[1])
 walk(t);return out

def continuation_cfg(t):
 N=length(t);out=[]
 def walk(n,start,breaks,continues):
  if leaf(n):
   op,k=n;after=(start+1)%N
   def target(stack,k):return stack[-k]%N if len(stack)>=k else 0
   edges=[] if op=='CH' else [target(continues,k)] if op=='CC' else [target(breaks,k)] if op=='CB' else [target(breaks,1),after] if op=='CD' else [after]
   assert len(out)==start
   out.append([op,None if op in ('CB','CC') else k,edges]);return
  end=start+length(n);middle=start+length(n[0])
  walk(n[0],start,breaks+[end],continues)
  walk(n[1],middle,breaks,continues+[start])
 walk(t,0,[],[]);return out
osites=json.loads(pold.read_text());nsites=json.loads(pnew.read_text());old=tree(osites);new=tree(nsites)
assert hashlib.sha256(pold.read_bytes()).hexdigest()=='19074981026ca9a46030f13ac57231f5b5131c7d826cf02739bf232ede591ba8'
assert hashlib.sha256(pnew.read_bytes()).hexdigest()=='ab25e03f724b45011660aeecb120a27b896a5f5dca0cb3848dbfde49bccd42d8'
# Independent interval-based resolver, separate from A's continuation CFG.
def resolve(rows):
 leaves={p:i for i,(p,_,_)in enumerate(rows)};intervals={}
 def visit(p):
  if p in leaves:a=leaves[p];v=(a,a+1)
  else:
   l=visit(p+'0');r=visit(p+'1');assert l[1]==r[0];v=l[0],r[1]
  intervals[p]=v;return v
 assert visit('')==(0,len(rows))
 def unwind(p,edge,k):
  while p:
   bit=p[-1];p=p[:-1]
   if bit==edge:
    k-=1
    if k==0:return intervals[p][0] if edge=='1' else intervals[p][1]%len(rows)
  return 0
 out=[]
 for i,(p,op,k)in enumerate(rows):
  if op=='CI':edge=[(i+1)%len(rows)]
  elif op=='CD':edge=[unwind(p,'0',1),(i+1)%len(rows)]
  elif op=='CB':edge=[unwind(p,'0',k)]
  elif op=='CC':edge=[unwind(p,'1',k)]
  else:assert op=='CH';edge=[]
  out.append([op,k if op in ('CI','CD') else None,edge])
 return out
oc=resolve(osites);nc=resolve(nsites);assert oc==continuation_cfg(old);assert nc==continuation_cfg(new)
assert len(osites)==4732 and len(nsites)==4734
assert nsites[-2:]==[['110','CI',6],['111','CC',3]]
assert nc[-2:]==[['CI',6,[4733]],['CC',None,[0]]]
# Every old command-return edge is redirected to the unique common increment.
changes=[]
for i,(a,b)in enumerate(zip(oc,nc)):
 if a!=b:changes.append([i,a,b])
 expected_edges=[4732 if j==0 else j for j in a[2]]
 assert b[2]==expected_edges,(i,a,b)
 assert a[:2]==b[:2] or i==4696 and a[:2]==['CC',None] and b[:2]==['CB',None]
assert [x[0]for x in changes]==[4696,4729]
assert at(new,'0')==at(old,'0')
# Exact unchanged MP and AX command bodies from calibrated transfer baseline.
base=tree(json.loads(args.baseline.read_text()))
assert hashlib.sha256(args.baseline.read_bytes()).hexdigest()=='05e7caa159d95cdf9ee254d313c44c52369ac91e52cbc23d54b15f0b64b95922'
assert at(new,'100101')==at(base,'110101')
assert at(new,'1001001')==at(base,'1101001')
# Entire short-transfer body is the original clear/copy/pop implementation.
assert at(new,'101')==(at(old,'101'),at(old,'11'))
# Exact top-level register interpreter, only small arithmetic corroboration.
def run(pc,stop,reg,cap=1000000):
 reg=list(reg)
 for n in range(cap):
  if n and pc==stop:return reg,n
  op,k,edges=nc[pc]
  if op=='CI':reg[k]+=1;pc=edges[0]
  elif op=='CD':b=int(reg[k]>0);reg[k]-=b;pc=edges[b]
  elif op in ('CB','CC'):pc=edges[0]
  else:raise AssertionError(('unexpected halt',pc))
 raise AssertionError('probe budget exceeded')
from math import isqrt
def unpair(n):
 s=(isqrt(8*n+1)-1)//2;b=n-s*(s+1)//2;return s-b,b
probes=0
for N in range(30):
 for L in range(20):
  for bias in (0,1):
   r=[N,17,29,0,13,23,bias,0,L];out,_=run(0,23,r);want=r[:]
   if L:
    a,b=unpair(L-1+bias);want[8]=b
   else:
    a,b=unpair(N);want[0]=N+bias+1;want[8]=b
   want[3]=a;want[6]=want[7]=0
   assert out==want,(r,out,want);probes+=1
# Footer is two literal instructions and restores the unique bias invariant.
for N in (0,1,17):
 for L in (0,1,13):
  r=[N,19,23,0,29,31,0,0,L];out,steps=run(4732,0,r);want=r[:];want[6]=1
  assert out==want and steps==2;probes+=1
rec={'status':'PASS','source_sha256':hashlib.sha256(pnew.read_bytes()).hexdigest(),'reference_sha256':hashlib.sha256(pold.read_bytes()).hexdigest(),'baseline_sha256':hashlib.sha256(args.baseline.read_bytes()).hexdigest(),'leaves':len(nsites),'dag_nodes':len(nodes(new)),'independent_CFG_resolvers_agree':True,'changed_return_edges':changes,'common_footer':nc[-2:],'unchanged_MP_AX_and_short_transfer':True,'finite_prelude_footer_probes':probes,'scope':'Exact full finite CFG and block identity. All-natural source semantics established by accompanying loop-invariant proof. Binary runtime and blank startup are separate obligations.'}
args.output.write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
