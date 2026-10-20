#!/usr/bin/env python3
"""Project every seeded primitive trace and accelerated loop interior to local windows.

Inherited mathematical projector from root_work/project_windows.py. This version
accepts explicit immutable inputs and proves their source product invariant
before projecting. K219's startup has gap80 and130 spare words equal to1.
The finite radius is a widening, not a bound on actual register values or time.
"""
from pathlib import Path
from functools import lru_cache
from collections import defaultdict
import sys,json,time,argparse,hashlib,struct
ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'k220_replay/baseline/K221_Construction_2026-10-20'
DEFAULT=ROOT/'baseline219/K219_Construction_2026-10-20/machine'
sys.path.insert(0,str(BASE/'portable'));import build221 as b
sys.path.insert(0,str(BASE/'portable/runtime/vendor'));import symbolic_runtime as rt
sys.path.insert(0,str(ROOT/'theory_notes'));from audit_abstract_certificate import check
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--table',type=Path,default=DEFAULT/'k219.native.tm')
ap.add_argument('--sites',type=Path,default=DEFAULT/'sites219.json')
ap.add_argument('--invariant',type=Path,default=ROOT/'machine218/abstract219.json')
ap.add_argument('--startup',type=Path,default=DEFAULT/'canonicalization.json')
ap.add_argument('--output',type=Path,default=ROOT/'machine218/windows219')
ap.add_argument('--radius',type=int,default=7)
ap.add_argument('--limit',type=int,default=0)
ap.add_argument('--residue',type=Path,default=ROOT/'root218/joint_residue.bin')
ap.add_argument('--residue-audit',type=Path,default=ROOT/'root218/joint_residue_audit.json')
a=ap.parse_args();R=a.radius;CAP=2*R+3
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
T=b.read_table(a.table.read_bytes());S=json.loads(a.sites.read_text())
cert=json.loads(a.invariant.read_text());INV=cert['domains']
assert cert['source_sha256']==sha(a.sites)
audit=check(S,INV,[3,0,0,0,3,0,0,0,0])

residue_raw=a.residue.read_bytes()
residue_audit=json.loads(a.residue_audit.read_text())
assert residue_audit['status']=='INDEPENDENT_JOINT_RESIDUE_INDUCTIVE_CERTIFICATE_PASS'
assert residue_audit['source_sha256']==sha(a.sites)
assert residue_audit['product_certificate_sha256']==sha(a.invariant)
assert residue_audit['binary_certificate_sha256']==hashlib.sha256(residue_raw).hexdigest()
rn,rbase,rwords=struct.unpack_from('<III',residue_raw)
assert (rn,rbase,rwords)==(len(S),3**9,(3**9+63)//64)
assert len(residue_raw)==12+rn*rwords*8
JOINT=[int.from_bytes(residue_raw[12+i*rwords*8:12+(i+1)*rwords*8],'little') for i in range(rn)]
POW3=[3**j for j in range(9)]
DIGIT_MASKS=[[sum(1<<m for m in range(rbase) if m//POW3[j]%3==d) for d in range(3)] for j in range(9)]
ALL_PROFILES=(1<<rbase)-1

bootcert=json.loads(a.startup.read_text());boot=bootcert['startup']
assert bootcert['table_sha256']==sha(a.table)
assert boot['logical_registers']==[3,0,0,0,3,0,0,0,0]
assert boot['extra_gap']>=CAP and len(boot['spares'])-1>2*((R+2)//3+1)
assert all(v==1 for v in boot['spares'])
mp={int(q):int(z)for q,z in json.loads((BASE/'portable/runtime/reference_results/legacy_mapping.json').read_text()).items()}
for q in {q for q,bit in T}|{254}:
 if q not in mp:mp[q]=q+1000
assert len(set(mp.values()))==len(mp)
inv={z:q for q,z in mp.items()}
L={(mp[q],bit):(w,d,mp[z])for(q,bit),(w,d,z)in T.items()}
lemmas,blocks=rt.prove_blocks(L)
windows=defaultdict(set);covered=set();domains=None;stats=defaultdict(int)
started=time.monotonic();original_step=rt.State.step


def values(mask,positive=False,residue=None):
 vals=[]
 # CAP+2 is needed for the next representative of either parity after
 # subtraction of the positive guard's one unit. CAP denotes every larger
 # value, so this truncation only widens finite prefixes.
 for n in range(CAP+3):
  digit=0 if n==0 else 1 if n%2==0 else 2
  if residue is not None and residue!=digit:continue
  if mask&(1<<min(n,4)):
   if not positive or n>0:vals.append(min(CAP,n-int(positive)))
 return tuple(sorted(set(vals)))

@lru_cache(150000)
def runlengths(affine,dom):
 poss={min(CAP,affine[0])}
 assert affine[0]>=0 and all(x>=0 for x in affine)
 for i,c in enumerate(affine[1:],1):
  if not c:continue
  poss={min(CAP,x+c*v)for x in poss for v in dom[i]}
 return tuple(sorted(poss))

@lru_cache(200000)
def prefix(atoms,length,dom):
 if length==0:return (0,)
 if not atoms:raise AssertionError('Missing tape exterior')
 aa=atoms[0]
 if aa[0]=='blank':return (0,)
 if aa[0]=='list':
  # The list has at least129 identical blocks; even after unrolling4,
  # its remaining portion has more thanR cells.  End contexts are separate.
  word=(0,1,1)if aa[1]=='B'else(1,0,1)
  if aa[3]:word=tuple(reversed(word))
  return (sum(word[i%3]<<i for i in range(length)),)
 if aa[0]=='run':bit=aa[1];ns=runlengths(aa[2],dom)
 elif aa[0]=='lengths':bit=aa[1];ns=aa[2]
 else:raise AssertionError(aa)
 ans=set()
 for n in ns:
  if n>=length:ans.add(((1<<length)-1)*bit)
  else:
   low=((1<<n)-1)*bit
   ans.update(low+(p<<n)for p in prefix(atoms[1:],length-n,dom))
 return tuple(sorted(ans))

@lru_cache(1<<16)
def left_bits(x,n,top):return sum(((x>>i)&1)<<(top-i)for i in range(n))


@lru_cache(200000)
def relevant(atoms,length,dom):
 bits=0
 for aa in atoms:
  if length<=0 or aa[0]in('blank','list'):break
  ns=runlengths(aa[2],dom)if aa[0]=='run'else aa[2]
  lower=min(ns)
  if lower>=length:break
  if aa[0]=='run':
   for j in range(9):
    if aa[2][j+2]:bits|=1<<j
  length-=lower
 return bits

@lru_cache(None)
def projected_residue_patterns(ordinal,positive,rel):
 profiles=JOINT[ordinal]
 if S[ordinal][1]=='CD':
  reg=S[ordinal][2]
  allowed=ALL_PROFILES^DIGIT_MASKS[reg][0] if positive else DIGIT_MASKS[reg][0]
  profiles &= allowed
 regs=tuple(j for j in range(9) if rel&(1<<j))
 partial=[(profiles,())]
 for j in regs:
  newer=[]
  for bitset,digits in partial:
   for d in range(3):
    cut=bitset&DIGIT_MASKS[j][d]
    if cut:newer.append((cut,digits+(d,)))
  partial=newer
 return regs,tuple(digits for bitset,digits in partial if bitset)

def collect(q,left,right,direction):
 if q not in inv or inv[q]==254:return
 nl,nr=(R,R+1)if direction==1 else(R+1,R)
 left,right=tuple(left),tuple(right)
 stats['symbolic_positions']+=1
 upper_left=prefix(left,nl,domains);upper_right=prefix(right,nr,domains)
 coverage_key=(q,nl,upper_left,upper_right)
 if coverage_key in covered:
  stats['coverage_cache_skips']+=1
  return
 upper_lvals=[left_bits(v,nl,nl-1)for v in upper_left]
 upper_rvals=[v<<nl for v in upper_right]
 present=windows[inv[q]]
 if all((lv|rv)in present for lv in upper_lvals for rv in upper_rvals):
  if len(covered)>=100000:covered.clear()
  covered.add(coverage_key)
  stats['product_coverage_skips']+=1
  return
 rel=relevant(left,nl,domains)|relevant(right,nr,domains)
 regs,patterns=projected_residue_patterns(i,positive,rel)
 for pattern in patterns:
  dd=list(domains)
  for j,digit in zip(regs,pattern):
   dd[j+2]=values(masks[j],positive and site[1]=='CD'and j==site[2],digit)
   assert dd[j+2],(i,j,digit,masks[j])
  dom=tuple(dd)
  ls=prefix(left,nl,dom);rs=prefix(right,nr,dom)
  lvals=[left_bits(v,nl,nl-1)for v in ls];rvals=[v<<nl for v in rs]
  windows[inv[q]].update(lv|rv for lv in lvals for rv in rvals)

def loop_positions(state,src,dst,atom,row):
 w,d,q=row;ns=runlengths(atom[2],domains)
 # Each k<R retains the precise finite prefix of newly written cells.
 for k in range(1,R):
  remain=tuple(sorted({min(CAP,n-k)for n in ns if n>k}))
  if not remain:continue
  ss=[('lengths',atom[1],remain)]+src[1:];dd=[rt.run(w,k)]+dst
  collect(q,dd,ss,1)if d==1 else collect(q,ss,dd,-1)
 # k>=R: the whole radius behind the head has been overwritten.
 # Forgetting the n=k+m relation is a safe widening.  Include every positive
 # residual length when the cap denotes a possible arbitrarily large run.
 if max(ns,default=0)>R:
  remain=set()
  for n in ns:
   if n==CAP:remain.update(range(1,CAP+1))
   else:remain.update(range(1,n-R+1))
  ss=[('lengths',atom[1],tuple(sorted(remain)))]+src[1:];dd=[rt.run(w,R)]+dst
  collect(q,dd,ss,1)if d==1 else collect(q,ss,dd,-1)
 stats['unary_schemas']+=1

def list_positions(state,src,dst,atom):
 key=(state.q,state.direction,atom[1],atom[3]);after=lemmas[key];nblocks=(R+2)//3+1
 beforeword=(0,1,1)if atom[1]=='B'else(1,0,1)
 if atom[3]:beforeword=tuple(reversed(beforeword))
 explicit=[rt.bit(bit)for bit in beforeword*nblocks]
 for ending in(False,True):
  ss=explicit+(src[1:]if ending else[atom]+src[1:])
  dd=([('list',after,atom[2],not atom[3])]+dst)if ending else dst
  st=rt.State(state.q,dd,ss,1)if state.direction==1 else rt.State(state.q,ss,dd,-1)
  clock=rt.ZERO;motion=rt.ZERO
  # Each block has exactly3 symbols and each displayed primitive schema
  # takes3 transitions when its represented value is1.
  while clock[0] < 3*nblocks:
   assert not any(clock[1:]), ("nonconstant list microtrace", clock)
   collect(st.q,st.left,st.right,st.direction)
   clock,motion,event=original_step(st,L,{},clock,motion)
   assert event[0]!='list'
  collect(st.q,st.left,st.right,st.direction)
 stats['list_schemas']+=1

def observed(self,table,lms,clock,motion):
 self.key();collect(self.q,self.left,self.right,self.direction)
 src,dst=(self.right,self.left)if self.direction==1 else(self.left,self.right)
 atom=src[0]
 if atom[0]=='run':
  row=table[self.q,atom[1]]
  if row[2]==self.q and row[1]==self.direction:loop_positions(self,src,dst,atom,row)
 elif atom[0]=='list':list_positions(self,src,dst,atom)
 return original_step(self,table,lms,clock,motion)
rt.State.step=observed
# Check the literal startup completely, while collecting its exact windows.
q=0;head=0;ones=set()
for tick in range(boot['steps']+1):
 windows[q].add(sum(int(head+i-R in ones)<<i for i in range(2*R+1)))
 if tick==boot['steps']:break
 w,d,q=T[q,int(head in ones)]
 if w:ones.add(head)
 else:ones.discard(head)
 head+=d
assert(q,head,sorted(ones))==(boot['native_state'],boot['head'],boot['one_cells'])
assert q==84
startup_windows={q:set(p)for q,p in windows.items()};windows=defaultdict(set)
cases=0
for i,site in enumerate(S):
 masks=INV[i]
 if masks is None:continue
 for positive in((False,True)if site[1]=='CD'else(False,)):
  if site[1]=='CD' and not(masks[site[2]]&(30 if positive else 1)):continue
  domains=tuple([(),(CAP,)]+[values(mask,positive and site[1]=='CD'and j==site[2])for j,mask in enumerate(masks)]+[(1,),(CAP,)])
  result=rt.case(L,lemmas,site,positive)
  cases+=1
  if cases%250==0:print('CASES',cases,'windows',sum(map(len,windows.values())),'seconds',round(time.monotonic()-started,1),flush=True)
  if a.limit and cases>=a.limit:break
 if a.limit and cases>=a.limit:break
out=a.output;out.mkdir(exist_ok=True,parents=True)
with(out/f'windows_postinit_r{R}.txt').open('w')as f:
 for q in sorted(windows):
  for pat in sorted(windows[q]):f.write(f'{q} {pat}\n')
postinit_patterns=sum(map(len,windows.values()))
for q,pats in startup_windows.items():windows[q].update(pats)
with(out/f'windows_r{R}.txt').open('w')as f:
 for q in sorted(windows):
  for pat in sorted(windows[q]):f.write(f'{q} {pat}\n')
receipt=dict(residue_certificate_sha256=sha(a.residue),residue_audit_sha256=sha(a.residue_audit),status='PROJECTED_ALL_SEEDED_PRIMITIVE_FAMILIES'if not a.limit else'PARTIAL',radius=R,cases=cases,postinit_patterns=postinit_patterns,patterns=sum(map(len,windows.values())),states=len(windows),per_state={q:len(pats)for q,pats in windows.items()},stats=dict(stats),seconds=time.monotonic()-started,table_sha256=sha(a.table),sites_sha256=sha(a.sites),invariant_sha256=sha(a.invariant),startup_sha256=sha(a.startup),projector_sha256=sha(Path(__file__)),minimum_gap=boot['extra_gap'],minimum_spares=len(boot['spares']),all_spares_one=True,source_invariant_audit=audit,proof_boundary='Requires independently checked product and joint-residue source invariants, symbolic runtime induction, and proved source semantics. Projection widens correlations. Unary and identical-block list interiors covered separately. No local-machine fixed-point closure is claimed. Post-initialization output requires separate bootstrap proof for any transformed machine.')
(out/f'receipt_r{R}.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt),flush=True)
