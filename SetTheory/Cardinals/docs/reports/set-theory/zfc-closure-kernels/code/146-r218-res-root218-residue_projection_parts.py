"""Relational refinement inserted into the authenticated primitive projector.

This file is source-generation input and can also be audited in isolation.
All original accelerated-loop and list-interior handling remains intact.
"""

SETUP = r'''
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
'''

VALUES = r'''
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
'''

COLLECT = r'''
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
'''
