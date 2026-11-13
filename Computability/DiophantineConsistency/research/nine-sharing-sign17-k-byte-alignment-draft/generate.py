#!/usr/bin/env python3
"""Build staged block alignment source drafts; external provenance is not formalized."""
import gzip,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;R=P.parent;seed=R/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json';coeff=R/'padding-staircase-independent/coefficients.json';sha=lambda b:hashlib.sha256(b).hexdigest()
sb=seed.read_bytes();cb=coeff.read_bytes();assert sha(sb)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac' and sha(cb)=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93'
c=json.loads(cb);binding=json.loads(sb)['coefficient_binding'];rec=binding['ports']['K0'];packed=(seed.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert sha(packed)==rec['gzip_sha256'] and sha(raw)==rec['raw_sha256'] and len(raw)==11868
r=2**47;digits=[0]*2021
for i,x in enumerate(c):
 if x:digits[1005-i]+=x
for j in (18,1004,2020):digits[j]+=1
patterns=[];ids={};layout=[];pairs=[]
for j in range(253):
 ds=tuple(digits[8*j:min(8*j+8,len(digits))]);bs=tuple(raw[::-1][47*j:47*(j+1)]);pair=(ds,bs)
 assert sum(x*r**k for k,x in enumerate(ds))==sum(x*256**k for k,x in enumerate(bs))
 if pair not in ids:ids[pair]=len(patterns);patterns.append(pair)
 pairs.append(pair);layout.append(ids[pair])
assert len(patterns)==126 and len(layout)==253
old=json.loads((R/'nine-sharing-sign17-k-byte-patterns-draft/layout.json').read_text());assert old['indices']==layout
fmt=lambda xs:'['+', '.join(map(str,xs))+']'
base='''import DiophantineConsistency.Sign17KBytePatterns00

/-! SOURCE ONLY. Generic radix/byte block alignment. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KByteAlignmentCore

def aligned (digits bytes : List ℕ) : Prop :=
  digits.length = 8 ∧ bytes.length = 47 ∧
    Nat.ofDigits CurrentKernel2011.radix digits = Nat.ofDigits 256 bytes

end DiophantineConsistency.Sign17KByteAlignmentCore
'''
(P/'Sign17KByteAlignmentCore.lean').write_text(base)
for g in range(8):
 lo=32*g;hi=min(lo+32,252);out=['import DiophantineConsistency.Sign17KByteAlignmentCore']+[f'import DiophantineConsistency.Sign17KBytePatterns{k:02d}' for k in sorted({layout[j]//16 for j in range(lo,hi)})]
 out += ['','/-! SOURCE ONLY. One finite alignment group. -/','set_option autoImplicit false','noncomputable section',f'namespace DiophantineConsistency.Sign17KByteAlignment{g:02d}','',f'def digitBlocks : List (List ℕ) := [{", ".join(fmt(pairs[j][0]) for j in range(lo,hi))}]',f'def byteBlocks : List (List ℕ) := [{", ".join(fmt(pairs[j][1]) for j in range(lo,hi))}]','',f'theorem aligned : List.Forall₂ Sign17KByteAlignmentCore.aligned digitBlocks byteBlocks := by','  unfold digitBlocks byteBlocks']
 for j in range(lo,hi):
  k=layout[j];out.append(f'  refine List.Forall₂.cons ⟨rfl, rfl, Sign17KBytePatterns{k//16:02d}.pattern{k:03d}⟩ ?_')
 out += ['  exact List.Forall₂.nil','',f'end DiophantineConsistency.Sign17KByteAlignment{g:02d}',f'#print axioms DiophantineConsistency.Sign17KByteAlignment{g:02d}.aligned']
 (P/f'Sign17KByteAlignment{g:02d}.lean').write_text('\n'.join(out)+'\n')
print('SOURCE_ONLY 252 full blocks in 8 groups; tail 252 separate')
