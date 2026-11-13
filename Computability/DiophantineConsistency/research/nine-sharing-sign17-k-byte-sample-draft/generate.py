#!/usr/bin/env python3
"""Build source-only radix/byte fixture probes; external files remain evidence."""
import gzip,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;R=P.parent;seed=R/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json';coeff=R/'padding-staircase-independent/coefficients.json';sha=lambda b:hashlib.sha256(b).hexdigest()
sb=seed.read_bytes();cb=coeff.read_bytes();assert sha(sb)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac' and sha(cb)=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93'
c=json.loads(cb);binding=json.loads(sb)['coefficient_binding'];rec=binding['ports']['K0'];packed=(seed.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert sha(packed)==rec['gzip_sha256'] and sha(raw)==rec['raw_sha256'] and len(raw)==11868
radix=2**47;digits=[0]*2021
for i,x in enumerate(c):
 if x:digits[1005-i]+=x
for j in (18,1004,2020):digits[j]+=1
assert all(0<=x<radix for x in digits)
parts=[]
for j in (2,125,126,252):
 ds=digits[8*j:min(8*j+8,len(digits))];bs=list(raw[::-1][47*j:47*(j+1)])
 assert sum(x*radix**k for k,x in enumerate(ds))==sum(x*256**k for k,x in enumerate(bs))
 fmt=lambda xs:'['+', '.join(map(str,xs))+']'
 parts += [f'theorem block{j:03d} :',f'    Nat.ofDigits CurrentKernel2011.radix {fmt(ds)} =',f'      Nat.ofDigits 256 {fmt(bs)} := by', '  decide +kernel','']
out='''import DiophantineConsistency.Sign17KRadixStreamCurrent

/-! SOURCE ONLY. Selected radix/byte fixture identities; source file provenance is external. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KByteSample

'''+ '\n'.join(parts)+'''end DiophantineConsistency.Sign17KByteSample
'''+''.join(f'#print axioms DiophantineConsistency.Sign17KByteSample.block{j:03d}\n' for j in (2,125,126,252))
(P/'Sign17KByteSample.lean').write_text(out)
print('SOURCE_ONLY sample blocks 2,125,126,252; no Lean run or file theorem')
