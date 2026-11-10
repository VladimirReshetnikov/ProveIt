#!/usr/bin/env python3
"""Source-only radix/byte pattern fixtures; files remain external evidence."""
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
patterns=[];index={};layout=[]
for j in range(253):
 ds=tuple(digits[8*j:min(8*j+8,len(digits))]);bs=tuple(raw[::-1][47*j:47*(j+1)])
 assert sum(x*radix**k for k,x in enumerate(ds))==sum(x*256**k for k,x in enumerate(bs))
 pair=(ds,bs)
 if pair not in index:index[pair]=len(patterns);patterns.append(pair)
 layout.append(index[pair])
assert len(patterns)==126 and len(layout)==253
fmt=lambda xs:'['+', '.join(map(str,xs))+']'
for g in range(8):
 out=['import DiophantineConsistency.Sign17KRadixStreamCurrent','','/-! SOURCE ONLY. Radix/byte numeric fixtures; source file provenance is external. -/','set_option autoImplicit false','noncomputable section',f'namespace DiophantineConsistency.Sign17KBytePatterns{g:02d}','']
 for j in range(16*g,min(16*g+16,len(patterns))):
  ds,bs=patterns[j];out += [f'theorem pattern{j:03d} :',f'    Nat.ofDigits CurrentKernel2011.radix {fmt(ds)} =',f'      Nat.ofDigits 256 {fmt(bs)} := by','  decide +kernel','']
 out += [f'end DiophantineConsistency.Sign17KBytePatterns{g:02d}']+[f'#print axioms DiophantineConsistency.Sign17KBytePatterns{g:02d}.pattern{j:03d}' for j in range(16*g,min(16*g+16,len(patterns)))]
 (P/f'Sign17KBytePatterns{g:02d}.lean').write_text('\n'.join(out)+'\n')
(P/'layout.json').write_text(json.dumps({'indices':layout,'distinct':len(patterns),'blocks':len(layout),'scope':'external fixture pattern mapping, not a Lean binding'},indent=2)+'\n')
print('SOURCE_ONLY 126 fixture patterns across 8 modules; no Lean or file theorem')
