#!/usr/bin/env python3
"""Reconstruct fixed K' as a bounded bit integer and prove eight exact gcds."""
import hashlib,json,math,re
from pathlib import Path
root=Path(__file__).resolve().parents[2]; here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
base=root/'Lean/DiophantineConsistency/Compact44'
s=(base/'Compact943Data.lean').read_text()
body=s.split('-- BEGIN PINNED ORDERED ROWS',1)[1].split('-- END PINNED ORDERED ROWS',1)[0]
rows=[tuple(map(int,x)) for x in re.findall(r'^\s*\(\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+)\s*\)',body,re.M)]
s=(base/'CompactSymbolicKernel.lean').read_text()
slots=[int(x) for x in re.search(r'def slots : List ℕ := \[([^]]+)\]',s).group(1).split(',')]
assert len(rows)==943 and len(slots)==41 and all(0<=i<4393 for i in slots)
assert 'def rho : ℕ := 2^67' in s
s=(base/'CompactFixedBeta.lean').read_text();assert 'def betaNat : ℕ := 2^(67*8807)-1' in s
s=(base/'C44Short15Facts.lean').read_text();assert 'abbrev c44 : Fin 4 → ℕ := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat' in s
s=(base/'CompactCoefficientMass.lean').read_text()
for x in ['t.1 + 2^8*t.2.1 + 2^17*t.2.2.1 + 2^25*t.2.2.2 + 127*2^34','1 + 2^10 * (2^41 - value t)']:assert x in s
s=(base/'CompactSymbolicKernelOpaque.lean').read_text()
for x in ['r^30+r^62+r^1100+r^2201','∑ i : Fin 943','r^(4393-i.val)+r^(5495-i.val)',
          '∑ i : Fin 41','2^(10+i.val)','r^(4393-position i)+r^(5495-position i)',
          'r^8807*r^42']:assert x in s
# K0 = beta*rho^42 + Kprime; rho^8807*rho^42 contributes rho^42 to Kprime.
kp=sum(1<<(67*e) for e in (42,30,62,1100,2201))
for j,(a,b,c,d) in enumerate(rows):
 value=a+2**8*b+2**17*c+2**25*d+127*2**34
 assert 0<value<2**41
 selector=1+2**10*(2**41-value)
 kp+=selector*((1<<(67*(4393-j)))+(1<<(67*(5495-j))))
for j,pos in enumerate(slots):
 kp+=2**(10+j)*((1<<(67*(4393-pos)))+(1<<(67*(5495-pos))))
N=67*8807;beta=(1<<N)-1
assert 0<kp<1<<(67*5496)
results=[math.gcd(beta,kp+(1<<e)) for e in range(8)]
assert results==[1]*8
print(json.dumps({'fixed_beta_bit_length':beta.bit_length(),'Kprime_bit_length':kp.bit_length(),
 'ordered_rows':len(rows),'slots':len(slots),'exponents':list(range(8)),
 'gcd_results':results,'condition_on_w':'w congruent to 2^e mod beta',
 'forces_C_beta_and_alpha_1_when_F_zero_J_one':True,
 'branch_contradiction':False,'full_zero_proved':False,'lean_executed':False,
 'large_numerals_written_or_printed':False},indent=2,sort_keys=True))
