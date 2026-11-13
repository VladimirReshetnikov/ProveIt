from pathlib import Path
from hashlib import sha256
import ast,json,math,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-f-unshift-small-power-w-gcd-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-f-unshift-fixed-small-power-w-gcd')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
C=Path('Lean/DiophantineConsistency/Compact44')
s=(C/'Compact943Data.lean').read_text();body=s.split('-- BEGIN PINNED ORDERED ROWS',1)[1].split('-- END PINNED ORDERED ROWS',1)[0]
rows=ast.literal_eval('['+body+']');assert len(rows)==943 and all(len(row)==4 for row in rows)
s=(C/'CompactSymbolicKernel.lean').read_text();slots=ast.literal_eval(re.search(r'^def slots : List ℕ := (\[[^\n]+\])$',s,re.M).group(1));assert len(slots)==41 and all(0<=i<4393 for i in slots) and 'def rho : ℕ := 2^67' in s
s=(C/'CompactFixedBeta.lean').read_text();assert 'def betaNat : ℕ := 2^(67*8807)-1' in s
s=(C/'CompactCoefficientMass.lean').read_text()
assert 't.1 + 2^8*t.2.1 + 2^17*t.2.2.1 + 2^25*t.2.2.2 + 127*2^34' in s
assert '1 + 2^10 * (2^41 - value t)' in s
s=(C/'CompactSymbolicKernelOpaque.lean').read_text()
for x in ('r^30+r^62+r^1100+r^2201','r^(4393-i.val)+r^(5495-i.val)',
 'r^(4393-position i)+r^(5495-position i)','r^8807*r^42'):assert x in s
# Reconstruct the same finite integer via coefficient accumulation followed
# by base-rho Horner evaluation, independently of the bit-shift summation.
rho=2**67;coeff=[0]*5496
for e in (42,30,62,1100,2201):coeff[e]+=1
for j,(a,b,c,d) in enumerate(rows):
 value=a+256*b+131072*c+33554432*d+127*2**34
 assert 0<value<2**41
 sel=1+1024*(2**41-value)
 coeff[4393-j]+=sel;coeff[5495-j]+=sel
for j,pos in enumerate(slots):
 coeff[4393-pos]+=2**(10+j);coeff[5495-pos]+=2**(10+j)
kp=0
for x in reversed(coeff):kp=kp*rho+x
beta=rho**8807-1
assert 0<kp<rho**5496 and beta.bit_length()==590069 and kp.bit_length()==368209
# C-implemented integer gcd on independently reconstructed exact integers;
# report only the eight small results, never the giant operands.
results=[math.gcd(beta,kp+2**e) for e in range(8)];assert results==[1]*8
# Child literal's exact signed root and F=0 carrier use.
g=json.loads(Path('research/ordinary13-eta85-shift-boundary-probes/F-probe.json').read_text());r={n:(op,a,b) for n,op,a,b in g['source']}
for n,row in {'qm':('*','n_J','beta'),'q':('+',1,'qm'),'X':('*','q','n_w'),
 'C':('-','qF','alpha'),'g26':('+','X','K0'),'g27':('*','C','g26'),
 'Bt':('-','g27','n_F'),'folded_kBt':('*','k','Bt'),
 'folded_g31':('-','g31','folded_kBt'),'Z':('-','g32','Bt'),
 'A0':('-','g38','g42')}.items():assert r[n]==row,(n,r[n])
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduced':True,'ordered_rows':len(rows),'slots':len(slots),
 'independent_base_rho_Horner_kernel':True,'Kprime_bit_length':kp.bit_length(),
 'beta_bit_length':beta.bit_length(),'independent_input_exact_gcds':results,
 'literal_first_carrier_rows_checked':True,
 'scope':'Conditional F=0,C>0,J=1 first-norm result for eight entire w classes; no zero exclusion or all-model proof.',
 'large_numerals_printed_or_written':False,'lean_executed':False},sort_keys=True,indent=2))
