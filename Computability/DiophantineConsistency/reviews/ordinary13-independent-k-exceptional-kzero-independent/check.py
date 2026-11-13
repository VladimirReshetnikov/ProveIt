from pathlib import Path
from hashlib import sha256
import sys,json,subprocess,itertools
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-exceptional-kzero-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for base in ('ordinary13-independent-k-first-factor-audit','ordinary13-independent-k-exceptional-kzero-audit'):
 p=Path('research')/base
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
# Independently enumerate factor residues, including all k and all signed ports mod 4.
for b,z,x,s,k in itertools.product(range(4),repeat=5):
 y=(1+b)**3*s;ell=x*y*y*k
 assert (1+z*z-b*b*(1+ell*(ell+k)))%4!=3
for u,a,c,z in itertools.product(range(4),repeat=4):
 D0=3+4*a+a*a
 assert (1+z*z-u*u*(1+D0*c*c))%4!=3
for y,v,a,f in itertools.product(range(4),repeat=4):
 D0=3+4*a+a*a
 assert (y*y-D0*(f*f-1)*(y*y-v*v))%4!=3
for i,a,f in itertools.product(range(4),repeat=3):
 D0=3+4*a+a*a
 assert (1+i*i-D0*(f*f-1))%4!=3
# Independently authenticate source-level binding of fixed K and mask tuple.
ports=Path('research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src').read_text()
chain=Path('research/ordinary13-unscale84-compact-chain-draft/Unscale84CompactChain.lean.src').read_text()
assert 'CompactSymbolicPorts.ports CompactFixedBeta.betaNat K' in ports
assert 'CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat' in ports
assert 'def fixedK : ℕ := paramKernel rho' in chain
compact=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text()
assert '![β,K,L,β+H]' in compact
assert '8807 1063 CompactConcreteMask.support' in compact
mask=Path('Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean').read_text()
assert '{1063,1064,1095,2195,3296}) \\ {1}' in mask
assert 'range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032' in mask
recipe=Path('Lean/DiophantineConsistency/Compact44/CompactListMask.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in recipe
assert 'Nat.ofDigits B ((List.range n).map f) = ∑ j ∈ range n, f j * B^j' in recipe
fixed=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in fixed
assert 'r^30+r^62+r^1100+r^2201' in Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernelOpaque.lean').read_text()
assert 'def rho : ℕ := 2^67' in Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernel.lean').read_text()
# Exceptional relation and rank congruence over bounded integer examples,
# deliberately including negative qF cases in the first root reconstruction.
cases=0;intervals=0
for beta in range(3,25):
 for J in range(1,5):
  q=1+beta*J;b=q-1
  for d in range(7,16):
   for qF in range(-3,q):
    for alpha in range(1,q+3):
     F=q-qF; C=qF-alpha; Bt=C*d-F
     if C<=0 and Bt==-b:
      assert qF*(d+1)==alpha*d+1 and qF>=1
      t=alpha-qF
      assert t>=0 and d*t==qF-1 and 7*t<beta*J
      for MC in range(beta):
       if 6*MC<=5*beta:continue
       MF=beta;G=qF*b+alpha;R=G*(q*q-1)+J*(MC+q*MF)
       u=J*MC+1-t
       assert (R+1-u)%q==0 and 2*q<3*u<3*q and 3*u%q!=0
       intervals+=1
      cases+=1
print(json.dumps({'both_author_receipts_reproduced':True,'independent_factor_mod4_controls':1600,'source_fixed_tuple_and_recipes_checked':True,'bounded_exceptional_branches':cases,'bounded_rank_interval_controls':intervals,'physical_pdf_or_provider_authentication':False,'lean_executed':False},sort_keys=True,indent=2))
