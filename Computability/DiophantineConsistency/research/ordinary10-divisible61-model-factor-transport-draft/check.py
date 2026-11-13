from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary10-divisible61-model-factor-transport-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s=(D/'Divisible61ModelFactors.lean.src').read_text()
for name in ('normalized_first_of_signed','reconstructed_first_root'):
 assert re.search(r'^theorem '+name+r'\b',s,re.M)
 assert '#print axioms DiophantineConsistency.Divisible61ModelFactorsDraft.'+name in s
for x in ('ModelRelationCombining.sq_dvd_sq','nonneg_iff.mp','P72Root.ι_tsub',
 'let r : V := (tau-ell)+k*(b*h-1)+h','(hB : 0<B)',
 '(hnorm : z*z=ι b*ι b*(1+ι ell*(ι ell+ι k)))'):
 assert x in s,x
assert not re.search(r'\b(?:sorry|admit|axiom)\b',s)
q=Path('Lean/DiophantineConsistency/ModelRelationCombining.lean').read_text()
assert 'theorem sq_dvd_sq (m s : DiffRing V) (hm : m ≠ 0) (h : m ^ 2 ∣ s ^ 2) : m ∣ s' in q
assert 'theorem nonneg_iff {x : DiffRing V}' in Path('Lean/DiophantineConsistency/ModelDifferenceRing.lean').read_text()
assert 'theorem ι_tsub {a b : V} (h : b ≤ a)' in Path('Lean/DiophantineConsistency/Compact44/P72Root.lean').read_text()
assert 'theorem xzero_impossible' in Path('research/ordinary13-residue90-xzero-model-draft/Residue90XZeroArithmetic.lean.src').read_text()
assert 'theorem scaled_quotient' in Path('Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean').read_text()
# Independent bounded first-norm controls for both signed roots and the
# tsub formula. Norm equations not found are not counted as counterexamples.
count=0
for b in range(1,8):
 for h in range(1,8):
  for ell in range(16):
   for k in range(1,16):
    rad=1+ell*(ell+k);tau=__import__('math').isqrt(rad)
    if tau*tau!=rad:continue
    r=(tau-ell)+k*(b*h-1)+h
    assert tau>ell and r>=0 and b*(ell+k+r-k*b*h)-b*h==b*tau
    for sign in (-1,1):
     z=sign*b*tau
     assert z*z==b*b*rad and (b*h)%b==0
    count+=1
assert count>0
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'two_unelaborated_factor_level_declarations':True,'exact_qualified_source_interfaces_observed':True,
 'finite_first_norm_controls':count,'graph_zero_maps_or_provider_validation':False,
 'lean_executed':False},sort_keys=True,indent=2))
