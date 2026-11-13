#!/usr/bin/env python3
"""Bounded pinned textual checks of important 79 theorem interfaces. No Lean."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];base=D/'research/ordinary14-natural79-corrected-reflection-overlay/source'
pins={
'Natural79ZeroWUnits.lean.src':'2570ae56ca0c4081b9442d768d94a4ded2cb365b74ed66bfe040c202b65aec1c',
'Natural79ConcreteUnits.lean.src':'253421a5ac864a94a9926472d9c469c2997d6581cded0aaa3fda27b2830d118d',
'Natural79ZeroWJPos.lean.src':'f1cf89c29eebe2259069dd26fd66d8cece75d48374358cc95ab9cc1ba83a2f0a',
'Natural79ZeroWMainNorm.lean.src':'afacf4636f4b66e2bff939300347ba5568b72d477a3028ec0a424aba42ce8009',
'ForcedWDivisibility.lean.src':'111f5a6da543baf6f08b3b1c6e5e8371cfb222197ba4566b8693598edffb6833',
'Natural79ZeroWRootCut.lean.src':'c3fd2660899139ddd335214893e5698a4124399432604111a6aa1942bc8009ec',
'Natural79ZeroWDivisibility.lean.src':'4ab36ba289a4cfce93d80bcc6bcb2cc75f0ca2a64d0a729b076846775dac0896',
'Natural79WShift.lean.src':'7635b50c819f665a6d9410758b3db01c70d3b42c1fff2aee6f3733263f76d7a1',
'Natural79Endpoint.lean.src':'9b527ff7a8b6e166869f2565b83a8c37956680d538c49557de9c82ea1a6041e6',
'NaturalDvdReflectionSlim.lean.src':'90acd025abeaf3e687a28e1e4d2c8695f8443340848430419e3057c4c7ff33f4'}
providers={
'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean':'ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d',
'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean':'9e80ae52f5dddd21d50684ebb6ca6556e95ac37905277bc476d251b7bf59f5a4',
'Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean':'40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884',
'Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean':'d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06',
'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998',
'Lean/DiophantineConsistency/Compact44/ReducedNormSigned.lean':'c01a13fd7f48c5abeb8a6741e19adad7b9d848fc57d51057c8bbb4694139674c',
'/tmp/ipra-foundation-guarded-v2-cjHUaJun/lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic/PeanoMinus/Functions.lean':'289c1c72c5a87a8dfbd1c4f4fcbead879570dbb47ab33f4612df05f3f91ee168'}
def read(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s={n:read(base/n,h) for n,h in pins.items()}
s.update({Path(n).name:read(Path(n) if n.startswith('/') else D/n,h) for n,h in providers.items()})
def has(name,*parts):
 for p in parts:assert p in s[name],(name,p)
# The positive-factor call supplies exclusions for p, q, r and t, and yields
# exactly the first/main/aux/guard/strong order consumed by J and main clients.
has('ArithmeticSignedPairs.lean','theorem product5_positive {p q r s t : Pair V}',
 '(hp : p.1+1≠p.2) (hq : q.1+1≠q.2) (hr : r.1+1≠r.2) (ht : t.1+1≠t.2)',
 'p.1=p.2+1 ∧ q.1=q.2+1 ∧ r.1=r.2+1 ∧ s.1=s.2+1 ∧ t.1=t.2+1')
has('Natural79ZeroWUnits.lean.src','rw [swap_last] at h','exact product5_positive (product_of_zero p v hz)',
 '(nonnegative_not_negative_unit _ v hn)','(fun h => hstrong (negative_residue h))')
has('ArithmeticAdaptiveFactorUnits2011.lean','theorem negative_residue {p : Pair V} (h : p.1 + 1 = p.2) : pairResidue p = -1')
has('Natural79ZeroWJPos.lean.src','eval_one_of_pair_unit _ v units.2.2.2.1')
has('Natural79ZeroWMainNorm.lean.src','eval_one_of_pair_unit (P79NaturalForcedW.graph p).main v units.2.1',
 'obtain ⟨z,hsgn,hz2⟩ := ReducedNormSigned.natural_magnitude_square D',
 'obtain ⟨t,ht,ht2⟩ := scaled_quotient (scale beta v) z (normRhs beta v)',
 '(scale_pos beta v hb hJ) hzNat','rcases hsgn with hp | hn','refine ⟨ι t, ?_, ?_⟩','refine ⟨-ι t, ?_, ?_⟩')
has('ReducedNormSigned.lean','theorem natural_magnitude_square (x : DiffRing V)',
 '∃ a : V, (x=ι a ∨ x= -ι a) ∧ x*x=ι (a*a)')
has('ArithmeticAdaptiveQuotients2011.lean','theorem scaled_quotient (m z n : V) (hm : 0<m) (h : z*z=m*m*n)',
 '∃ t : V, z=m*t ∧ t*t=n')
has('ForcedWDivisibility.lean.src','theorem divisor_of_main_norm {R : Type*} [CommRing R] (H U d a c : R)',
 '(hdiv : H ∣ U*(d-a*c))','(hnorm : d*d=1+(a*a+H)*c*c) : H ∣ U',
 'theorem divisor_of_three_square {R : Type*} [CommRing R] (H U q Y : R)',
 '(hH : H=4*Y+3) (hU : U=Y*q*q) (hdiv : H ∣ U) : H ∣ 3*q*q')
has('Natural79ZeroWRootCut.lean.src','divisor_of_main_norm H U d Y C hd hn',
 'divisor_of_three_square H U Q Y rfl hU hHU')
has('NaturalDvdReflectionSlim.lean.src','import Foundation.FirstOrder.Arithmetic.IOpen.Basic',
 'theorem natural_dvd_of_signed (a b : V) (hd : (ι a : DiffRing V)∣ι b) : a∣b')
has('Natural79ZeroWDivisibility.lean.src','import NaturalDvdReflectionSlim',
 'apply NaturalDvdReflectionSlimDraft.natural_dvd_of_signed',
 'Arithmetic.le_of_dvd hpos hd','J_pos_of_zero_w_zero p K v hK hz hw')
has('Functions.lean','lemma le_of_dvd (h : 0 < b) : a ∣ b → a ≤ b')
has('ModelDifferenceRing.lean','theorem internalZero_iff {σ : Type*} (e : Expr σ) (v : σ → V)',
 'AdaptiveEquationSyntax2011.InternalZero e v ↔ e.evalRing (fun i => ι (v i)) = 0')
has('Natural79WShift.lean.src','v79 6 = v80 6 + 1','(positive_w : ∀ v, InternalZero (P79NaturalForcedW.graph p).output v → 0 < v 6)',
 'simpa [w, add_comm] using hz')
has('Natural79Endpoint.lean.src','Natural79WShiftDraft.exists_zero_iff_of_positive (V:=V)',
 'Natural79ZeroWDivisibilityDraft.w_pos_of_zero CompactSymbolicModelIff.p',
 'Natural80EndpointDraft.expression','sameNoZero Natural80EndpointDraft.polynomialBridge')
has('HAExpressionNoZeroEquiv.lean','(h : SameNoZero e f) (hf : PolynomialBridge f) : PolynomialBridge e')
print(json.dumps({'scope':'bounded selected source call/declaration comparisons; no elaboration or theorem claim',
 'pinned_files':len(pins)+len(providers),'checked_interfaces':['five_factor_units','signed_magnitude','scaled_quotient','root_divisibility','natural_reflection','positive_dvd_bound','valuation_transfer','nozero_bridge'],
 'confirmed_new_mismatches':0,'full_name_resolution_or_lean_check':False},sort_keys=True,indent=2))
