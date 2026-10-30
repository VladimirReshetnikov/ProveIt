import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRACseqWitnessBound
import DiophantineConsistency.PRAFixSuccWitnessBound
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRACseqFixpointBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem zero_bound (φ : Fixpoint.Blueprint 0) (z w : V) :
 φ.prBlueprint.zero.val.Evalb ![z] → (bnd φ.prBlueprint.zero.val).Evalb ![z,w] := by
  simp [Fixpoint.Blueprint.prBlueprint,bnd_open]
 theorem cseq_fixpoint_bound (φ : Fixpoint.Blueprint 0) (s w : V)
 (hsize : 2*s+1 ≤ w)
 (hseq : PRASeqFullWitnessBound.seqMajorant s ≤ w)
 (hlh : PRANegLhWitnessBound.negLhMajorant s ≤ w)
 (hrel : ∀ x y, x ≤ 2*s+1 → y ≤ s → PRAMemRelWitnessBound.memRelMajorant s x y ≤ w)
 (hrelneg : PRANegBitFullWitnessBound.negBitMajorant s ≤ w)
 (hpos : PRABitFullWitnessBound.bitMajorant s ≤ w)
 (hneg : PRANegBitFullWitnessBound.negBitMajorant s ≤ w)
 (hcore : ∀ u z i x, u < s → z < s → i < 2*s → x < u+(i+1) → φ.core.sigma.val.Evalb ![x,z] →
  (bnd φ.core.sigma.val).Evalb ![x,z,w])
 (hcoreneg : ∀ u z i x, u < s → z < s → i < 2*s → x < u+(i+1) → (∼φ.core.pi.val).Evalb ![x,z] →
  (bnd (∼φ.core.pi.val)).Evalb ![x,z,w]) :
 φ.prBlueprint.cseqDef.val.Evalb ![s] → (bnd φ.prBlueprint.cseqDef.val).Evalb ![s,w] := by
  apply PRACseqWitnessBound.cseq_bound φ.prBlueprint s w hsize hseq hlh hrel hrelneg
  · intro z hz he
    exact zero_bound φ z w he
  · intro u z i hu hz hi he
    have hp : PRABitFullWitnessBound.bitMajorant u ≤ w :=
      le_trans (PRASeqDomainBound.bitMajorant_mono u s (le_of_lt hu)) hpos
    have hn : PRANegBitFullWitnessBound.negBitMajorant u ≤ w :=
      le_trans (PRASeqDomainBound.negBitMajorant_mono u s (le_of_lt hu)) hneg
    apply PRAFixSuccWitnessBound.succ_bound_of_core φ u z i w hp hn ?_ ?_ he
    · intro x hx hxcore
      exact hcore u z i x hu hz hi hx hxcore
    · intro x hx hxcore
      exact hcoreneg u z i x hu hz hi hx hxcore
noncomputable def coreSigma (φ : Fixpoint.Blueprint 0) : ArithmeticSemisentence 2 := φ.core.sigma.val
noncomputable def negCorePi (φ : Fixpoint.Blueprint 0) : ArithmeticSemisentence 2 := ∼φ.core.pi.val
noncomputable def boundedCoreSigma (φ : Fixpoint.Blueprint 0) : ArithmeticSemisentence 3 := bnd (coreSigma φ)
noncomputable def boundedNegCorePi (φ : Fixpoint.Blueprint 0) : ArithmeticSemisentence 3 := bnd (negCorePi φ)
noncomputable def cseqCore (φ : Fixpoint.Blueprint 0) : ArithmeticSemisentence 1 := φ.prBlueprint.cseqDef.val
noncomputable def boundedCseq (φ : Fixpoint.Blueprint 0) : ArithmeticSemisentence 2 := bnd (cseqCore φ)
noncomputable def cseqFixpointBody (φ : Fixpoint.Blueprint 0) : ArithmeticSemisentence 2 :=
  “s w. 2*s+1 ≤ w ∧ ((2*(s)+1)+(((2*(s)+1)⁴+1)+((2*(s)+1)²+1)+(2*(2*(s)+1)²+1)+((2*(s)+1)⁴+(2*(s)+1)⁴+2*(2*(s)+1)+1))+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+((2*(s)+1)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((2*(s)+(s)+1)²+1+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)))) ≤ w ∧ (((2*(s)+1)+(((2*(s)+1)⁴+1)+((2*(s)+1)²+1)+(2*(2*(s)+1)²+1)+((2*(s)+1)⁴+(2*(s)+1)⁴+2*(2*(s)+1)+1))+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+((2*(s)+1)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((2*(s)+(s)+1)²+1+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1))))+(((2*(s)+1)+((2*(s))+(s)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1)))+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((2*(s)+(s)+1)²+1+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)))+((2*(s))+(s)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1)))+((2*(2*(s)+1)+1)+(2*(2*(s)+1)²+1)))+((2*(s))+(s)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1)))+((2*(2*(s)+1)+1)+(2*(2*(s)+1)²+1))) ≤ w ∧
    (∀ x <⁺ 2*s+1, ∀ y <⁺ s, ((x+y+1)²+1+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)) ≤ w) ∧ (((2*(s)+1)+(2*(s)²+1))+(s)+1) ≤ w ∧
    (((s⁴+1)+(s²+1)+(2*s²+1)+(s⁴+s⁴+2*s+1))+s+1) ≤ w ∧
    (∀ u < s, ∀ z < s, ∀ i < 2*s, ∀ x < u+(i+1), !((coreSigma φ)) x z → !((boundedCoreSigma φ)) x z w) ∧
    (∀ u < s, ∀ z < s, ∀ i < 2*s, ∀ x < u+(i+1), !((negCorePi φ)) x z → !((boundedNegCorePi φ)) x z w) ∧
    !((cseqCore φ)) s → !((boundedCseq φ)) s w”
theorem cseqFixpointBody_model (φ : Fixpoint.Blueprint 0) (e : Fin 2 → V) : (cseqFixpointBody φ).Eval e Empty.elim := by
  simp [cseqFixpointBody,boundedCoreSigma,boundedNegCorePi,coreSigma,negCorePi,boundedCseq,cseqCore,Semiformula.eval_substs]
  intro hsize hseq hlh hrel hrelneg hpos hcore hcoreneg hcseq
  apply cseq_fixpoint_bound φ (e 0) (e 1) hsize hseq hlh ?_ hrelneg hpos hrelneg ?_ ?_ hcseq
  · intro x y hx hy
    exact hrel x hx y hy
  · intro u z i x hu hz hi hx hh
    exact hcore u hu z hz i hi x hx hh
  · intro u z i x hu hz hi hx hh
    exact hcoreneg u hu z hz i hi x hx (by simpa using hh)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def cseqFixpointSentence (φ : Fixpoint.Blueprint 0) : Sentence language := ∀⁰* Semiformula.lMap embedding (cseqFixpointBody φ)
theorem candidate_proves_cseq_fixpoint_bound (φ : Fixpoint.Blueprint 0) : PRA ⊢ cseqFixpointSentence φ := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact cseqFixpointBody_model φ e
theorem candidate_proves_derivation_cseq_bound {L : Language} [L.Encodable] [L.LORDefinable]
    (T : Theory L) [T.Δ₁] : PRA ⊢ cseqFixpointSentence (Derivation.blueprint T) :=
  candidate_proves_cseq_fixpoint_bound (Derivation.blueprint T)
end DiophantineConsistency.PRACseqFixpointBound
