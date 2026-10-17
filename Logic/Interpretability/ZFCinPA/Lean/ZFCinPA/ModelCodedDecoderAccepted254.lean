import ZFCinPA.ModelCodedDecoderBundle254
import ZFCinPA.ModelCodedDecoderRho4_254
import BusyBeaver.ZFC.ArithmeticHistoryRecurrence254

set_option autoImplicit false
noncomputable section

/-!
Accepted-row transport. The induction ranges over all internal
numeric proof codes, using an actual Sigma1 predicate. It retains rejection as
value zero, and decodes accepted conclusions. It does not identify arbitrary
accepted conclusions with falsity or claim the converse ZF-to-C254 direction.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderAccepted254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderPropositional254
open LeanProofs.ZFCinPA.ModelCodedDecoderGeneralization254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho4_254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254
open LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
open LeanProofs.ZFCinPA.ModelCodedDecoderBundle254
open LeanProofs.ZFCinPA.ModelCodedDecoderFalsity254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticRow254
open ArithmeticHistory254 ArithmeticHistoryRecurrence254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private instance value_delta : 𝚫₁-Function₁[V] ArithmeticHistory254.value :=
  value_defined_delta.to_definable
private instance decode_delta : 𝚫₁-Function₁[V] ModelCodedDecoder254.decode :=
  decode_defined.graph_delta.to_definable

/-- A local row theorem, before selecting any numeric child codes. The MP
hypotheses cover the changed antecedent/major targets exactly. -/
theorem rowKernel_sound (k payload u v : V)
    (hu : u ≠ 0 → Provable (𝗭𝗙 : SetTheory) (decode (u-1)))
    (hv : v ≠ 0 → Provable (𝗭𝗙 : SetTheory) (decode (v-1))) :
    rowKernel k payload u v = 0 ∨
      Provable (𝗭𝗙 : SetTheory) (decode (rowKernel k payload u v-1)) := by
  classical
  by_cases h0 : k = 0
  · by_cases hp : payload = 0
    · right
      simpa [rowKernel,h0,hp] using decodedProvable_zero (V := V) 𝗭𝗙
    · left; simp [rowKernel,h0,hp]
  by_cases h1 : k = 1
  · by_cases hg : MPGate (first payload) u v
    · rcases hg with ⟨x,hxu,m,hmv,heU,heV,heM⟩
      have hu' : Provable (𝗭𝗙 : SetTheory) (decode x) := by
        simpa [heU] using hu (by rw [heU]; simp)
      have hv' : Provable (𝗭𝗙 : SetTheory) (decode (4*cantor x (first payload))) := by
        simpa [heV,heM,wim,tagged] using hv (by rw [heV]; simp)
      have hp := decodedProvable_mp 𝗭𝗙 hv' hu'
      right
      have hg : MPGate (first payload) u v := ⟨x,hxu,m,hmv,heU,heV,heM⟩
      simpa [rowKernel,h0,h1,mpValue,hg] using hp
    · left; simp [rowKernel,h0,h1,mpValue,hg]
  by_cases h2 : k = 2
  · by_cases hz : u = 0
    · left; simp [rowKernel,h0,h1,h2,genValue,hz]
    · right
      simpa [rowKernel,h0,h1,h2,genValue,hz] using
        zf_decodedProvable_gen (first payload) (hu hz)
  by_cases h3 : k = 3
  · right
    simpa [rowKernel,h0,h1,h2,h3] using zf_decoded_rho1_provable (first payload) (second payload)
  by_cases h4 : k = 4
  · right
    simpa [rowKernel,h0,h1,h2,h3,h4] using zf_decoded_rho2_provable (first payload) (first (second payload)) (second (second payload))
  by_cases h5 : k = 5
  · right
    simpa [rowKernel,h0,h1,h2,h3,h4,h5] using decoded_rho3_provable 𝗭𝗙 (first payload) (first (second payload)) (second (second payload))
  by_cases h6 : k = 6
  · right
    simpa [rowKernel,h0,h1,h2,h3,h4,h5,h6] using decoded_rho4_provable 𝗭𝗙 (first payload) (first (second payload)) (second (second payload))
  by_cases h7 : k = 7
  · right
    simpa [rowKernel,h0,h1,h2,h3,h4,h5,h6,h7] using decoded_rho5_provable 𝗭𝗙 (first payload) (first (second payload)) (second (second payload))
  by_cases h8 : k = 8
  · right
    simpa [rowKernel,h0,h1,h2,h3,h4,h5,h6,h7,h8] using zf_decoded_rho6_provable (first payload) (second payload)
  by_cases h9 : k = 9
  · right
    simpa [rowKernel,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] using decoded_rho7_provable 𝗭𝗙 (first payload) (first (second payload)) (second (second payload))
  by_cases h10 : k = 10
  · right
    simpa [rowKernel,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10] using decoded_rho8_provable 𝗭𝗙 (first payload) (first (second payload)) (first (second (second payload))) (second (second (second payload)))
  by_cases h11 : k = 11
  · by_cases hg : second (second payload) ≠ first payload ∧
        second (second payload) ≠ first (second payload)
    · right
      simpa [rowKernel,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,hg] using
        zf_decoded_bundle_provable (first payload) (first (second payload))
          (second (second payload)) hg.1 hg.2
    · left; simp [rowKernel,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,hg]
  · left; simp [rowKernel,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]

/-- One actual Sigma1 invariant; no unbounded universal proof-witness premise. -/
theorem rejected_or_decoded_provable : ∀ code : V,
    value code = 0 ∨ Provable (𝗭𝗙 : SetTheory) (decode (value code-1)) := by
  apply ISigma1.sigma1_order_induction (P := fun code : V =>
    value code = 0 ∨ Provable (𝗭𝗙 : SetTheory) (decode (value code-1)))
  · definability
  · intro code ih
    rcases zero_or_succ code with rfl | ⟨raw,rfl⟩
    · left; simp
    · have child (i : V) (hi : i ≤ raw) (hne : value i ≠ 0) :
          Provable (𝗭𝗙 : SetTheory) (decode (value i-1)) := by
        rcases ih i (lt_of_le_of_lt hi (lt_add_one raw)) with hz | hp
        · exact False.elim (hne hz)
        · exact hp
      rw [value_succ]
      apply rowKernel_sound
      · by_cases htag : raw % 12 = 2
        · simpa only [htag,ite_true] using child (second (raw/12)) (tail_le raw)
        · simpa only [htag,ite_false] using
            child (first (second (raw/12))) (minor_le raw)
      · exact child (second (second (raw/12))) (major_le raw)

theorem accepted_decoded_provable (code : V) (hv : value code ≠ 0) :
    Provable (𝗭𝗙 : SetTheory) (decode (value code-1)) :=
  (rejected_or_decoded_provable code).resolve_left hv

theorem accepted_conclusion_provable (code conclusion : V)
    (hv : value code = conclusion+1) :
    Provable (𝗭𝗙 : SetTheory) (decode conclusion) := by
  have hp := accepted_decoded_provable code (by rw [hv]; simp)
  simpa [hv] using hp

/-- Falsity is a specialization of accepted-conclusion transport, not its
conclusion for every accepted proof. -/
theorem accepted_falsity_provable_bottom (code : V) (hv : value code = 2) :
    Provable (𝗭𝗙 : SetTheory) (^⊥ : V) := by
  apply decoded_one_provable_iff_bottom.mp
  exact accepted_conclusion_provable code 1 (by simpa only [one_add_one_eq_two] using hv)

end LeanProofs.ZFCinPA.ModelCodedDecoderAccepted254
