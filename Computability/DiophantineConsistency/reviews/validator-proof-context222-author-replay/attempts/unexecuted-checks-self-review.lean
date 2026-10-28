import ZFCinPA.ValidatorProofContext222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace LeanProofs.ZFCinPA.ValidatorProofContext222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorFormulaEncoder222
open ValidatorProofContext222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- This is an actual numeric C222 proof, even for an internally sized list. -/
theorem internal_hypothesis (G i : V) (hi : i < len G) :
    ∃ d : V, ArithmeticHistory222.value d = imps G G.[i] + 1 :=
  (der_iff_history _ _).mp (der_hyp G i hi)

theorem empty_is_theorem (g : V) : Der (0 : V) g ↔ CProv g := der_nil g

theorem duplicate_contraction {G a g : V} (h : Der (a ∷ a ∷ G) g) :
    Der (a ∷ G) g := by
  apply der_sub (h := h)
  intro x hx
  simpa only [memVec_adjoin_iff, or_self_left] using hx

theorem exchange {G a b g : V} (h : Der (a ∷ b ∷ G) g) :
    Der (b ∷ a ∷ G) g := by
  apply der_sub (h := h)
  intro x hx
  simpa only [memVec_adjoin_iff, or_left_comm] using hx

theorem deduction_roundtrip (G a g : V) :
    Der (a ∷ G) g ↔ Der G (wim a g) := ⟨der_ded, der_undeduct⟩

theorem internal_cut {G a g : V} (ha : Der G a) (hg : Der (a ∷ G) g) :
    Der G g := der_mp (der_ded hg) ha

theorem closes_contradiction {G a : V} (ha : Der G a) (hna : neg a ∈ᵥ G) :
    ∃ d : V, ArithmeticHistory222.value d = seqC (0 : V) 0 0 + imps G 1 := by
  have hd := (der_iff_history _ _).mp (der_absurd hna ha)
  simpa [seqC, add_comm] using hd

theorem actual_negated_lookup (F s L i : V) (hi : i < len L) :
    (negEnc F s L).[i] = wim (encode F 0 s L.[i]) 1 :=
  (negEnc_len_nth F s L).2 i hi

theorem nested_source_shift (F s p : V) (hp : IsUFormula ℒₛₑₜ p) :
    negEnc F s (shiftList ?[^∀ (^∃ p)]) =
      negEnc (ValidatorEnvironmentLabels254.tail F) s ?[^∀ (^∃ p)] := by
  apply negEnc_shiftList
  intro q hq
  have hq' : q = ^∀ (^∃ p) := by simpa using hq
  subst q
  exact hp.exs.all

theorem empty_sequent (F s : V) : seqC F s (0 : V) = 1 := by simp [seqC]

theorem false_sequent (F s : V) : CProv (seqC F s ?[(^⊥ : V)]) := by
  simp only [seqC, negEnc_cons, encode_falsum, negEnc_nil, imps_cons, imps_nil]
  exact cProv_mp (double_neg_elim (1 : V)) (double_neg_intro (1 : V))

theorem enumeration_independence (F s S : V) :
    ∃ L : V, Enum L S ∧ ∀ K : V, Enum K S →
      (CProv (seqC F s L) ↔ CProv (seqC F s K)) := by
  obtain ⟨L, hL⟩ := exists_enum S
  exact ⟨L, hL, fun K hK => seqC_enum_iff F s hL hK⟩

#print axioms imps_defined
#print axioms der_defined
#print axioms cProv_imps_mp
#print axioms der_sub
#print axioms der_byContra
#print axioms negEnc_defined
#print axioms seqC_defined
#print axioms shiftList_defined
#print axioms negEnc_shiftList
#print axioms enum_defined
#print axioms exists_enum
#print axioms seqC_enum_iff
#print axioms internal_hypothesis
#print axioms duplicate_contraction
#print axioms nested_source_shift
#print axioms enumeration_independence

end LeanProofs.ZFCinPA.ValidatorProofContext222Checks
