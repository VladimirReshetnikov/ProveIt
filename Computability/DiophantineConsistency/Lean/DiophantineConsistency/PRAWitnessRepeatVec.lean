import DiophantineConsistency.PRAWitnessExpBounds
import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Basic
/-! # Witness bounds for `repeatVec`

`repeatVec x k = x ∷ x ∷ ⋯ ∷ 0` (`k` copies) is a primitive recursion. Its
result formula has a computation history as an unbounded witness, and term
recursions query its value. In `𝗜𝚺₁`:

* `repeatVec_mono`: the values increase with `k`, so a canonical history of
  length `u + 1` has entries at most `repeatVec x u` and, by Foundation's
  `seq_bound`, is below `2^((u + z + 2)²)` for the result `z`;
* `repeatVec_lt`: `repeatVec x k < 2^((x + 5) · 4^k)`, since a cons step
  `⟪x, r⟫ + 1 ≤ 4B²` stays below `B⁴` once `B ≥ 4`.

`PRAWitnessTransfer.wb_exs_bound` moves both to candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessRepeatVec
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

section sigma1
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem repeatVec_lt_succ (x k : V) : repeatVec x k < repeatVec x (k + 1) := by
  simp

theorem repeatVec_mono (x : V) : ∀ u i, i ≤ u → repeatVec x i ≤ repeatVec x u := by
  intro u
  induction u using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro i hi; simp [nonpos_iff_eq_zero.mp hi]
  case succ u ih =>
    intro i hi
    rcases lt_or_eq_of_le hi with h | rfl
    · exact le_trans (ih i (lt_succ_iff_le.mp h)) (le_of_lt (repeatVec_lt_succ x u))
    · exact le_rfl

theorem exp_two_eq : Exp.exp (2 : V) = 2 * 2 := by
  rw [← one_add_one_eq_two, exp_succ, ← zero_add (1 : V), exp_succ]
  simp [one_add_one_eq_two]

theorem exp_four (c : V) : Exp.exp (c * (2 * 2)) = Exp.exp c * Exp.exp c * (Exp.exp c * Exp.exp c) := by
  rw [show c * (2 * 2) = (c + c) + (c + c) by rw [← two_mul, ← two_mul, mul_comm c, ← mul_assoc]]
  simp [exp_add]

/-- **`repeatVec` grows at most doubly exponentially.** -/
theorem repeatVec_lt (x k : V) : repeatVec x k < Exp.exp ((x + 2) * Exp.exp (2 * k)) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    set c := (x + 2) * Exp.exp (2 * k) with hc
    set B := Exp.exp c with hB
    have hc2 : (2 : V) ≤ c :=
      le_trans (le_add_self) (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (exp_pos _)))
    have hB2 : (2 : V) < B := by
      have h4 : Exp.exp (2 : V) ≤ B := exp_monotone_le.mpr hc2
      rw [exp_two_eq] at h4
      exact lt_of_lt_of_le (by simp [two_mul]) h4
    have hxB : x < B := lt_of_le_of_lt (le_trans le_self_add (le_mul_of_one_le_right (by simp)
      (pos_iff_one_le.mp (exp_pos _)))) (lt_exp c)
    have hrB : repeatVec x k + 1 ≤ B := lt_iff_succ_le.mp ih
    have hsum : x + repeatVec x k + 1 < B + B := by
      rw [add_assoc]; exact add_lt_add_of_lt_of_le hxB hrB
    have hpair : ⟪x, repeatVec x k⟫ + 1 ≤ (B + B) * (B + B) := by
      have h1 : ⟪x, repeatVec x k⟫ ≤ (x + repeatVec x k + 1) * (x + repeatVec x k + 1) := by
        simpa [sq] using pair_polybound x (repeatVec x k)
      have h2 : (x + repeatVec x k + 1) * (x + repeatVec x k + 1) < (B + B) * (B + B) :=
        mul_lt_mul'' hsum hsum (by simp) (by simp)
      exact lt_iff_succ_le.mp (lt_of_le_of_lt h1 h2)
    have hB4 : (B + B) * (B + B) < B * B * (B * B) := by
      have hsq : (2 : V) * 2 < B * B := mul_lt_mul'' hB2 hB2 (by simp) (by simp)
      have hBB : 0 < B * B := mul_pos (exp_pos c) (exp_pos c)
      calc (B + B) * (B + B) = (2 * 2) * (B * B) := by
            rw [← two_mul, mul_mul_mul_comm]
        _ < (B * B) * (B * B) := mul_lt_mul_of_pos_right hsq hBB
    have hexp : Exp.exp ((x + 2) * Exp.exp (2 * (k + 1))) = B * B * (B * B) := by
      rw [mul_add, mul_one, exp_add, exp_two_eq, ← mul_assoc, exp_four]
    rw [hexp, show repeatVec x (k + 1) = ⟪x, repeatVec x k⟫ + 1 by simp [adjoin_def]]
    exact lt_of_le_of_lt hpair hB4

/-- **A canonical history of `repeatVec`, bounded by its result.** -/
theorem history_canonical (x u z s : V)
    (hs : repeatVec.adjointruction.CSeq (fun _ : Fin 1 => x) s) (huz : ⟪u, z⟫ ∈ s) :
    ∃ s', repeatVec.adjointruction.CSeq (fun _ : Fin 1 => x) s' ∧ ⟪u, z⟫ ∈ s' ∧
      s' < Exp.exp ((u + 1 + (z + 1) + 1) * (u + 1 + (z + 1) + 1)) := by
  have hv : (![x] : Fin 1 → V) = fun _ => x := funext fun i => Fin.cases rfl (fun j => Fin.elim0 j) i
  have hz : z = repeatVec.adjointruction.result (fun _ : Fin 1 => x) u :=
    (repeatVec.adjointruction.result_graph (fun _ : Fin 1 => x) z u).mpr ⟨s, hs, huz⟩
  obtain ⟨s', hs', hl, hu⟩ := repeatVec.adjointruction.result_spec (fun _ : Fin 1 => x) u
  refine ⟨s', hs', hz ▸ hu, ?_⟩
  have hent : ∀ i w, ⟪i, w⟫ ∈ s' → w < z + 1 := by
    intro i w hw
    have hi : i < lh s' := Seq.lt_lh_of_mem hs'.seq hw
    have hw' : w = repeatVec.adjointruction.result (fun _ : Fin 1 => x) i :=
      (repeatVec.adjointruction.result_graph (fun _ : Fin 1 => x) w i).mpr ⟨s', hs', hw⟩
    have hiu : i ≤ u := lt_succ_iff_le.mp (hl ▸ hi)
    have hle : w ≤ z := by
      rw [hw', hz]
      have := repeatVec_mono x u i hiu
      simpa [repeatVec, hv] using this
    exact lt_succ_iff_le.mpr hle
  have hb := Language.TermRec.Construction.seq_bound hs'.seq hl hent
  simpa [sq] using hb

end sigma1

section models
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
  PRAWitnessExpBounds
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- The history bound `2^((u + 1 + (z + 1) + 1)²)`, context `z :> u :> x`. -/
noncomputable def historyPoly : ArithmeticSemiterm Empty 3 :=
  ‘(#1 + 1 + (#0 + 1) + 1) * (#1 + 1 + (#0 + 1) + 1)’

theorem wb_repeatVec_cseq : WB M repeatVec.blueprint.cseqDef.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_seqDef (M := M); have := wb_lhDef (M := M); have := wb_adjoinDef (M := M)
  have := wb_memRel (M := M); have := wb_neg_lhDef (M := M); have := wb_neg_memRel (M := M)
  have : WB M memRelOpr.sentence := wb_memRel (M := M)
  have : WB M (∼memRelOpr.sentence) := wb_neg_memRel (M := M)
  simp only [PR.Blueprint.cseqDef, repeatVec.blueprint, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_repeatVec_result : WB M repeatVec.blueprint.resultDef.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_repeatVec_cseq (M := M)
  have : WB M memRelOpr.sentence := wb_memRel (M := M)
  simp only [PR.Blueprint.resultDef, HierarchySymbol.Semiformula.val_mkSigma]
  refine PRAWitnessTransfer.wb_exs_bound _ (by simp) (expGraph historyPoly) (expBound historyPoly)
    (dominates_expBound historyPoly) (mono_expBound historyPoly) ?_ (by wb_auto)
  intro V _ _ e s h
  have he : e = ![e 0, e 1, e 2] := by
    funext j; revert j; simp [Fin.forall_fin_succ]
  rw [he] at h ⊢
  have h' : repeatVec.adjointruction.CSeq (fun _ : Fin 1 => e 2) s ∧ ⟪e 1, e 0⟫ ∈ s := by
    simpa [Semiformula.Operator.val, memRelOpr, repeatVec.adjointruction.cseq_defined.iff] using h
  obtain ⟨s', hs', hu', hlt⟩ := history_canonical (e 2) (e 1) (e 0) s h'.1 h'.2
  refine ⟨Exp.exp ((e 1 + 1 + (e 0 + 1) + 1) * (e 1 + 1 + (e 0 + 1) + 1)), ?_, s', le_of_lt hlt, ?_⟩
  · rw [eval_expGraph]
    simpa [historyPoly] using exponential_exp ((e 1 + 1 + (e 0 + 1) + 1) * (e 1 + 1 + (e 0 + 1) + 1))
  · simpa [Semiformula.Operator.val, memRelOpr, repeatVec.adjointruction.cseq_defined.iff] using And.intro hs' hu'

theorem wb_repeatVecDef : WB M repeatVecDef.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  simp only [repeatVecDef, HierarchySymbol.Semiformula.val_rew]
  exact wb_rew _ wb_repeatVec_result

end models

end DiophantineConsistency.PRAWitnessRepeatVec
