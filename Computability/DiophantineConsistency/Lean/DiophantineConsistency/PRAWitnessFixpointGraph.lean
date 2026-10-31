import DiophantineConsistency.PRAWitnessTransfer
import DiophantineConsistency.PRAHistoryTruncation
import DiophantineConsistency.PRAFixpointRank
/-! # Witness bounds for fixpoints with an unbounded stage

Recursion graphs (vector, term and formula recursions) are defined by
Foundation's `fixpointDef`, `“x. ∃ s L, !limSeqDef L s ⋯ ∧ x ∈ L”`, whose stage
`s` is an unbounded witness. `wb_fixpointDef` bounds all of its witnesses in
every candidate-PRA model from two inputs:

* witness bounds for the blueprint's core (both polarities), which give the
  history and the stage value through `PRAHistoryTruncation`;
* an `𝗜𝚺₁` stage bound: every element of some stage is in the stage `P x`,
  for an `ℒₒᵣ` polynomial `P`. It moves to candidate PRA by
  `PRAWitnessTransfer.wb_exs_poly`.

`stage_bound_of_rank` derives the `𝗜𝚺₁` input from a decreasing rank
(`PRAFixpointRank.RankFinite`) dominated by `P`, using cumulativity. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessFixpointGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus PRAWitnessArithmetic

/-- **An `𝗜𝚺₁` stage bound from a decreasing rank.** -/
theorem stage_bound_of_rank {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {φ : Fixpoint.Blueprint 0} (c : Fixpoint.Construction V φ)
    (ρ : V → V) [𝚺₁-Function₁ ρ] (hge : ∀ x, x ≤ ρ x) (hr : PRAFixpointRank.RankFinite c ρ)
    (P : V → V) (hP : ∀ x, ρ x + 1 ≤ P x) (x s L : V)
    (hL : φ.limSeqDef.val.Evalb ![L, s]) (hx : bitDef.val.Evalb ![x, L]) :
    φ.limSeqDef.val.Evalb ![c.limSeq ![] (P x), P x] ∧
      bitDef.val.Evalb ![x, c.limSeq ![] (P x)] := by
  have hL' : L = c.limSeq ![] s := by
    simpa [Matrix.empty_eq] using (c.eval_limSeqDef ![L, s]).mp hL
  have hxL : x ∈ L := by simpa [Semiformula.Operator.val, operator_mem_def] using hx
  have hmem : x ∈ c.limSeq ![] (ρ x + 1) := by
    have h := PRAFixpointRank.mem_limSeq_rank ρ hge hr ![] x s (hL' ▸ hxL)
    exact h
  refine ⟨by simpa [Matrix.empty_eq] using (c.eval_limSeqDef ![c.limSeq ![] (P x), P x]).mpr rfl, ?_⟩
  have h := c.limSeq_cumulative (v := ![]) (hP x) hmem
  simpa [Semiformula.Operator.val, operator_mem_def] using h

section models
open PRAFiniteFunctionCodes PRALanguage PRATheory
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- The stage formula `∃ L, limSeq L s ∧ x ∈ L`, in context `s :> x`. -/
noncomputable def stageFormula (φ : Fixpoint.Blueprint 0) : ArithmeticSemisentence 2 :=
  “s x. ∃ L, !φ.limSeqDef L s ∧ x ∈ L”

theorem fixpointDef_eq (φ : Fixpoint.Blueprint 0) :
    φ.fixpointDef.val = ∃⁰ stageFormula φ := by
  simp [Fixpoint.Blueprint.fixpointDef, stageFormula]

/-- **Witness bounds for `fixpointDef`.** -/
theorem wb_fixpointDef (φ : Fixpoint.Blueprint 0)
    (hσ : WB M φ.core.sigma.val) (hπ : WB M (∼φ.core.pi.val)) (P : ArithmeticSemiterm Empty 1)
    (hI : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (x s L : V),
      φ.limSeqDef.val.Evalb ![L, s] → bitDef.val.Evalb ![x, L] →
        ∃ L', φ.limSeqDef.val.Evalb ![L', P.val ![x] Empty.elim] ∧ bitDef.val.Evalb ![x, L']) :
    WB M φ.fixpointDef.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hl := PRAHistoryTruncation.wb_limSeqDef φ hσ hπ
  have hbit := wb_bitDef (M := M)
  have hs : Hierarchy 𝚺 1 (stageFormula φ) := by
    simp [stageFormula, φ.limSeqDef.sigma_prop]
  have hWBs : WB M (stageFormula φ) := by
    simp only [stageFormula]
    refine wb_exs (fun e => PRAHistoryTruncation.histBound (e 0))
      (fun e e' h => PRAHistoryTruncation.histBound_mono (h 0)) ?_ (by wb_auto)
    rintro e ⟨L, hL⟩
    obtain ⟨s, x, rfl⟩ : ∃ s x : M, e = ![s, x] := ⟨e 0, e 1, Matrix.fun_eq_vec_two e⟩
    have hlim : φ.limSeqDef.val.Evalb ![L, s] := by
      have h := hL
      simp [Semiformula.Operator.val] at h
      exact h.1
    exact ⟨L, le_of_lt (show L < PRAHistoryTruncation.histBound s from
      PRAHistoryTruncation.limSeq_value_lt φ hlim), hL⟩
  rw [fixpointDef_eq]
  refine PRAWitnessTransfer.wb_exs_poly (stageFormula φ) hs P ?_ hWBs
  intro V _ _ e s h
  obtain ⟨x, rfl⟩ : ∃ x : V, e = ![x] := ⟨e 0, Matrix.fun_eq_vec_one e⟩
  obtain ⟨L, hL, hx⟩ : ∃ L, φ.limSeqDef.val.Evalb ![L, s] ∧ bitDef.val.Evalb ![x, L] := by
    simpa [stageFormula, Semiformula.Operator.val, operator_mem_def] using h
  obtain ⟨L', hL', hx'⟩ := hI V x s L hL hx
  refine ⟨P.val ![x] Empty.elim, le_rfl, ?_⟩
  have hx'' : x ∈ L' := by simpa [Semiformula.Operator.val, operator_mem_def] using hx'
  simpa [stageFormula, Semiformula.Operator.val, operator_mem_def] using ⟨L', hL', hx''⟩

end models
end DiophantineConsistency.PRAWitnessFixpointGraph
