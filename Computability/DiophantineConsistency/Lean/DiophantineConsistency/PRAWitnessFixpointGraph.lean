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
theorem stage_bound_of_rank {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {ar : ℕ}
    {φ : Fixpoint.Blueprint ar} (c : Fixpoint.Construction V φ)
    (ρ : V → V) [𝚺₁-Function₁ ρ] (hge : ∀ x, x ≤ ρ x) (hr : PRAFixpointRank.RankFinite c ρ)
    (P : V → V) (hP : ∀ x, ρ x + 1 ≤ P x) (v : Fin ar → V) (x s L : V)
    (hL : φ.limSeqDef.val.Evalb (L :> s :> v)) (hx : bitDef.val.Evalb ![x, L]) :
    φ.limSeqDef.val.Evalb (c.limSeq v (P x) :> P x :> v) ∧
      bitDef.val.Evalb ![x, c.limSeq v (P x)] := by
  have hL' : L = c.limSeq v s := by
    simpa using (c.eval_limSeqDef (L :> s :> v)).mp hL
  have hxL : x ∈ L := by simpa [Semiformula.Operator.val, operator_mem_def] using hx
  have hmem : x ∈ c.limSeq v (ρ x + 1) :=
    PRAFixpointRank.mem_limSeq_rank ρ hge hr v x s (hL' ▸ hxL)
  refine ⟨by simpa using (c.eval_limSeqDef (c.limSeq v (P x) :> P x :> v)).mpr (by simp), ?_⟩
  have h := c.limSeq_cumulative (v := v) (hP x) hmem
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

/-- The stage formula `∃ L, limSeq L s ∧ x ∈ L`, in context `s :> x :> params`. -/
noncomputable def stageFormula {ar : ℕ} (φ : Fixpoint.Blueprint ar) : ArithmeticSemisentence (ar + 2) :=
  “s x. ∃ L, !φ.limSeqDef L s ⋯ ∧ x ∈ L”

theorem fixpointDef_eq {ar : ℕ} (φ : Fixpoint.Blueprint ar) :
    φ.fixpointDef.val = ∃⁰ stageFormula φ := by
  simp [Fixpoint.Blueprint.fixpointDef, stageFormula]

/-- **Witness bounds for `fixpointDef`.** The stage bound `P` may depend on
the element `e 0` and on the parameters `e i.succ`. -/
theorem wb_fixpointDef {ar : ℕ} (φ : Fixpoint.Blueprint ar)
    (hσ : WB M φ.core.sigma.val) (hπ : WB M (∼φ.core.pi.val)) (P : ArithmeticSemiterm Empty (ar + 1))
    (hI : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin (ar + 1) → V) (s L : V),
      φ.limSeqDef.val.Evalb (L :> s :> fun i => e i.succ) → bitDef.val.Evalb ![e 0, L] →
        ∃ L', φ.limSeqDef.val.Evalb (L' :> P.val e Empty.elim :> fun i => e i.succ) ∧
          bitDef.val.Evalb ![e 0, L']) :
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
    have hlim : φ.limSeqDef.val.Evalb (L :> e 0 :> fun i => e i.succ.succ) := by
      have h := hL
      simp [Semiformula.Operator.val, Matrix.comp_vecCons'', PRAHistoryTruncation.val_comp_bvar] at h
      exact h.1
    exact ⟨L, le_of_lt (show L < PRAHistoryTruncation.histBound (e 0) from
      PRAHistoryTruncation.limSeq_value_lt φ _ hlim), hL⟩
  rw [fixpointDef_eq]
  refine PRAWitnessTransfer.wb_exs_poly (stageFormula φ) hs P ?_ hWBs
  intro V _ _ e s h
  obtain ⟨L, hL, hx⟩ : ∃ L, φ.limSeqDef.val.Evalb (L :> s :> fun i => e i.succ) ∧
      bitDef.val.Evalb ![e 0, L] := by
    simpa [stageFormula, Semiformula.Operator.val, operator_mem_def, Matrix.comp_vecCons'',
      PRAHistoryTruncation.val_comp_bvar] using h
  obtain ⟨L', hL', hx'⟩ := hI V e s L hL hx
  refine ⟨P.val e Empty.elim, le_rfl, ?_⟩
  have hx'' : e 0 ∈ L' := by simpa [Semiformula.Operator.val, operator_mem_def] using hx'
  simpa [stageFormula, Semiformula.Operator.val, operator_mem_def, Matrix.comp_vecCons'',
    PRAHistoryTruncation.val_comp_bvar] using ⟨L', hL', hx''⟩

end models
end DiophantineConsistency.PRAWitnessFixpointGraph
