import DiophantineConsistency.PRAWitnessSetTerms
import DiophantineConsistency.PRAWitnessRepeatVec
/-! # Witness bounds for term recursions over `ℒₛₑₜ`

A `Language.TermRec.Blueprint` core has a function branch whose witness `rv`
is `repeatVec C k`, the argument set repeated `k` times. Its bound is
doubly exponential (`PRAWitnessRepeatVec.repeatVec_lt`); vector entries are
bounded by the vector (`nth_le`, `len_le`). Given witness bounds for the
blueprint's three clauses, both polarities of the core are witness bounded. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessTermRec
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessVectors PRAWitnessSetTerms
  PRAWitnessRepeatVec PRAWitnessExpBounds

section models
open PRAFiniteFunctionCodes PRALanguage PRATheory
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- **The negated `Π` graph of a `𝚺₁` function has bounded witnesses** once
the function's value is polynomially bounded in `𝗜𝚺₁`: it is
`∃ y', φ y' ⋯ ∧ y' ≠ y`, and `y'` is the value. -/
theorem wb_neg_graphDelta_pi {k : ℕ} (φ : 𝚺₁.Semisentence (k + 1)) (hφ : WB M φ.val)
    (P : ArithmeticSemiterm Empty k)
    (hI : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin k → V) (y : V),
      φ.val.Evalb (y :> e) → y ≤ P.val e Empty.elim) :
    WB M (∼φ.graphDelta.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  simp only [HierarchySymbol.Semiformula.graphDelta, HierarchySymbol.Semiformula.pi_mkDelta,
    HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) (Rew.bShift P)
    (fun V _ _ e x h => ⟨x, ?_, h⟩) (by wb_auto)
  have h' := h
  simp [Matrix.comp_vecCons'', PRAHistoryTruncation.val_comp_bvar] at h'
  simpa [Semiterm.val_bShift', Function.comp_def] using hI V (fun i => e i.succ) x h'.1

variable {ar : ℕ} (β : Language.TermRec.Blueprint ar)

theorem wb_core_sigma (h1 : WB M β.bvar.val) (h2 : WB M β.fvar.val) (h3 : WB M β.func.val) :
    WB M (β.blueprint ℒₛₑₜ).core.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqBvarDef (M := M); have := wb_qqFvarDef (M := M); have := wb_pairDef (M := M)
  have := wb_isUTerm_sigma (M := M); have := wb_qqFuncDef (M := M); have := wb_lenDef (M := M)
  have := wb_nthDef (M := M); have := wb_repeatVecDef (M := M); have := wb_memRel (M := M)
  have : WB M memRelOpr.sentence := wb_memRel (M := M)
  simp only [Language.TermRec.Blueprint.blueprint, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  refine PRAWitnessTransfer.wb_exs_bound _ (by simp)
    (expGraph2 ‘#6 + 2’ ‘2 * #2’) (expBound2 ‘#6 + 2’ ‘2 * #2’)
    (dominates_expBound2 _ _) (mono_expBound2 _ _) ?_ ?_
  · intro V _ _ e x h
    have h' := h; simp at h'
    refine ⟨Exp.exp ((e 6 + 2) * Exp.exp (2 * e 2)), ?_, x, ?_, h⟩
    · rw [eval_expGraph2]
      exact ⟨Exp.exp (2 * e 2), by simpa using exponential_exp (2 * e 2),
        by simpa using exponential_exp ((e 6 + 2) * Exp.exp (2 * e 2))⟩
    · rw [h'.1]; exact le_of_lt (repeatVec_lt _ _)
  · wb_auto
    exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#3’
      (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩)
      (by
        wb_auto
        exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#2’
          (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩) (by wb_auto))

theorem wb_core_neg_pi (h1 : WB M (∼β.bvar.graphDelta.pi.val))
    (h2 : WB M (∼β.fvar.graphDelta.pi.val)) (h3 : WB M (∼β.func.graphDelta.pi.val)) :
    WB M (∼(β.blueprint ℒₛₑₜ).core.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_neg_qqBvarDef (M := M); have := wb_neg_qqFvarDef (M := M); have := wb_neg_pairDef (M := M)
  have := wb_isUTerm_neg_pi (M := M); have := wb_neg_qqFuncDef (M := M); have := wb_lenDef (M := M)
  have := wb_nthDef (M := M); have := wb_neg_memRel (M := M); have := wb_repeatVecDef (M := M)
  have : WB M (∼memRelOpr.sentence) := wb_neg_memRel (M := M)
  simp only [Language.TermRec.Blueprint.blueprint, HierarchySymbol.Semiformula.pi_mkDelta,
    HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  refine PRAWitnessTransfer.wb_exs_bound _ (by simp)
    (expGraph2 ‘#6 + 2’ ‘2 * #2’) (expBound2 ‘#6 + 2’ ‘2 * #2’)
    (dominates_expBound2 _ _) (mono_expBound2 _ _) ?_ ?_
  · intro V _ _ e x h
    have h' := h; simp at h'
    refine ⟨Exp.exp ((e 6 + 2) * Exp.exp (2 * e 2)), ?_, x, ?_, h⟩
    · rw [eval_expGraph2]
      exact ⟨Exp.exp (2 * e 2), by simpa using exponential_exp (2 * e 2),
        by simpa using exponential_exp ((e 6 + 2) * Exp.exp (2 * e 2))⟩
    · rw [h'.1]; exact le_of_lt (repeatVec_lt _ _)
  · wb_auto
    · exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’
        (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩) (by wb_auto)
    · exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#3’
        (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩)
        (by
          wb_auto
          exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#2’
            (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩) (by wb_auto))

/-- A construction of the blueprint in every `𝗜𝚺₁` model. -/
abbrev Constructions := ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], Language.TermRec.Construction V β

/-- Witness bounds for the six clause formulas of a blueprint. -/
structure ClauseBounds (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA] : Prop where
  bvar : WB M β.bvar.val
  fvar : WB M β.fvar.val
  func : WB M β.func.val
  bvar_pi : WB M (∼β.bvar.graphDelta.pi.val)
  fvar_pi : WB M (∼β.fvar.graphDelta.pi.val)
  func_pi : WB M (∼β.func.graphDelta.pi.val)

variable {β}

theorem wb_fixpoint (c : Constructions β) (hβ : ClauseBounds β M) :
    WB M (β.blueprint ℒₛₑₜ).fixpointDef.val := by
  refine PRAWitnessFixpointGraph.wb_fixpointDef _ (wb_core_sigma β hβ.bvar hβ.fvar hβ.func)
    (wb_core_neg_pi β hβ.bvar_pi hβ.fvar_pi hβ.func_pi) ‘#0 + 1’ ?_
  intro V _ _ e s L hL hx
  have h := PRAWitnessFixpointGraph.stage_bound_of_rank ((c V).construction ℒₛₑₜ) (fun x => x)
    (fun _ => le_rfl) (termRec_set_rankFinite (c V)) (fun x => x + 1) (fun _ => le_rfl)
    (fun i => e i.succ) (e 0) s L hL hx
  exact ⟨_, by simpa using h.1, h.2⟩

theorem wb_graph (c : Constructions β) (hβ : ClauseBounds β M) : WB M (β.graph ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_fixpoint c hβ; have := wb_pairDef (M := M)
  simp only [Language.TermRec.Blueprint.graph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_result (c : Constructions β) (hβ : ClauseBounds β M) : WB M (β.result ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_graph c hβ; have := wb_isUTerm_sigma (M := M); have := wb_isUTerm_neg_pi (M := M)
  simp only [Language.TermRec.Blueprint.result, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_resultVec (c : Constructions β) (hβ : ClauseBounds β M) :
    WB M (β.resultVec ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_graph c hβ; have := wb_isUTermVec_sigma (M := M); have := wb_isUTermVec_neg_pi (M := M)
  have := wb_lenDef (M := M); have := wb_nthDef (M := M)
  simp only [Language.TermRec.Blueprint.resultVec, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#3’
    (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩)
    (by
      wb_auto
      exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#2’
        (fun V _ _ e u h => ⟨u, by have h' := h; simp at h'; simp [h'.1], h⟩) (by wb_auto))

end models
end DiophantineConsistency.PRAWitnessTermRec
