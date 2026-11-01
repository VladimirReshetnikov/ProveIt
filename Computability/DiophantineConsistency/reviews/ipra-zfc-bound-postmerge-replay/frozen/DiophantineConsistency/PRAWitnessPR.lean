import DiophantineConsistency.PRAWitnessBoundTerms
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
/-! # Witness bounds for primitive recursions

`PR.Blueprint.resultDef` is `∃ s, cseqDef s ⋯ ∧ ⟪u, z⟫ ∈ s`, with an unbounded
computation history `s`. If the values `result v i`, `i ≤ u`, are below a
bound term `H`, the canonical history of length `u + 1` is below
`2^((u + H + 3)²)` (`history_bound`, through Foundation's `seq_bound`), so
`wb_resultDef` bounds the history, given witness bounds for the zero and
successor clauses. This covers `qqAlls` (iterated universal quantifiers) and
`fvarVec` (the vector of the first free variables), which the separation and
replacement recognizers use. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessPR
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessVectors
  PRAWitnessTermFunctions PRAWitnessCodeGrowth PRAWitnessBoundTerms PRAWitnessBoundTerms.BoundTerm
  PRAWitnessRepeatVec

section sigma1
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **A computation history bounded by the values.** -/
theorem history_bound {k : ℕ} {p : PR.Blueprint k} (c : PR.Construction V p) (v : Fin k → V)
    {u z s F : V} (hs : c.CSeq v s) (huz : ⟪u, z⟫ ∈ s) (hF : ∀ i ≤ u, c.result v i ≤ F) :
    ∃ s', c.CSeq v s' ∧ ⟪u, z⟫ ∈ s' ∧
      s' < Exp.exp ((u + 1 + (F + 1) + 1) * (u + 1 + (F + 1) + 1)) := by
  have hz : z = c.result v u := (c.result_graph v z u).mpr ⟨s, hs, huz⟩
  obtain ⟨s', hs', hl, hu⟩ := c.result_spec v u
  refine ⟨s', hs', hz ▸ hu, ?_⟩
  have hent : ∀ i w, ⟪i, w⟫ ∈ s' → w < F + 1 := by
    intro i w hw
    have hi : i < lh s' := Seq.lt_lh_of_mem hs'.seq hw
    have hw' : w = c.result v i := (c.result_graph v w i).mpr ⟨s', hs', hw⟩
    have hiu : i ≤ u := lt_succ_iff_le.mp (hl ▸ hi)
    exact lt_succ_iff_le.mpr (hw' ▸ hF i hiu)
  have hb := Language.TermRec.Construction.seq_bound hs'.seq hl hent
  simpa [sq] using hb

/-- `PRAWitnessVectors.vecRec_rankFinite`, for any arity. -/
theorem vecRec_rankFinite' {ar : ℕ} {β : VecRec.Blueprint ar} (c : VecRec.Construction V β)
    (hadj : ∀ v x xs ih, ih ≤ c.adjoin v x xs ih) :
    PRAFixpointRank.RankFinite c.adjointruction (fun x => x) := by
  rintro v C pr (h | ⟨x, xs, ih, rfl, hC⟩)
  · exact Or.inl h
  · exact Or.inr ⟨x, xs, ih, rfl, hC,
      lt_of_le_of_lt (pair_le_pair_right xs (hadj v x xs ih)) (pair_lt_pair_left (lt_adjoin' x xs) _)⟩

theorem small_le_tau (X D : V) {n : ℕ} (hn : n ≤ 16) : (n : V) ≤ tau X D := by
  have h16 : (16 : V) ≤ tau X D := by
    have h4 : (4 : V) ≤ (X + 4) * Exp.exp D := le_trans le_add_self (le_tauE X D)
    have he : Exp.exp (4 : V) = 16 := by
      rw [show (4 : V) = 2 + 2 by norm_num, exp_add, exp_two_eq]; norm_num
    exact he ▸ exp_monotone_le.mpr h4
  exact le_trans (by exact_mod_cast hn) h16

/-- `qqAlls p k` is `k` pairings above `p`. -/
theorem qqAlls_le (p : V) : ∀ k, qqAlls p k ≤ tau p (2 * k) := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using le_tau p 0
  case succ k ih =>
    rw [qqAlls_succ, show 2 * (k + 1) = 2 * k + 2 by ring]
    simpa [qqAll] using code2_le_tau (by exact_mod_cast small_le_tau p (2 * k) (n := 6) (by norm_num)) ih

theorem fvarVec_le (u : V) : ∀ i ≤ u, fvarVec i ≤ tau ((u + 2) * (u + 2) + 1) (2 * u) := by
  intro i hi
  have he : ∀ j < len (fvarVec i), (fvarVec i).[j] ≤ (u + 2) * (u + 2) + 1 := by
    intro j hj
    rw [len_fvarVec] at hj
    rw [nth_fvarVec i j hj]
    have h2 : 1 + j + 1 ≤ u + 2 := by
      calc 1 + j + 1 = j + 2 := by ring
        _ ≤ u + 2 := add_le_add (le_trans (le_of_lt hj) hi) le_rfl
    exact le_trans (qqFvar_le j) (add_le_add (mul_le_mul' h2 h2) le_rfl)
  have h := len_repeatVec_of_nth_le (v := fvarVec i) he
  rw [len_fvarVec] at h
  exact le_trans h (le_trans (PRAWitnessRepeatVec.repeatVec_mono _ _ _ hi)
    (by simpa using repeatVec_le_tau (le_tau ((u + 2) * (u + 2) + 1) 0) u))

end sigma1

section models
open PRAFiniteFunctionCodes PRALanguage PRATheory
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- `wb_exs_bt`, allowing a smaller witness. -/
theorem wb_exs_bt' {n : ℕ} (ψ : ArithmeticSemisentence (n + 1)) (hψ : Hierarchy 𝚺 1 ψ)
    (A : BoundTerm n)
    (hI : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) (x : V),
      ψ.Eval (x :> e) Empty.elim → ∃ x' ≤ A.vval e, ψ.Eval (x' :> e) Empty.elim)
    (hWB : WB M ψ) : WB M (∃⁰ ψ) :=
  PRAWitnessTransfer.wb_exs_bound ψ hψ A.graph A.term (dominates_term A) (mono_term A)
    (fun V _ _ e x h => ⟨A.vval e, (eval_graph A _ e).mpr rfl, hI V e x h⟩) hWB

theorem wb_cseq {k : ℕ} (p : PR.Blueprint k) (hz : WB M p.zero.val) (hs : WB M p.succ.val) :
    WB M p.cseqDef.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_seqDef (M := M); have := wb_lhDef (M := M); have := wb_adjoinDef (M := M)
  have := wb_memRel (M := M); have := wb_neg_lhDef (M := M); have := wb_neg_memRel (M := M)
  have : WB M memRelOpr.sentence := wb_memRel (M := M)
  have : WB M (∼memRelOpr.sentence) := wb_neg_memRel (M := M)
  simp only [PR.Blueprint.cseqDef, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

/-- The history bound term `2^((u + 1 + (H + 1) + 1)²)`, context `z :> u :> v`. -/
noncomputable def histT {k : ℕ} (H : BoundTerm (k + 2)) : BoundTerm (k + 2) :=
  let S := add (add (add (poly ‘#1’) (poly ‘1’)) (add H (poly ‘1’))) (poly ‘1’)
  exp2 (mul S S) (poly ‘0’)

/-- **Witness bounds for a primitive recursion's result**, given bounds on its
values. -/
theorem wb_resultDef {k : ℕ} (p : PR.Blueprint k)
    (c : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], PR.Construction V p)
    (hz : WB M p.zero.val) (hs : WB M p.succ.val) (H : BoundTerm (k + 2))
    (hH : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin (k + 2) → V) (i : V),
      i ≤ e 1 → (c V).result (fun j => e j.succ.succ) i ≤ H.vval e) :
    WB M p.resultDef.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_cseq p hz hs
  have : WB M memRelOpr.sentence := wb_memRel (M := M)
  simp only [PR.Blueprint.resultDef, HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs_bt' _ (by simp) (histT H) (fun V _ _ e s h => ?_) (by wb_auto)
  have h' : (c V).CSeq (fun j => e j.succ.succ) s ∧ ⟪e 1, e 0⟫ ∈ s := by
    simpa [Semiformula.Operator.val, memRelOpr, (c V).cseq_defined.iff, Matrix.comp_vecCons'',
      PRAHistoryTruncation.val_comp_bvar] using h
  obtain ⟨s', hs', hu', hlt⟩ := history_bound (c V) _ h'.1 h'.2 (hH V e)
  refine ⟨s', ?_, ?_⟩
  · simpa [histT, vval] using le_of_lt hlt
  · simpa [Semiformula.Operator.val, memRelOpr, (c V).cseq_defined.iff, Matrix.comp_vecCons'',
      PRAHistoryTruncation.val_comp_bvar] using And.intro hs' hu'

theorem wb_qqAllsDef : WB M qqAllsDef.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqAllDef (M := M)
  have hz : WB M qqAlls.blueprint.zero.val := by
    simp only [qqAlls.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have hs : WB M qqAlls.blueprint.succ.val := by
    simp only [qqAlls.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  simp only [qqAllsDef, HierarchySymbol.Semiformula.val_rew]
  refine wb_rew _ (wb_resultDef _ (fun _ _ _ => qqAlls.construction) hz hs
    (tauT (poly ‘#2’) (poly ‘2 * #1’)) (fun V _ _ e i hi => ?_))
  have hv : (fun j : Fin 1 => e j.succ.succ) = ![e 2] := funext fun j => Fin.cases rfl (fun l => l.elim0) j
  rw [hv, vval_tauT]
  exact le_trans (qqAlls_le (e 2) i) (tau_mono (by simp [vval]) (by simpa [vval] using mul_le_mul' (le_refl 2) hi))

/-! ### `concat` -/

private theorem wb_concat_core (neg : Bool) :
    WB M (if neg then ∼Concat.blueprint.blueprint.core.pi.val
      else Concat.blueprint.blueprint.core.sigma.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_pairDef (M := M); have := wb_adjoinDef (M := M); have := wb_memRel (M := M)
  have := wb_neg_pairDef (M := M); have := wb_neg_memRel (M := M)
  have : WB M memRelOpr.sentence := wb_memRel (M := M)
  have : WB M (∼memRelOpr.sentence) := wb_neg_memRel (M := M)
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    simp only [VecRec.Blueprint.blueprint, Concat.blueprint, HierarchySymbol.Semiformula.sigma_mkDelta,
      HierarchySymbol.Semiformula.pi_mkDelta, HierarchySymbol.Semiformula.val_mkPi,
      HierarchySymbol.Semiformula.val_mkSigma]
    wb_auto
    · exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(#2 + 1) * (#2 + 1) + 1’ (fun V _ _ e u h => ⟨u, by
        have h' := h; simp at h'
        rw [h'.1, adjoin_def]
        simpa using add_le_add (pair_le_sq (le_refl (e 2)) (le_refl 0)) (le_refl 1), h⟩) (by wb_auto)
    · refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(#2 + #1 + 1) * (#2 + #1 + 1) + 1’
        (fun V _ _ e u h => ⟨u, by
          have h' := h; simp at h'
          rw [h'.1, adjoin_def]
          exact add_le_add (pair_le_sq le_rfl le_rfl) le_rfl, h⟩) ?_
      wb_auto
      exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(#3 + #1 + 1) * (#3 + #1 + 1) + 1’
        (fun V _ _ e u h => ⟨u, by
          have h' := h; simp at h'
          rw [h'.1, adjoin_def]
          exact add_le_add (pair_le_sq le_rfl le_rfl) le_rfl, h⟩) (by wb_auto)

theorem wb_concat_core_sigma : WB M Concat.blueprint.blueprint.core.sigma.val := by
  simpa using wb_concat_core (M := M) false

theorem wb_concat_core_neg_pi : WB M (∼Concat.blueprint.blueprint.core.pi.val) := by
  simpa using wb_concat_core (M := M) true

theorem wb_concat_graph : WB M Concat.blueprint.graphDef.val := by
  refine PRAWitnessFixpointGraph.wb_fixpointDef Concat.blueprint.blueprint wb_concat_core_sigma
    wb_concat_core_neg_pi ‘#0 + 1’ ?_
  intro V _ _ e s L hL hx
  have h := PRAWitnessFixpointGraph.stage_bound_of_rank (Concat.adjointruction (V := V)).adjointruction
    (fun x => x) (fun _ => le_rfl)
    (vecRec_rankFinite' Concat.adjointruction (fun _ x _ ih => le_of_lt (lt_adjoin' x ih)))
    (fun x => x + 1) (fun _ => le_rfl) (fun i => e i.succ) (e 0) s L hL hx
  exact ⟨_, by simpa using h.1, h.2⟩

theorem wb_concatDef : WB M concatDef.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hg := wb_concat_graph (M := M); have := wb_pairDef (M := M)
  simp only [concatDef, VecRec.Blueprint.resultDef, HierarchySymbol.Semiformula.val_mkSigma]
  refine wb_exs_term ‘(#1 + #0 + 1) * (#1 + #0 + 1)’ (fun e y h => ?_) (by wb_auto)
  simp at h
  rw [h.1]
  simpa [sq] using pair_polybound (e 1) (e 0)

theorem wb_fvarVecDef : WB M fvarVecDef.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_concatDef (M := M); have := wb_qqFvarDef (M := M)
  have hz : WB M fvarVec.blueprint.zero.val := by
    simp only [fvarVec.blueprint, HierarchySymbol.Semiformula.val_mkSigma]; wb_auto
  have hs : WB M fvarVec.blueprint.succ.val := by
    simp only [fvarVec.blueprint, HierarchySymbol.Semiformula.val_mkSigma]
    exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(1 + #2 + 1) * (1 + #2 + 1) + 1’
      (fun V _ _ e u h => ⟨u, by
        have h' := h; simp at h'
        rw [h'.1]; exact qqFvar_le _, h⟩) (by wb_auto)
  simp only [fvarVecDef]
  refine wb_resultDef _ (fun _ _ _ => fvarVec.construction) hz hs
    (tauT (poly ‘(#1 + 2) * (#1 + 2) + 1’) (poly ‘2 * #1’)) (fun V _ _ e i hi => ?_)
  have hv : (fun j : Fin 0 => e j.succ.succ) = ![] := funext fun j => j.elim0
  rw [hv, vval_tauT]
  simpa [vval, fvarVec] using fvarVec_le (e 1) i hi

end models
end DiophantineConsistency.PRAWitnessPR
