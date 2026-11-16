module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentCode
@[expose] public section

/-! Exact singleton scan behavior. Singleton sequents retain the trailing
empty disjunction; no equality with their sole translated member is asserted. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

attribute [local irreducible] ActualArithmeticGraph.graph sequentScanGraph translateGraph

noncomputable def singletonScanInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ param p, ∃ s a out, !expDef s p ∧ !translateGraph a param p ∧
    !sequentScanGraph out param s n ∧
    (p<n → !(ActualArithmeticGraph.graph translationOr) out a 1 0 0) ∧
    (n≤p → out=1)”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem singletonScan_invariant (n : V) :
    singletonScanInvariant.Evalb ![n] ↔ ∀ param p : V,
      (p<n → sequentScan param {p} n=
        ActualArithmeticGraph.eval translationOr (translate param p) 1 0 0) ∧
      (n≤p → sequentScan param {p} n=1) := by
  simp [singletonScanInvariant,sequentScan_graph,translate_graph,
    ActualArithmeticGraph.graph_correct,singleton_def,Matrix.comp_vecCons'']

attribute [local irreducible] sequentScan translate singletonScanInvariant

variable [V↓[ℒₒᵣ] ⊧* theory]

theorem sequentScan_singleton (n param p : V) :
    (p<n → sequentScan param {p} n=
      ActualArithmeticGraph.eval translationOr (translate param p) 1 0 0) ∧
    (n≤p → sequentScan param {p} n=1) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ param p : V,
      (p<n → sequentScan param {p} n=
        ActualArithmeticGraph.eval translationOr (translate param p) 1 0 0) ∧
      (n≤p → sequentScan param {p} n=1) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V => ∀ param p : V,
      (p<n → sequentScan param {p} n=
        ActualArithmeticGraph.eval translationOr (translate param p) 1 0 0) ∧
      (n≤p → sequentScan param {p} n=1)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb singletonScanInvariant,by trivial,?_⟩
      intro n
      simpa using (singletonScan_invariant (V:=V) n).symm
    · intro param p
      simp
    · intro n ih param p
      by_cases hn : n=p
      · subst p
        rw [sequentScan_mem _ _ _ (by simp),(ih param n).2 le_rfl]
        simp
      · rw [sequentScan_not_mem _ _ _ (by simpa using hn)]
        constructor
        · intro hp
          rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he | hlt
          · exact False.elim (hn he.symm)
          · exact (ih param p).1 hlt
        · intro hp
          exact (ih param p).2 (le_trans (by simp) hp)
  exact hall n param p

theorem sequent_singleton (param p : V) :
    sequentCode param {p}=
      ActualArithmeticGraph.eval translationOr (translate param p) 1 0 0 := by
  change sequentScan param ({p}:V) ({p}:V)=_
  exact (sequentScan_singleton ({p}:V) param p).1 (lt_of_mem (by simp))

/-- This is nativeOr(1,1), not the code 1. Certificate extraction must apply
actual double-negation elimination, which is supplied in a later bridge. -/
theorem sequent_singleton_falsum (param : V) :
    sequentCode param {qqFalsum}=
      ActualArithmeticGraph.eval translationOr (1:V) 1 0 0 := by
  rw [sequent_singleton,translate_falsum]

#print axioms singletonScan_invariant
#print axioms sequentScan_singleton
#print axioms sequent_singleton
#print axioms sequent_singleton_falsum
end M6.PA.RelationalSource.Numeric

