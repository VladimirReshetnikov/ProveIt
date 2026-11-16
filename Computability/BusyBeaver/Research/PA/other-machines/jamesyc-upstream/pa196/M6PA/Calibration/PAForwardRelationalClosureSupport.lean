module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalClosureCoverage
@[expose] public section

/-! Translation introduces no free parameter names. The proof uses exact source
and target renaming, not expansion of the arithmetic graph definitions. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] formula value Ordinal.domain PairGraph.orderIso

theorem canonical_sourceRename (p : SourceFormula 0) (ψ : Nat → Nat) :
    Semiformula.rewAux (Rew.map id ψ)
      (formula p Fin.elim0 (fun i => (.fvar i : Term 0))) =
      formula (Semiformula.rewAux (Rew.map id ψ) p) Fin.elim0 (fun i => (.fvar i : Term 0)) := by
  rw [formula_rew, formula_sourceMap]
  apply formula_env_ext
  · intro i
    exact Fin.elim0 i
  · intro i
    rfl

/-- The canonical target translation has no free variables beyond those of the
source. Internal arithmetic witnesses are bound, never extra free parameters. -/
theorem canonical_formula_support (p : SourceFormula 0) (i : Nat)
    (h : (formula p Fin.elim0 (fun j => (.fvar j : Term 0))).FVar? i) : p.FVar? i := by
  classical
  by_contra hi
  let ψ : Nat → Nat := fun j => if j = i then i+1 else j
  have hsource : Semiformula.rewAux (Rew.map id ψ) p = p := by
    apply Semiformula.rew_eq_self_of
    · intro j
      exact Fin.elim0 j
    · intro j hj
      have hji : j ≠ i := by intro e; subst j; exact hi hj
      simp [ψ, hji]
  have htarget : Semiformula.rewAux (Rew.map id ψ)
      (formula p Fin.elim0 (fun j => (.fvar j : Term 0))) =
      formula p Fin.elim0 (fun j => (.fvar j : Term 0)) := by
    rw [canonical_sourceRename, hsource]
  have hh : ((Rew.map id ψ : Rew language Nat 0 Nat 0) ▹
      formula p Fin.elim0 (fun j => (.fvar j : Term 0))).FVar? i := by
    simpa only [app_eq_rewAux, htarget] using h
  rcases Semiformula.fvar?_rew hh with ⟨j,hj⟩ | ⟨j,_,hj⟩
  · exact Fin.elim0 j
  · by_cases hji : j = i
    · subst j
      simpa [ψ] using hj
    · simpa [ψ, hji, Ne.symm hji] using hj

theorem canonical_formula_support_bound (p : SourceFormula 0) (i : Nat)
    (h : (formula p Fin.elim0 (fun j => (.fvar j : Term 0))).FVar? i) : i < p.fvSup :=
  Semiformula.lt_fvSup_of_fvar? (canonical_formula_support p i h)

theorem formula_from_canonical (p : SourceFormula 0) (f : Nat → Term 0) :
    Semiformula.rewAux (Rew.rewrite f) (formula p Fin.elim0 (fun i => (.fvar i : Term 0))) =
      formula p Fin.elim0 f := by
  rw [formula_rew]
  apply formula_env_ext
  · intro i
    exact Fin.elim0 i
  · intro i
    rfl

/-- Ground environments need agree only on actual source free parameters. -/
theorem formula_env_on_sourceFree (p : SourceFormula 0) (f g : Nat → Term 0)
    (hfg : ∀ i, p.FVar? i → f i = g i) : formula p Fin.elim0 f = formula p Fin.elim0 g := by
  rw [← formula_from_canonical p f, ← formula_from_canonical p g]
  apply Semiformula.rew_eq_of_funEqOn
  · intro i
    exact Fin.elim0 i
  · intro i hi
    exact hfg i (canonical_formula_support p i hi)

theorem formula_env_on_sourcePrefix (p : SourceFormula 0) (f g : Nat → Term 0)
    (hfg : ∀ i, i < p.fvSup → f i = g i) : formula p Fin.elim0 f = formula p Fin.elim0 g :=
  formula_env_on_sourceFree p f g (fun i hi => hfg i (Semiformula.lt_fvSup_of_fvar? hi))

theorem formula_env_closed_source (p : SourceFormula 0) (hclosed : p.freeVariables = ∅)
    (f g : Nat → Term 0) : formula p Fin.elim0 f = formula p Fin.elim0 g := by
  apply formula_env_on_sourceFree p f g
  intro i hi
  simp [Semiformula.FVar?, hclosed] at hi

theorem formula_closed_source_shift (p : SourceFormula 0) (hclosed : p.freeVariables = ∅)
    (f : Nat → Term 0) : (formula p Fin.elim0 f).shift = formula p Fin.elim0 f := by
  rw [formula_shift]
  have he : freeShiftEnv (Fin.elim0 : Fin 0 → Term 0) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rw [he]
  exact formula_env_closed_source p hclosed (freeShiftEnv f) f

#print axioms canonical_sourceRename
#print axioms canonical_formula_support
#print axioms canonical_formula_support_bound
#print axioms formula_from_canonical
#print axioms formula_env_on_sourceFree
#print axioms formula_env_on_sourcePrefix
#print axioms formula_env_closed_source
#print axioms formula_closed_source_shift
end M6.PA.ForwardRelational

