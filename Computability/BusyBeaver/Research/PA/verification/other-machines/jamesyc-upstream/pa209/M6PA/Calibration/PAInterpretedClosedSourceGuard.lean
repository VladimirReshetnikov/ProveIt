module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedClosedSourceSyntax
public import M6PA.Calibration.PAInterpretedInductionParameters
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

theorem domain_fvar_support (i j : Nat) (h : (Ordinal.domain (&i : Term 0)).FVar? j) : j = i := by
  simpa [Ordinal.domain, Ordinal.representative, Ordinal.memberIr, Ordinal.transitive,
    Ordinal.memberTransitive, Ordinal.memberLinear, Ordinal.internalExtrema,
    Ordinal.subset, Ordinal.nonempty, Ordinal.least, Ordinal.greatest,
    ND.mem, ND.eq, Semiformula.FVar?, Semiformula.freeVariables, ← Semiformula.neg_eq,
    Semiterm.freeVariables, Fin.univ_succ] using h

theorem inductionParameterGuard_support (is : List Nat) (i : Nat)
    (h : (inductionParameterGuard is (fun j => &j)).FVar? i) : i ∈ is := by
  induction is with
  | nil => simp [inductionParameterGuard] at h
  | cons j js ih =>
    have hh : (Ordinal.domain (&j : Term 0)).FVar? i ∨
        (inductionParameterGuard js (fun k => &k)).FVar? i := by
      simpa only [inductionParameterGuard, Semiformula.fvar?_and] using h
    rcases hh with hj | hj
    · exact List.mem_cons.mpr (.inl (domain_fvar_support j i hj))
    · exact List.mem_cons.mpr (.inr (ih hj))

theorem inductionParameterGuard_rewrite (is : List Nat) (f : Nat → Term 0) :
    Rew.rewrite f ▹ inductionParameterGuard is (fun i => &i) = inductionParameterGuard is f := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [inductionParameterGuard, LogicalConnective.HomClass.map_and, ih]
    congr 1
    simpa only [app_eq_rewAux, Rew.rewrite_fvar] using
      Ordinal.domain_rew (Rew.rewrite f) (&i : Term 0)

def inductionParameterGuardIntro {Γ : List Form} (is : List Nat) (f : Nat → Term 0)
    (H : ∀ i, i ∈ is → ND.Proof Γ (Ordinal.domain (f i))) :
    ND.Proof Γ (inductionParameterGuard is f) := by
  induction is with
  | nil => exact closed LK.Derivation.verum
  | cons i is ih =>
    exact andIntro (H i (by simp)) (ih (fun j hj => H j (by simp [hj])))

#print axioms domain_fvar_support
#print axioms inductionParameterGuard_support
#print axioms inductionParameterGuard_rewrite
#print axioms inductionParameterGuardIntro
end M6.PA.ForwardRelational

