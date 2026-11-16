module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedClosedSourceGuard
@[expose] public section

/-! Conversion of one fully closed guarded target derivation to the exact
source universal closure. The finite target support obligation is syntactic,
not an open proof premise or a uniform proof family. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def guardedSourceBody (p : SourceFormula 0) (is : List Nat) : Form :=
  inductionParameterGuard is (fun i => &i) 🡒 formula p Fin.elim0 (fun i => &i)

theorem guardedSourceBody_support (p : SourceFormula 0) (is : List Nat)
    (his : ∀ i, i ∈ is → i < p.fvSup)
    (hp : ∀ i, (formula p Fin.elim0 (fun j => (&j : Term 0))).FVar? i → i < p.fvSup) :
    ∀ i, (guardedSourceBody p is).FVar? i → i < p.fvSup := by
  intro i hi
  have hh : (inductionParameterGuard is (fun j => (&j : Term 0))).FVar? i ∨
      (formula p Fin.elim0 (fun j => (&j : Term 0))).FVar? i := by
    simpa only [guardedSourceBody, Semiformula.FVar?, Semiformula.freeVariables_imp, Finset.mem_union] using hi
  exact hh.elim (fun h => his i (inductionParameterGuard_support is i h)) (hp i)

theorem guardedSourceBody_rewrite (p : SourceFormula 0) (is : List Nat)
    (f : Nat → Term 0) :
    Rew.rewrite f ▹ guardedSourceBody p is =
      inductionParameterGuard is f 🡒 formula p Fin.elim0 f := by
  simp only [guardedSourceBody, LogicalConnective.HomClass.map_imply,
    inductionParameterGuard_rewrite]
  congr 1
  simp only [app_eq_rewAux, formula_rew, Rew.rewrite_fvar]
  apply formula_env_ext
  · intro i; exact Fin.elim0 i
  · intro i; rfl

/-- The only logical input is one already fully closed proof. Target finite
support is exposed separately until discharged by translation support syntax. -/
def closedGuardToSourceUniversalClosureOfSupport {Γ : List Form}
    (p : SourceFormula 0) (is : List Nat)
    (his : ∀ i, i ∈ is → i < p.fvSup)
    (hp : ∀ i, (formula p Fin.elim0 (fun j => (&j : Term 0))).FVar? i → i < p.fvSup)
    (h : ND.Proof Γ (closeParameters p.fvSup (guardedSourceBody p is)))
    (f : Nat → Term 0) : ND.Proof Γ (formula p.univCl' Fin.elim0 f) := by
  have hs := guardedSourceBody_support p is his hp
  apply sourceUniversalClosureFromClosed p (closeParameters p.fvSup (guardedSourceBody p is))
    (closeParameters_shift p.fvSup (guardedSourceBody p is) hs) ?_ h f
  intro Δ hc g H
  have ho := closeParametersElim p.fvSup (guardedSourceBody p is) hs g hc
  rw [guardedSourceBody_rewrite] at ho
  exact mp (inductionParameterGuardIntro is g (fun i hi => H ⟨i, his i hi⟩)) ho

#print axioms guardedSourceBody_support
#print axioms guardedSourceBody_rewrite
#print axioms closedGuardToSourceUniversalClosureOfSupport
end M6.PA.ForwardRelational

