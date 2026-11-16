module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedParameterClosure
public import M6PA.Calibration.PAForwardRelationalClosureClosedPremise
@[expose] public section

/-! Exact raw target closure syntax and constructive specialization. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

theorem closeParameters_eq_allClosure (n : Nat) (p : Form) :
    closeParameters n p = ∀¹* (Rew.fixitr 0 n ▹ p) := by
  induction n with
  | zero => simp [closeParameters]
  | succ n ih =>
    rw [closeParameters, ih, LawfulSyntacticRewriting.allClosure_fixitr]
    rfl

def rawAllClosureElim {Γ : List Form} {n : Nat} (p : Formula n)
    (b : Fin n → Term 0) (h : ND.Proof Γ (∀¹* p)) :
    ND.Proof Γ (Rew.subst b ▹ p) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have hh := ih (.all p) (fun i => b i.succ) h
    have ho := allElim _ (b 0) hh
    have he : (Rew.subst ![b 0]).comp (Rew.subst (fun i => b i.succ)).q = Rew.subst b := by
      ext i
      · refine Fin.cases ?_ (fun j => ?_) i <;> simp [Rew.comp_app]
      · simp [Rew.comp_app]
    simpa only [Rewriting.app_all, Rewriting.subst, ← app_eq_rewAux, ← TransitiveRewriting.comp_app, he] using ho

/-- A support bound is enough; unused indices may be quantified. -/
theorem closeParameters_noFree (n : Nat) (p : Form)
    (hp : ∀ i, p.FVar? i → i < n) (i : Nat) :
    ¬ (closeParameters n p).FVar? i := by
  rw [closeParameters_eq_allClosure]
  simp only [Semiformula.fvar?_allClosure]
  intro h
  rcases Semiformula.fvar?_rew h with (⟨j, hj⟩ | ⟨j, hj, hij⟩)
  · exact Fin.elim0 j
  · simp [Rew.fixitr_fvar, hp j hj] at hij

theorem closeParameters_shift (n : Nat) (p : Form)
    (hp : ∀ i, p.FVar? i → i < n) :
    (closeParameters n p).shift = closeParameters n p := by
  apply Semiformula.rew_eq_self_of
  · intro i; exact Fin.elim0 i
  · intro i hi; exact False.elim (closeParameters_noFree n p hp i hi)

/-- Specialize the single closed theorem at an arbitrary finite assignment. -/
def closeParametersElim {Γ : List Form} (n : Nat) (p : Form)
    (hp : ∀ i, p.FVar? i → i < n) (f : Nat → Term 0)
    (h : ND.Proof Γ (closeParameters n p)) :
    ND.Proof Γ (Rew.rewrite f ▹ p) := by
  rw [closeParameters_eq_allClosure] at h
  have ho := rawAllClosureElim (Rew.fixitr 0 n ▹ p) (fun i => f i.val) h
  have he : (Rew.subst (fun i : Fin (0+n) => f i.val)).comp (Rew.fixitr 0 n) ▹ p =
      Rew.rewrite f ▹ p := by
    apply Semiformula.rew_eq_of_funEqOn₀
    intro i hi
    simp [Rew.comp_app, Rew.fixitr_fvar, hp i hi]
  simpa only [← TransitiveRewriting.comp_app, he] using ho

#print axioms closeParameters_noFree
#print axioms closeParameters_shift
#print axioms closeParametersElim
#print axioms closeParameters_eq_allClosure
#print axioms rawAllClosureElim
end M6.PA.ForwardRelational
