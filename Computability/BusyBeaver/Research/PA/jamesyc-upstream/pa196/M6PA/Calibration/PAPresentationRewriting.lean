module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationSyntax
@[expose] public section

/-! Capture-avoiding compatibility, including the extra existential binder
introduced by strict-order elimination. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

@[simp] theorem term_bShift {ξ : Type} {n : Nat} (t : ArithmeticSemiterm ξ n) :
    term (Rew.bShift t) = Rew.bShift (term t) :=
  term_rew Rew.bShift Rew.bShift (by intro i; rfl) (by intro i; rfl) t

def translateRew {ξ ζ : Type} {n m : Nat} (ω : Rew ℒₒᵣ ξ n ζ m) : Rew language ξ n ζ m :=
  Rew.bind (fun i => term (ω (.bvar i))) (fun i => term (ω (.fvar i)))

theorem term_translateRew {ξ ζ : Type} {n m : Nat} (ω : Rew ℒₒᵣ ξ n ζ m)
    (t : ArithmeticSemiterm ξ n) : term (ω t) = translateRew ω (term t) :=
  term_rew ω (translateRew ω) (by intro i; rfl) (by intro i; rfl) t

@[simp] theorem translateRew_q {ξ ζ : Type} {n m : Nat} (ω : Rew ℒₒᵣ ξ n ζ m) :
    translateRew ω.q = (translateRew ω).q := by
  apply Rew.ext
  · intro i
    change term (ω.q (.bvar i)) = (translateRew ω).q (.bvar i)
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Rew.q_bvar_zero,Rew.q_bvar_zero]; rfl
    · rw [Rew.q_bvar_succ,Rew.q_bvar_succ,term_bShift]; rfl
  · intro i
    change term (ω.q (.fvar i)) = (translateRew ω).q (.fvar i)
    rw [Rew.q_fvar,Rew.q_fvar,term_bShift]; rfl

theorem eq_rew {ξ ζ : Type} {n m : Nat} (ω : Rew language ξ n ζ m)
    (s t : Semiterm language ξ n) :
    Semiformula.rewAux ω (eq s t) = eq (ω s) (ω t) := by
  apply congrArg (Semiformula.rel (L := language) (ξ := ζ) (n := m) Rel.eq)
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

theorem less_rew {ξ ζ : Type} {n m : Nat} (ω : Rew language ξ n ζ m)
    (s t : Semiterm language ξ n) :
    Semiformula.rewAux ω (less s t) = less (ω s) (ω t) := by
  simp only [less,Semiformula.rewAux,eq_rew,rew_add,rew_succ,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero]
  rfl

theorem atom_rew {ξ ζ : Type} {n m k : Nat} (ω : Rew ℒₒᵣ ξ n ζ m)
    (r : Language.ORing.Rel k) (ts : Fin k → ArithmeticSemiterm ξ n) :
    atom r (ω ∘ ts) = Semiformula.rewAux (translateRew ω) (atom r ts) := by
  cases r <;> simp only [atom,Function.comp_apply,term_translateRew,eq_rew,less_rew]

theorem formula_rew {ξ ζ : Type} {n m : Nat} (p : ArithmeticSemiformula ξ n)
    (ω : Rew ℒₒᵣ ξ n ζ m) :
    formula (Semiformula.rewAux ω p) = Semiformula.rewAux (translateRew ω) (formula p) := by
  induction p generalizing m with
  | verum | falsum => rfl
  | rel r ts => exact atom_rew ω r ts
  | nrel r ts =>
    change (atom r (ω ∘ ts)).neg = Semiformula.rewAux (translateRew ω) (atom r ts).neg
    rw [atom_rew]
    exact (Semiformula.rewAux_neg _ _).symm
  | and p q ihp ihq | or p q ihp ihq => simp only [Semiformula.rewAux,formula,ihp,ihq]; rfl
  | all p ih | exs p ih => simp only [Semiformula.rewAux,formula,ih,translateRew_q]; rfl

#print axioms formula_rew
end M6.PA.Presentation
