module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationRewriting
@[expose] public section

/-! Concrete binder operations used by the actual Foundation LK rules. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

@[simp] theorem translateRew_shift {n : Nat} :
    translateRew (Rew.shift (L := ℒₒᵣ) (n := n)) = Rew.shift (L := language) := by
  apply Rew.ext
  · intro i; rfl
  · intro i; rfl

@[simp] theorem translateRew_free :
    translateRew (Rew.free (L := ℒₒᵣ) (n := 0)) = Rew.free (L := language) := by
  apply Rew.ext
  · intro i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  · intro i; rfl

@[simp] theorem translateRew_subst {ξ : Type} {n m : Nat}
    (v : Fin n → ArithmeticSemiterm ξ m) :
    translateRew (Rew.subst v) = Rew.subst (term ∘ v) := by
  apply Rew.ext
  · intro i; rfl
  · intro i; rfl

@[simp] theorem formula_shift (p : ArithmeticProposition) :
    formula p.shift = (formula p).shift := by
  change formula (Semiformula.rewAux Rew.shift p) = Semiformula.rewAux Rew.shift (formula p)
  rw [formula_rew,translateRew_shift]

@[simp] theorem formula_free (p : ArithmeticSemiproposition 1) :
    formula p.free = (formula p).free := by
  change formula (Semiformula.rewAux Rew.free p) = Semiformula.rewAux Rew.free (formula p)
  rw [formula_rew,translateRew_free]

@[simp] theorem formula_subst {ξ : Type} {n m : Nat} (p : ArithmeticSemiformula ξ n)
    (v : Fin n → ArithmeticSemiterm ξ m) :
    formula (Semiformula.rewAux (Rew.subst v) p) =
      Semiformula.rewAux (Rew.subst (term ∘ v)) (formula p) := by
  simpa only [translateRew_subst] using formula_rew p (Rew.subst v)

@[simp] theorem formula_instantiate (p : ArithmeticSemiproposition 1)
    (t : ArithmeticTerm Nat) : formula (p/[t]) = (formula p)/[term t] := by
  have hv : term ∘ (![t] : Fin 1 → ArithmeticTerm Nat) = ![term t] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  change formula (Semiformula.rewAux (Rew.subst ![t]) p) =
    Semiformula.rewAux (Rew.subst ![term t]) (formula p)
  rw [formula_subst,hv]

#print axioms formula_instantiate
#print axioms formula_free
end M6.PA.Presentation
