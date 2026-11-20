import Hierarchy

/-! Constructive equivalence between a universal packet sentence and the
absence of a tuple failing its zero-test. These theorems are derivations
in the object theory. The only induction axiom used is quantifier-free.
-/
namespace RHCounterexamples

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

def neg {n : Nat} (A : Fm PTm n) : Fm PTm n := A ⟶ Fm.bot

/-- Flip the initial universal prefix and negate its matrix. -/
def counter : {n : Nat} → Fm PTm n → Fm PTm n
  | _, .all A => .ex (counter A)
  | _, A => neg A

/-- A universal block ending in a term-equals-zero predicate. -/
inductive UniversalZero : {n : Nat} → Fm PTm n → Prop
  | matrix {n : Nat} (t : PTm n) : UniversalZero (t ≐ PTm.zero)
  | binder {n : Nat} {A : Fm PTm (n+1)} : UniversalZero A → UniversalZero (.all A)

def zeroCases {n : Nat} (t : PTm n) : Fm PTm n :=
  (t ≐ PTm.zero) ⋎ neg (t ≐ PTm.zero)

/-- Decidability of every term's zero-test in iPRA itself. -/
theorem zero_decidable {n : Nat} {Γ : List (Fm PTm n)} (t : PTm n) :
    Prf PRAAx Γ (zeroCases t) := by
  let A : Fm PTm (n+1) := zeroCases (var 0)
  have h : Prf PRAAx Γ (.all A) := by
    apply PRA.qfInd A
    · exact ⟨trivial, trivial, trivial⟩
    · simpa [A, zeroCases, neg] using (Prf.orI₁ (ψ := neg (PTm.zero ≐ PTm.zero))
        (Prf.eqRefl (Ax := PRAAx) (Γ := Γ) PTm.zero))
    · simpa [A, zeroCases, neg] using (Prf.orI₂ (φ := PTm.succ (var 0) ≐ PTm.zero)
        (PRA.succNeZero (Γ := A :: Γ.map Fm.shift) (var 0)))
  simpa [A, zeroCases, neg] using Prf.allE t h

private theorem ex_at_var {n : Nat} {C : Fm PTm (n+1)}
    {Γ : List (Fm PTm (n+1))} (h : Prf PRAAx Γ C) :
    Prf PRAAx Γ (Fm.ex C).shift := by
  apply Prf.exI (var 0)
  simpa only [Fm.subst_up_succ_inst] using h

private theorem lift_binder {n : Nat} {A C : Fm PTm (n+1)}
    (h : Prf PRAAx [] (Fm.iff A (neg C))) :
    Prf PRAAx [] (Fm.iff (Fm.all A) (neg (Fm.ex C))) := by
  apply Prf.iffI
  · apply Prf.impI
    apply Prf.impI
    apply Prf.exE Prf.hyp0
    have ha := (Prf.allOpen (Prf.hyp1 (Ax := PRAAx) (Γ := [])
      (φ := Fm.all A) (ψ := Fm.ex C))).wk (ψ := C)
    exact Prf.impE (Prf.iffMp (Prf.ofNil h) ha) Prf.hyp0
  · apply Prf.impI
    apply Prf.allI
    apply Prf.iffMpr (Prf.ofNil h)
    apply Prf.impI
    have hn := (Prf.shift (Prf.hyp0 (Ax := PRAAx) (Γ := [])
      (φ := neg (Fm.ex C)))).wk (ψ := C)
    exact Prf.impE hn (ex_at_var Prf.hyp0)

/-- Positive universal testing and the negative counterexample formulation
are equivalent in iPRA for every finite universal block of zero-tests. -/
theorem no_counterexample {n : Nat} {A : Fm PTm n} (hA : UniversalZero A) :
    Prf PRAAx [] (Fm.iff A (neg (counter A))) := by
  induction hA with
  | matrix t =>
    apply Prf.iffI
    · exact Prf.impI (Prf.impI (Prf.impE Prf.hyp0 Prf.hyp1))
    · apply Prf.impI
      apply Prf.orE (zero_decidable t)
      · exact Prf.hyp0
      · exact Prf.botE _ (Prf.impE Prf.hyp1 Prf.hyp0)
  | binder _ ih => exact lift_binder ih

open RHHierarchy

theorem rh_iff_no_counterexample (f : PR 5) :
    Prf PRAAx [] (Fm.iff (RHOf f) (neg (counter (RHOf f)))) :=
  no_counterexample (.binder (.matrix _))

theorem grh_iff_no_counterexample (f : PR 5) :
    Prf PRAAx [] (Fm.iff (GRHOf f) (neg (counter (GRHOf f)))) :=
  no_counterexample (.binder (.binder (.matrix _)))

theorem erh_iff_no_counterexample (f : PR 5) :
    Prf PRAAx [] (Fm.iff (ERHOf f) (neg (counter (ERHOf f)))) :=
  no_counterexample (.binder (.binder (.binder (.binder (.binder (.matrix _))))))

end RHCounterexamples
