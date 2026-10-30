import DiophantineConsistency.HAAdditiveArithmetic

/-! # Multiplicative arithmetic proved in conventional HA

Every induction below is an application of the actual HA formula-induction
rule. Free term parameters are shifted beneath its variable and restored by
universal elimination. Algebraic rearrangements are composed HA equalities,
not metatheoretic ring identities or classical PA derivations.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HA.Arithmetic
open SetTheory.PA

private theorem in_context {G : List Formula} {a : Formula} (h : Proves a) :
    Relative Formula.Ax_s G a := h.weaken (by simp)

private theorem add_interchange (a b c d : Term) : Proves (.eq
    (.add (.add a b) (.add c d)) (.add (.add a c) (.add b d))) := by
  have h₁ := add_assoc a b (.add c d)
  have h₂ := (add_assoc b c d).eq_symm.eq_add_right a
  have h₃ := ((add_comm b c).eq_add_left d).eq_add_right a
  have h₄ := (add_assoc c b d).eq_add_right a
  have h₅ := (add_assoc a c (.add b d)).eq_symm
  exact (((h₁.eq_trans h₂).eq_trans h₃).eq_trans h₄).eq_trans h₅

theorem zero_mul_all : Proves (.all (.eq (.mul .zero (.var 0)) .zero)) := by
  let a : Formula := .eq (.mul .zero (.var 0)) .zero
  apply induction a
  · simpa only [Proves, a, Formula.subst, Term.subst, Formula.substZero] using mul_zero .zero
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    have ih : Relative Formula.Ax_s [a] a :=
      relative_of_derives (.ass _ _ List.mem_cons_self)
    have hl : Relative Formula.Ax_s [a]
        (.eq (.mul .zero (.succ (.var 0))) (.add (.mul .zero (.var 0)) .zero)) :=
      in_context (mul_succ .zero (.var 0))
    have h := (hl.eq_trans (ih.eq_add_left .zero)).eq_trans (in_context (add_zero .zero))
    simpa only [Proves, List.map_nil, a, Formula.subst, Term.subst,
      Formula.substSuccVar] using h

theorem zero_mul (t : Term) : Proves (.eq (.mul .zero t) .zero) := by
  have h := Relative.all_elim t zero_mul_all
  simpa only [Proves, Formula.subst, Term.subst, Formula.instTerm] using h

theorem mul_one (t : Term) : Proves (.eq (.mul t (.succ .zero)) t) :=
  ((mul_succ t .zero).eq_trans ((mul_zero t).eq_add_left t)).eq_trans (zero_add t)

theorem one_mul_all : Proves (.all (.eq (.mul (.succ .zero) (.var 0)) (.var 0))) := by
  let a : Formula := .eq (.mul (.succ .zero) (.var 0)) (.var 0)
  apply induction a
  · simpa only [Proves, a, Formula.subst, Term.subst, Formula.substZero] using mul_zero (.succ .zero)
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    have ih : Relative Formula.Ax_s [a] a :=
      relative_of_derives (.ass _ _ List.mem_cons_self)
    have hl : Relative Formula.Ax_s [a]
        (.eq (.mul (.succ .zero) (.succ (.var 0)))
          (.add (.mul (.succ .zero) (.var 0)) (.succ .zero))) :=
      in_context (mul_succ (.succ .zero) (.var 0))
    have h := (hl.eq_trans (ih.eq_add_left (.succ .zero))).eq_trans
      (in_context (add_one (.var 0)))
    simpa only [Proves, List.map_nil, a, Formula.subst, Term.subst,
      Formula.substSuccVar] using h

theorem one_mul (t : Term) : Proves (.eq (.mul (.succ .zero) t) t) := by
  have h := Relative.all_elim t one_mul_all
  simpa only [Proves, Formula.subst, Term.subst, Formula.instTerm] using h

/-- Distribution over a sum on the right, by induction on its final argument. -/
theorem mul_add_all (x y : Term) : Proves (.all (.eq
    (.mul (Term.rename Nat.succ x) (.add (Term.rename Nat.succ y) (.var 0)))
    (.add (.mul (Term.rename Nat.succ x) (Term.rename Nat.succ y))
      (.mul (Term.rename Nat.succ x) (.var 0))))) := by
  let xs := Term.rename Nat.succ x
  let ys := Term.rename Nat.succ y
  let a : Formula := .eq (.mul xs (.add ys (.var 0)))
    (.add (.mul xs ys) (.mul xs (.var 0)))
  apply induction a
  · have hl := (add_zero y).eq_mul_right x
    have hr := ((mul_zero x).eq_add_right (.mul x y)).eq_trans (add_zero (.mul x y))
    have h := hl.eq_trans hr.eq_symm
    simpa only [Proves, a, xs, ys, Formula.subst, Term.subst, Formula.substZero,
      Formula.term_substZero_rename_succ] using h
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    have ih : Relative Formula.Ax_s [a] a :=
      relative_of_derives (.ass _ _ List.mem_cons_self)
    have hl : Relative Formula.Ax_s [a]
        (.eq (.mul xs (.add ys (.succ (.var 0))))
          (.add (.mul xs (.add ys (.var 0))) xs)) :=
      in_context (((add_succ ys (.var 0)).eq_mul_right xs).eq_trans
        (mul_succ xs (.add ys (.var 0))))
    have hr : Relative Formula.Ax_s [a]
        (.eq (.add (.add (.mul xs ys) (.mul xs (.var 0))) xs)
          (.add (.mul xs ys) (.mul xs (.succ (.var 0))))) :=
      in_context ((add_assoc (.mul xs ys) (.mul xs (.var 0)) xs).eq_trans
        ((mul_succ xs (.var 0)).eq_symm.eq_add_right (.mul xs ys)))
    have h := (hl.eq_trans (ih.eq_add_left xs)).eq_trans hr
    simpa only [Proves, List.map_nil, a, xs, ys, Formula.subst, Term.subst,
      Formula.substSuccVar, Formula.term_substSuccVar_rename_succ] using h

theorem mul_add (x y z : Term) : Proves (.eq
    (.mul x (.add y z)) (.add (.mul x y) (.mul x z))) := by
  have h := Relative.all_elim z (mul_add_all x y)
  simpa only [Proves, Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using h

/-- Distribution over a sum on the left, using only proved HA additive rearrangements. -/
theorem add_mul_all (x y : Term) : Proves (.all (.eq
    (.mul (.add (Term.rename Nat.succ x) (Term.rename Nat.succ y)) (.var 0))
    (.add (.mul (Term.rename Nat.succ x) (.var 0))
      (.mul (Term.rename Nat.succ y) (.var 0))))) := by
  let xs := Term.rename Nat.succ x
  let ys := Term.rename Nat.succ y
  let a : Formula := .eq (.mul (.add xs ys) (.var 0))
    (.add (.mul xs (.var 0)) (.mul ys (.var 0)))
  apply induction a
  · have hr := (((mul_zero x).eq_add_left (.mul y .zero)).eq_trans
      ((mul_zero y).eq_add_right .zero)).eq_trans (add_zero .zero)
    have h := (mul_zero (.add x y)).eq_trans hr.eq_symm
    simpa only [Proves, a, xs, ys, Formula.subst, Term.subst, Formula.substZero,
      Formula.term_substZero_rename_succ] using h
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    have ih : Relative Formula.Ax_s [a] a :=
      relative_of_derives (.ass _ _ List.mem_cons_self)
    have hl : Relative Formula.Ax_s [a]
        (.eq (.mul (.add xs ys) (.succ (.var 0)))
          (.add (.mul (.add xs ys) (.var 0)) (.add xs ys))) :=
      in_context (mul_succ (.add xs ys) (.var 0))
    have hm : Relative Formula.Ax_s [a]
        (.eq (.add (.add (.mul xs (.var 0)) (.mul ys (.var 0))) (.add xs ys))
          (.add (.add (.mul xs (.var 0)) xs) (.add (.mul ys (.var 0)) ys))) :=
      in_context (add_interchange (.mul xs (.var 0)) (.mul ys (.var 0)) xs ys)
    have hr : Relative Formula.Ax_s [a]
        (.eq (.add (.add (.mul xs (.var 0)) xs) (.add (.mul ys (.var 0)) ys))
          (.add (.mul xs (.succ (.var 0))) (.mul ys (.succ (.var 0))))) :=
      in_context (((mul_succ xs (.var 0)).eq_symm.eq_add_left
        (.add (.mul ys (.var 0)) ys)).eq_trans
          ((mul_succ ys (.var 0)).eq_symm.eq_add_right (.mul xs (.succ (.var 0)))))
    have h := ((hl.eq_trans (ih.eq_add_left (.add xs ys))).eq_trans hm).eq_trans hr
    simpa only [Proves, List.map_nil, a, xs, ys, Formula.subst, Term.subst,
      Formula.substSuccVar, Formula.term_substSuccVar_rename_succ] using h

theorem add_mul (x y z : Term) : Proves (.eq
    (.mul (.add x y) z) (.add (.mul x z) (.mul y z))) := by
  have h := Relative.all_elim z (add_mul_all x y)
  simpa only [Proves, Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using h

theorem succ_mul (x y : Term) : Proves (.eq
    (.mul (.succ x) y) (.add (.mul x y) y)) :=
  ((((add_one x).eq_mul_left y).eq_symm.eq_trans (add_mul x (.succ .zero) y)).eq_trans
    ((one_mul y).eq_add_right (.mul x y)))

theorem mul_comm_all (x : Term) : Proves (.all (.eq
    (.mul (Term.rename Nat.succ x) (.var 0))
    (.mul (.var 0) (Term.rename Nat.succ x)))) := by
  let xs := Term.rename Nat.succ x
  let a : Formula := .eq (.mul xs (.var 0)) (.mul (.var 0) xs)
  apply induction a
  · have h := (mul_zero x).eq_trans (zero_mul x).eq_symm
    simpa only [Proves, a, xs, Formula.subst, Term.subst, Formula.substZero,
      Formula.term_substZero_rename_succ] using h
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    have ih : Relative Formula.Ax_s [a] a :=
      relative_of_derives (.ass _ _ List.mem_cons_self)
    have hl : Relative Formula.Ax_s [a]
        (.eq (.mul xs (.succ (.var 0))) (.add (.mul xs (.var 0)) xs)) :=
      in_context (mul_succ xs (.var 0))
    have hr : Relative Formula.Ax_s [a]
        (.eq (.add (.mul (.var 0) xs) xs) (.mul (.succ (.var 0)) xs)) :=
      in_context (succ_mul (.var 0) xs).eq_symm
    have h := (hl.eq_trans (ih.eq_add_left xs)).eq_trans hr
    simpa only [Proves, List.map_nil, a, xs, Formula.subst, Term.subst,
      Formula.substSuccVar, Formula.term_substSuccVar_rename_succ] using h

theorem mul_comm (x y : Term) : Proves (.eq (.mul x y) (.mul y x)) := by
  have h := Relative.all_elim y (mul_comm_all x)
  simpa only [Proves, Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using h

theorem mul_assoc_all (x y : Term) : Proves (.all (.eq
    (.mul (.mul (Term.rename Nat.succ x) (Term.rename Nat.succ y)) (.var 0))
    (.mul (Term.rename Nat.succ x) (.mul (Term.rename Nat.succ y) (.var 0))))) := by
  let xs := Term.rename Nat.succ x
  let ys := Term.rename Nat.succ y
  let a : Formula := .eq (.mul (.mul xs ys) (.var 0)) (.mul xs (.mul ys (.var 0)))
  apply induction a
  · have hr := ((mul_zero y).eq_mul_right x).eq_trans (mul_zero x)
    have h := (mul_zero (.mul x y)).eq_trans hr.eq_symm
    simpa only [Proves, a, xs, ys, Formula.subst, Term.subst, Formula.substZero,
      Formula.term_substZero_rename_succ] using h
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    have ih : Relative Formula.Ax_s [a] a :=
      relative_of_derives (.ass _ _ List.mem_cons_self)
    have hl : Relative Formula.Ax_s [a]
        (.eq (.mul (.mul xs ys) (.succ (.var 0)))
          (.add (.mul (.mul xs ys) (.var 0)) (.mul xs ys))) :=
      in_context (mul_succ (.mul xs ys) (.var 0))
    have hr : Relative Formula.Ax_s [a]
        (.eq (.mul xs (.mul ys (.succ (.var 0))))
          (.add (.mul xs (.mul ys (.var 0))) (.mul xs ys))) :=
      in_context (((mul_succ ys (.var 0)).eq_mul_right xs).eq_trans
        (mul_add xs (.mul ys (.var 0)) ys))
    have h := (hl.eq_trans (ih.eq_add_left (.mul xs ys))).eq_trans hr.eq_symm
    simpa only [Proves, List.map_nil, a, xs, ys, Formula.subst, Term.subst,
      Formula.substSuccVar, Formula.term_substSuccVar_rename_succ] using h

theorem mul_assoc (x y z : Term) :
    Proves (.eq (.mul (.mul x y) z) (.mul x (.mul y z))) := by
  have h := Relative.all_elim z (mul_assoc_all x y)
  simpa only [Proves, Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using h

end DiophantineConsistency.HA.Arithmetic
