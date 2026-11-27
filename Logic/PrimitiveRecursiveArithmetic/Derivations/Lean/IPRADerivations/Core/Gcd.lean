import IPRADerivations.Core.Division
import IPRADerivations.Core.Signum
import IPRADerivations.Core.LinearCombination

/-!
# Divisibility and the Euclidean algorithm in iPRA

`dvd d x` is the quantifier-free formula `rem x d = 0`; it is used for `d = S d' ≥ 1`.
Derived:

* `dvd_iff`: `d ∣ x` exactly when `x = d w` for some term `w`, via `dvd_of_eq` and
  `eq_of_dvd`; closure under sums, multiples and differences;
* the Euclidean algorithm as a simultaneous recursion
  `(x₀, y₀) = (a, b)`, `(x_{k+1}, y_{k+1}) = (y_k, x_k mod y_k)` if `y_k ≠ 0`, unchanged
  otherwise, with `y_{b+1} = 0`;
* the gcd theorem for `g = gcd(a, b) = x_{b+1}`: every common divisor `d ≥ 1` of `a`
  and `b` divides `g`, and if `g ≥ 1` then `g` divides `a` and `b`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Divisibility -/

/-- `d ∣ x`. -/
abbrev dvd (d x : PTm n) : Fm PTm n := rem x d ≐ zero

/-- Shift a divisibility derivation into a context with one fresh variable. -/
theorem Gcd.shift_dvd {d x : PTm n} (h : Γ ⊢[PRAAx] dvd d x) :
    Γ.map Fm.shift ⊢[PRAAx] dvd (Syn.shift d) (Syn.shift x) := by
  simpa only [dvd, Syn.shift, subst_ap2, ConciseIPRA.PTm.subst_zero] using Order.shift_eq h

theorem dvd_of_eq {d' x w : PTm n} (h : Γ ⊢[PRAAx] x ≐ succ d' * w) : Γ ⊢[PRAAx] dvd (succ d') x :=
  Prf.andE₂ (div_mod_unique (h.eqTrans (add_zero _).eqSymm) (zero_lt_succ _))

theorem eq_of_dvd {d' x : PTm n} (h : Γ ⊢[PRAAx] dvd (succ d') x) :
    Γ ⊢[PRAAx] x ≐ succ d' * quo x (succ d') :=
  (Prf.andE₁ (div_mod x d')).eqTrans ((congrAdd (.eqRefl _) h).eqTrans (add_zero _))

theorem dvd_zero (d' : PTm n) : Γ ⊢[PRAAx] dvd (succ d') zero :=
  dvd_of_eq (w := zero) (mul_zero _).eqSymm

theorem dvd_self (d' : PTm n) : Γ ⊢[PRAAx] dvd (succ d') (succ d') :=
  dvd_of_eq (w := one) ((mul_comm _ _).eqTrans (one_mul _)).eqSymm

theorem dvd_add {d' x y : PTm n} (hx : Γ ⊢[PRAAx] dvd (succ d') x) (hy : Γ ⊢[PRAAx] dvd (succ d') y) :
    Γ ⊢[PRAAx] dvd (succ d') (x + y) := by
  refine dvd_of_eq (w := quo x (succ d') + quo y (succ d')) ?_
  refine withEq (eq_of_dvd hx) fun e₁ => withEq (eq_of_dvd hy) fun e₂ => ?_
  apply deriveNat; ipra_simps; rw [e₁, e₂]; ring

theorem dvd_mul {d' x : PTm n} (c : PTm n) (hx : Γ ⊢[PRAAx] dvd (succ d') x) :
    Γ ⊢[PRAAx] dvd (succ d') (x * c) := by
  refine dvd_of_eq (w := quo x (succ d') * c) ?_
  refine withEq (eq_of_dvd hx) fun e₁ => ?_
  apply deriveNat; ipra_simps; rw [e₁]; ring

theorem dvd_congr {d x x' : PTm n} (h : Γ ⊢[PRAAx] x ≐ x') (hx : Γ ⊢[PRAAx] dvd d x) :
    Γ ⊢[PRAAx] dvd d x' :=
  (congrAp2 remF h.eqSymm (.eqRefl d)).eqTrans hx

/-- Cancellation of a positive factor in `≤`. -/
theorem mul_le_cancel {d' a b : PTm n} (h : Γ ⊢[PRAAx] le (succ d' * a) (succ d' * b)) :
    Γ ⊢[PRAAx] le a b := by
  refine .orE (lt_or_le b a) ?_ Prf.hyp0
  have w := eq_add_of_le (Prf.hyp0 : (lt b a :: Γ) ⊢[PRAAx] le (succ b) a)
  refine not_succ_le_self (succ d' * b) _ (le_trans ?_ h.wk)
  refine le_of_eq_add (d := d' + succ d' * monus a (succ b)) ?_
  refine withEq w fun e => ?_
  apply deriveNat; ipra_simps; rw [e]; ring

/-- Cancel a factor known to be a successor. -/
theorem mul_le_cancel_at {d c a b : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ c)
    (h : Γ ⊢[PRAAx] le (d * a) (d * b)) : Γ ⊢[PRAAx] le a b :=
  mul_le_cancel (le_congr (congrMul hd (.eqRefl _)) (congrMul hd (.eqRefl _)) h)

/-- Cancel the same positive factor in an equality of products. -/
theorem mul_eq_cancel_at {d c a b : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ c)
    (h : Γ ⊢[PRAAx] d * a ≐ d * b) : Γ ⊢[PRAAx] a ≐ b :=
  le_antisymm (mul_le_cancel_at hd (le_congr (.eqRefl _) h (le_refl _)))
    (mul_le_cancel_at hd (le_congr (.eqRefl _) h.eqSymm (le_refl _)))

/-- `d ∣ x + y` and `d ∣ y` give `d ∣ x`. -/
theorem dvd_sub {d' x y : PTm n} (hxy : Γ ⊢[PRAAx] dvd (succ d') (x + y))
    (hy : Γ ⊢[PRAAx] dvd (succ d') y) : Γ ⊢[PRAAx] dvd (succ d') x := by
  have e₁ := eq_of_dvd hxy
  have e₂ := eq_of_dvd hy
  -- d t ≤ d s, so t ≤ s, and x = d (s − t).
  have hle : Γ ⊢[PRAAx] le (quo y (succ d')) (quo (x + y) (succ d')) := by
    refine mul_le_cancel (le_congr e₂ e₁ (le_add_left _ _))
  refine dvd_of_eq (w := monus (quo (x + y) (succ d')) (quo y (succ d'))) ?_
  refine add_right_cancel (c := y) ?_
  refine withEq e₁ fun f₁ => withEq e₂ fun f₂ => withEq (eq_add_of_le hle) fun f₃ => ?_
  ipra_lc f₁ - f₂ + (Groth.ι (Q.mk Γ d') + 1) * f₃

/-! ## The Euclidean algorithm -/

/-- Step variables: `0 = k`, `1 = x_k`, `2 = y_k`, `3 = a`, `4 = b`. -/
abbrev eStepX : PTm 5 := sg (var 2) * var 2 + monus one (sg (var 2)) * var 1
abbrev eStepY : PTm 5 := sg (var 2) * rem (var 1) (var 2)

/-- `x_k(a, b)` and `y_k(a, b)`. -/
abbrev ex (k : PTm n) (ps : Fin 2 → PTm n) : PTm n := sim₁ (var 0) (var 1) eStepX eStepY k ps
abbrev ey (k : PTm n) (ps : Fin 2 → PTm n) : PTm n := sim₂ (var 0) (var 1) eStepX eStepY k ps

theorem ex_succ (k : PTm n) (ps : Fin 2 → PTm n) :
    Γ ⊢[PRAAx] ex (succ k) ps ≐ sg (ey k ps) * ey k ps + monus one (sg (ey k ps)) * ex k ps := by
  have h := sim₁_succ (Γ := Γ) (var 0) (var 1) eStepX eStepY ps k
  simp only [PTm.subst_add, PTm.subst_mul, PTm.subst_monus, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, Syn.subst_var, Fin.cases_zero, finCases_one, finCases_two] at h
  exact h

theorem ey_succ (k : PTm n) (ps : Fin 2 → PTm n) :
    Γ ⊢[PRAAx] ey (succ k) ps ≐ sg (ey k ps) * rem (ex k ps) (ey k ps) := by
  have h := sim₂_succ (Γ := Γ) (var 0) (var 1) eStepX eStepY ps k
  simp only [PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, Syn.subst_var, Fin.cases_zero, finCases_one, finCases_two] at h
  exact h

/-- When `y_k = 0` the state is unchanged; when `y_k = S c`, it is `(y_k, x_k mod y_k)`. -/
theorem e_step_zero {k : PTm n} {ps : Fin 2 → PTm n} (h : Γ ⊢[PRAAx] ey k ps ≐ zero) :
    Γ ⊢[PRAAx] (ex (succ k) ps ≐ ex k ps) ⋏ (ey (succ k) ps ≐ zero) := by
  have hs : Γ ⊢[PRAAx] sg (ey k ps) ≐ zero :=
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)).eqTrans sg_zero
  refine .andI ((ex_succ k ps).eqTrans ?_) ((ey_succ k ps).eqTrans ?_)
  · refine (congrAdd (congrMul hs (.eqRefl _)) (congrMul ((congrMonus (.eqRefl _) hs).eqTrans
      (monus_zero _)) (.eqRefl _))).eqTrans ?_
    exact (congrAdd (zero_mul _) (one_mul _)).eqTrans (zero_add _)
  · exact (congrMul hs (.eqRefl _)).eqTrans (zero_mul _)

theorem e_step_succ {k c : PTm n} {ps : Fin 2 → PTm n} (h : Γ ⊢[PRAAx] ey k ps ≐ succ c) :
    Γ ⊢[PRAAx] (ex (succ k) ps ≐ ey k ps) ⋏ (ey (succ k) ps ≐ rem (ex k ps) (ey k ps)) := by
  have hs : Γ ⊢[PRAAx] sg (ey k ps) ≐ one :=
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)).eqTrans (sg_succ _)
  refine .andI ((ex_succ k ps).eqTrans ?_) ((ey_succ k ps).eqTrans ?_)
  · refine (congrAdd (congrMul hs (.eqRefl _)) (congrMul ((congrMonus (.eqRefl _) hs).eqTrans
      (monus_self _)) (.eqRefl _))).eqTrans ?_
    exact (congrAdd (one_mul _) (zero_mul _)).eqTrans (add_zero _)
  · exact (congrMul hs (.eqRefl _)).eqTrans (one_mul _)

@[simp] theorem subst_ex2 {m : ℕ} (σ : Fin n → PTm m) (k a b : PTm n) :
    Syn.subst σ (ex k ![a, b]) = ex (Syn.subst σ k) ![Syn.subst σ a, Syn.subst σ b] := by
  rw [subst_sim₁]; congr 1; funext i; fin_cases i <;> rfl

@[simp] theorem subst_ey2 {m : ℕ} (σ : Fin n → PTm m) (k a b : PTm n) :
    Syn.subst σ (ey k ![a, b]) = ey (Syn.subst σ k) ![Syn.subst σ a, Syn.subst σ b] := by
  rw [subst_sim₂]; congr 1; funext i; fin_cases i <;> rfl

theorem ex_zero (a b : PTm n) : Γ ⊢[PRAAx] ex zero ![a, b] ≐ a := by
  simpa using sim₁_zero (Γ := Γ) (var 0) (var 1) eStepX eStepY ![a, b]

theorem ey_zero (a b : PTm n) : Γ ⊢[PRAAx] ey zero ![a, b] ≐ b := by
  simpa using sim₂_zero (Γ := Γ) (var 0) (var 1) eStepX eStepY ![a, b]

/-! ## Common divisors are preserved -/

section Invariant

/-- Variables: `0 = k`, `1 = a`, `2 = b`, `3 = d'` with `d = S d'`. -/
abbrev X : PTm 4 := ex (var 0) ![var 1, var 2]
abbrev Y : PTm 4 := ey (var 0) ![var 1, var 2]
abbrev D : PTm 4 := succ (var 3)

abbrev commonInv : Fm PTm 4 :=
  ((dvd D (var 1) ⋏ dvd D (var 2)) ⟶ (dvd D X ⋏ dvd D Y)) ⋏
    ((dvd D X ⋏ dvd D Y) ⟶ (dvd D (var 1) ⋏ dvd D (var 2)))

private abbrev X' : PTm 4 := ex (succ (var 0)) ![var 1, var 2]
private abbrev Y' : PTm 4 := ey (succ (var 0)) ![var 1, var 2]

theorem common_invariant : ([] : List (Fm PTm 4)) ⊢[PRAAx] commonInv := by
  ipra_ind (⟨⟨⟨trivial, trivial⟩, trivial, trivial⟩, ⟨trivial, trivial⟩, trivial, trivial⟩) [subst_ap2, subst_ex2,
      subst_ey2]
  · refine .andI (.impI (.andI ?_ ?_)) (.impI (.andI ?_ ?_))
    · exact dvd_congr (ex_zero _ _).eqSymm (Prf.andE₁ Prf.hyp0)
    · exact dvd_congr (ey_zero _ _).eqSymm (Prf.andE₂ Prf.hyp0)
    · exact dvd_congr (ex_zero _ _) (Prf.andE₁ Prf.hyp0)
    · exact dvd_congr (ey_zero _ _) (Prf.andE₂ Prf.hyp0)
  · have hF : [commonInv] ⊢[PRAAx] (dvd D (var 1) ⋏ dvd D (var 2)) ⟶ (dvd D X ⋏ dvd D Y) :=
      .andE₁ Prf.hyp0
    have hB : [commonInv] ⊢[PRAAx] (dvd D X ⋏ dvd D Y) ⟶ (dvd D (var 1) ⋏ dvd D (var 2)) :=
      .andE₂ Prf.hyp0
    refine .orE (zero_or_succ Y) ?_ ?_
    · -- y_k = 0: the state is unchanged.
      have hs := e_step_zero (Γ := (Y ≐ zero) :: [commonInv]) Prf.hyp0
      refine .andI (.impI (.andI ?_ ?_)) (.impI (.andI ?_ ?_))
      · exact dvd_congr (Prf.andE₁ hs.wk).eqSymm (Prf.andE₁ (.impE hF.wk.wk Prf.hyp0))
      · exact dvd_congr (Prf.andE₂ hs.wk).eqSymm (dvd_zero _)
      · refine Prf.andE₁ (.impE hB.wk.wk (.andI ?_ ?_))
        · exact dvd_congr (Prf.andE₁ hs.wk) (Prf.andE₁ Prf.hyp0)
        · exact dvd_congr Prf.hyp1.eqSymm (dvd_zero _)
      · refine Prf.andE₂ (.impE hB.wk.wk (.andI ?_ ?_))
        · exact dvd_congr (Prf.andE₁ hs.wk) (Prf.andE₁ Prf.hyp0)
        · exact dvd_congr Prf.hyp1.eqSymm (dvd_zero _)
    · -- y_k = S c: the state becomes (y_k, x_k mod y_k).
      have hs := e_step_succ (Γ := (Y ≐ succ (pred Y)) :: [commonInv]) Prf.hyp0
      have hd := div_mod_at (x := X) (Γ := (Y ≐ succ (pred Y)) :: [commonInv]) Prf.hyp0
      -- x = r + y q.
      have hx : ((Y ≐ succ (pred Y)) :: [commonInv]) ⊢[PRAAx] rem X Y + Y * quo X Y ≐ X :=
        (add_comm _ _).eqTrans (Prf.andE₁ hd).eqSymm
      refine .andI (.impI ?_) (.impI ?_)
      · have h : ((dvd D (var 1) ⋏ dvd D (var 2)) :: (Y ≐ succ (pred Y)) :: [commonInv]) ⊢[PRAAx]
            dvd D X ⋏ dvd D Y := Prf.impE hF.wk.wk Prf.hyp0
        refine .andI (dvd_congr (Prf.andE₁ hs.wk).eqSymm (Prf.andE₂ h)) ?_
        refine dvd_congr (Prf.andE₂ hs.wk).eqSymm (dvd_sub (y := Y * quo X Y) ?_ (dvd_mul _ (Prf.andE₂ h)))
        exact dvd_congr hx.wk.eqSymm (Prf.andE₁ h)
      · have hy : ((dvd D X' ⋏ dvd D Y') :: (Y ≐ succ (pred Y)) :: [commonInv]) ⊢[PRAAx] dvd D Y :=
          dvd_congr (Prf.andE₁ hs.wk) (Prf.andE₁ Prf.hyp0)
        have hr : ((dvd D X' ⋏ dvd D Y') :: (Y ≐ succ (pred Y)) :: [commonInv]) ⊢[PRAAx]
            dvd D (rem X Y) := dvd_congr (Prf.andE₂ hs.wk) (Prf.andE₂ Prf.hyp0)
        refine .impE hB.wk.wk (.andI ?_ hy)
        exact dvd_congr hx.wk (dvd_add hr (dvd_mul _ hy))

end Invariant

/-! ## Termination and the gcd theorem -/

section GcdTheorem

/-- Variables: `0 = k`, `1 = a`, `2 = b`. -/
abbrev Y₃ : PTm 3 := ey (var 0) ![var 1, var 2]

abbrev terminationInv : Fm PTm 3 := (Y₃ ≐ zero) ⋎ le (Y₃ + var 0) (var 2)

theorem termination_invariant : ([] : List (Fm PTm 3)) ⊢[PRAAx] terminationInv := by
  ipra_ind (⟨trivial, le_QF _ _⟩) [subst_le, subst_ey2]
  · exact .orI₂ (le_congr ((ey_zero _ _).eqSymm.eqTrans (add_zero _).eqSymm) (.eqRefl _) (le_refl _))
  · refine .orE (zero_or_succ Y₃) ?_ ?_
    · exact .orI₁ (Prf.andE₂ (e_step_zero Prf.hyp0))
    · have hs := e_step_succ (Γ := (Y₃ ≐ succ (pred Y₃)) :: [terminationInv]) Prf.hyp0
      have hd := div_mod_at (x := ex (var 0) ![var 1, var 2])
        (Γ := (Y₃ ≐ succ (pred Y₃)) :: [terminationInv]) Prf.hyp0
      refine .orE (Prf.hyp1 : ((Y₃ ≐ succ (pred Y₃)) :: [terminationInv]) ⊢[PRAAx] terminationInv) ?_ ?_
      · exact .botE _ (succ_ne_zero (a := pred Y₃) (Prf.hyp1.eqSymm.eqTrans Prf.hyp0))
      · refine .orI₂ (le_trans ?_ Prf.hyp0)
        refine le_congr ?_ (.eqRefl _) (add_le_add_right (var 0) (Prf.andE₂ hd).wk)
        exact (succ_add _ _).eqTrans ((add_succ _ _).eqSymm.eqTrans
          (congrAdd (Prf.andE₂ hs.wk).eqSymm (.eqRefl _)))

/-- `y_{b+1} = 0`: the algorithm stops within `b + 1` steps. Variables `0 = a`, `1 = b`. -/
theorem euclid_terminates :
    ([] : List (Fm PTm 2)) ⊢[PRAAx] ey (succ (var 1)) ![var 0, var 1] ≐ zero := by
  have h := inst (Γ := ([] : List (Fm PTm 2))) termination_invariant
    (![succ (var 1), var 0, var 1] : Fin 3 → PTm 2)
  simp only [Fm.subst_or, Fm.subst_eq, subst_le, PTm.subst_add, subst_ey2, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, ConciseIPRA.PTm.subst_zero] at h
  refine .orE h Prf.hyp0 ?_
  exact not_succ_le_self _ _ (le_trans (le_add_left _ _) Prf.hyp0)

/-- `gcd(a, b) = x_{b+1}`. -/
abbrev gcd (a b : PTm n) : PTm n := ex (succ b) ![a, b]

/-- Shift a derivation of coprimality into a context with one fresh variable. -/
theorem Gcd.shift_coprime {a b : PTm n} (h : Γ ⊢[PRAAx] gcd a b ≐ one) :
    Γ.map Fm.shift ⊢[PRAAx] gcd (Syn.shift a) (Syn.shift b) ≐ one := by
  simpa only [Syn.shift, subst_ex2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    using Order.shift_eq h

/-- Every common divisor `d = S d'` of `a` and `b` divides `gcd(a, b)`.
Variables `0 = a`, `1 = b`, `2 = d'`. -/
abbrev gcdGreatestFormula : Fm PTm 3 :=
  (dvd (succ (var 2)) (var 0) ⋏ dvd (succ (var 2)) (var 1)) ⟶ dvd (succ (var 2)) (gcd (var 0) (var 1))

theorem gcd_greatest : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 gcdGreatestFormula := by
  refine closeUniv 3 (.impI ?_)
  have h := inst (Γ := [dvd (succ (var 2)) (var 0) ⋏ dvd (succ (var 2)) (var 1)]) common_invariant
    (![succ (var 1), var 0, var 1, var 2] : Fin 4 → PTm 3)
  simp only [Fm.subst_and, Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_ex2, subst_ey2,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] at h
  exact Prf.andE₁ (.impE (Prf.andE₁ h) Prf.hyp0)

/-- If `gcd(a, b) ≥ 1` then it divides `a` and `b`. Variables `0 = a`, `1 = b`. -/
abbrev gcdDividesFormula : Fm PTm 2 :=
  (gcd (var 0) (var 1) ≐ succ (pred (gcd (var 0) (var 1)))) ⟶
    (dvd (gcd (var 0) (var 1)) (var 0) ⋏ dvd (gcd (var 0) (var 1)) (var 1))

theorem gcd_dvd : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 gcdDividesFormula := by
  refine closeUniv 2 (.impI ?_)
  have hg : ([gcd (var 0) (var 1) ≐ succ (pred (gcd (var 0) (var 1)))] : List (Fm PTm 2)) ⊢[PRAAx]
      gcd (var 0) (var 1) ≐ succ (pred (gcd (var 0) (var 1))) := Prf.hyp0
  have h := inst (Γ := [gcd (var 0) (var 1) ≐ succ (pred (gcd (var 0) (var 1)))]) common_invariant
    (![succ (var 1), var 0, var 1, pred (gcd (var 0) (var 1))] : Fin 4 → PTm 2)
  simp only [Fm.subst_and, Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_ex2, subst_ey2,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] at h
  -- The hypotheses of the backward direction: d ∣ g and d ∣ y_{b+1} = 0, with d = S (pred g).
  have hX := dvd_congr hg.eqSymm (dvd_self (Γ := [gcd (var 0) (var 1) ≐ succ (pred (gcd (var 0) (var 1)))])
    (pred (gcd (var 0) (var 1))))
  have hY := dvd_congr (euclid_terminates.ofNil).eqSymm
    (dvd_zero (Γ := [gcd (var 0) (var 1) ≐ succ (pred (gcd (var 0) (var 1)))])
      (pred (gcd (var 0) (var 1))))
  have hab := Prf.impE (Prf.andE₂ h) (.andI hX hY)
  -- Replace the divisor S (pred g) by g.
  exact .andI ((congrAp2 remF (.eqRefl _) hg).eqTrans (Prf.andE₁ hab))
    ((congrAp2 remF (.eqRefl _) hg).eqTrans (Prf.andE₂ hab))

end GcdTheorem

end LeanProofs.IPRA
