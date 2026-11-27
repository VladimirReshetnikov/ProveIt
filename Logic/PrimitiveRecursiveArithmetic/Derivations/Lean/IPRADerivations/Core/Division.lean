import IPRADerivations.Core.Pairing

/-!
# Division with remainder in iPRA

For a divisor `K`, the remainder and the quotient are defined by recursion on the
dividend:
`rem 0 K = 0`, `rem (z + 1) K = (rem z K + 1) (1 ∸ eqb (rem z K + 1) K)`, and
`quo 0 K = 0`, `quo (z + 1) K = quo z K + eqb (rem z K + 1) K`.
Derived, for `K ≥ 1` (written `K = S K'`):

* `div_mod`: `z = K quo z + rem z` and `rem z < K`, by induction on `z`;
* `euclid_unique`: `Kq + r = Kq' + r'` with `r, r' < K` gives `q = q'` and `r = r'`;
* `div_mod_unique`: `z = Kq + r` with `r < K` gives `quo z = q` and `rem z = r`;
* `Division.mul_quo_le` and `Division.lt_mul_succ_quo` bound the dividend by consecutive multiples.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The remainder step; variables `0 = z`, `1 = rem z K`, `2 = K`. -/
abbrev remStep : PTm 3 := succ (var 1) * monus one (eqb (succ (var 1)) (var 2))
abbrev remF : PR 2 := rec2 zero remStep
/-- `z mod K`. -/
abbrev rem (z K : PTm n) : PTm n := ap2 remF z K

/-- The quotient step; variables `0 = z`, `1 = quo z K`, `2 = K`. -/
abbrev quoStep : PTm 3 := var 1 + eqb (succ (rem (var 0) (var 2))) (var 2)
abbrev quoF : PR 2 := rec2 zero quoStep
/-- `z div K`. -/
abbrev quo (z K : PTm n) : PTm n := ap2 quoF z K

theorem rem_zero (K : PTm n) : Γ ⊢[PRAAx] rem zero K ≐ zero := by
  simpa using rec2_zero (Γ := Γ) zero remStep K

theorem rem_succ (z K : PTm n) :
    Γ ⊢[PRAAx] rem (succ z) K ≐ succ (rem z K) * monus one (eqb (succ (rem z K)) K) := by
  have h := rec2_succ (Γ := Γ) zero remStep z K
  simp only [PTm.subst_mul, PTm.subst_monus, subst_eqb, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, Syn.subst_var, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h
  exact h

theorem quo_zero (K : PTm n) : Γ ⊢[PRAAx] quo zero K ≐ zero := by
  simpa using rec2_zero (Γ := Γ) zero quoStep K

theorem quo_succ (z K : PTm n) :
    Γ ⊢[PRAAx] quo (succ z) K ≐ quo z K + eqb (succ (rem z K)) K := by
  have h := rec2_succ (Γ := Γ) zero quoStep z K
  simp only [PTm.subst_add, subst_eqb, subst_ap2, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at h
  exact h

/-- `0 < S K'`. -/
theorem zero_lt_succ (K' : PTm n) : Γ ⊢[PRAAx] lt zero (succ K') :=
  (succ_monus_succ _ _).eqTrans (zero_monus _)

/-! ## Existence -/

/-- The invariant; variables `0 = z`, `1 = K'`, with `K = S K'`. -/
abbrev divModF : Fm PTm 2 :=
  (var 0 ≐ succ (var 1) * quo (var 0) (succ (var 1)) + rem (var 0) (succ (var 1))) ⋏
    lt (rem (var 0) (succ (var 1))) (succ (var 1))

private abbrev Kv : PTm 2 := succ (var 1)
private abbrev Rv : PTm 2 := rem (var 0) (succ (var 1))
private abbrev Qv : PTm 2 := quo (var 0) (succ (var 1))

private theorem div_mod₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] divModF := by
  ipra_ind (⟨trivial, lt_QF _ _⟩) [subst_lt, subst_ap2]
  · refine .andI ?_ (lt_congr (rem_zero _).eqSymm (.eqRefl _) (zero_lt_succ _))
    refine withEq (rem_zero (Γ := ([] : List (Fm PTm 1))) (succ (var 0))) fun e₁ => ?_
    refine withEq (quo_zero (Γ := ([] : List (Fm PTm 1))) (succ (var 0))) fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂]; ring
  · have hz : [divModF] ⊢[PRAAx] var 0 ≐ Kv * Qv + Rv := .andE₁ Prf.hyp0
    have hr : [divModF] ⊢[PRAAx] lt Rv Kv := .andE₂ Prf.hyp0
    have hR := rem_succ (Γ := [divModF]) (var 0) Kv
    have hQ := quo_succ (Γ := [divModF]) (var 0) Kv
    refine .orE (eq_or_ne (succ Rv) Kv) ?_ ?_
    · -- S r = K: the remainder wraps to 0 and the quotient increases.
      have e₀ : ((succ Rv ≐ Kv) :: [divModF]) ⊢[PRAAx] rem (succ (var 0)) Kv ≐ zero :=
        hR.wk.eqTrans ((congrMul (.eqRefl _) ((congrMonus (.eqRefl _) (eqb_of_eq Prf.hyp0)).eqTrans
          (monus_self _))).eqTrans (mul_zero _))
      have e₁ : ((succ Rv ≐ Kv) :: [divModF]) ⊢[PRAAx] quo (succ (var 0)) Kv ≐ Qv + one :=
        hQ.wk.eqTrans (congrAdd (.eqRefl _) (eqb_of_eq Prf.hyp0))
      refine .andI ?_ (lt_congr e₀.eqSymm (.eqRefl _) (zero_lt_succ _))
      refine withEq hz.wk fun f₁ => withEq Prf.hyp0 fun f₂ => withEq e₀ fun f₃ => withEq e₁ fun f₄ => ?_
      apply deriveNat; ipra_simps; rw [f₃, f₄]; linear_combination f₁ + f₂
    · -- S r ≠ K: the remainder increases.
      have e₀ : ((neg (succ Rv ≐ Kv)) :: [divModF]) ⊢[PRAAx] rem (succ (var 0)) Kv ≐ succ Rv :=
        hR.wk.eqTrans ((congrMul (.eqRefl _) ((congrMonus (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans
          (monus_zero _))).eqTrans ((mul_comm _ _).eqTrans (one_mul _)))
      have e₁ : ((neg (succ Rv ≐ Kv)) :: [divModF]) ⊢[PRAAx] quo (succ (var 0)) Kv ≐ Qv :=
        hQ.wk.eqTrans ((congrAdd (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (add_zero _))
      refine .andI ?_ ?_
      · refine withEq hz.wk fun f₁ => withEq e₀ fun f₃ => withEq e₁ fun f₄ => ?_
        apply deriveNat; ipra_simps; rw [f₃, f₄]; linear_combination f₁
      · refine lt_congr e₀.eqSymm (.eqRefl _) ?_
        refine .orE (lt_or_eq_of_le (hr.wk : _ ⊢[PRAAx] le (succ Rv) Kv)) Prf.hyp0 ?_
        exact .botE _ (.impE Prf.hyp1 Prf.hyp0)

/-- `z = K quo z + rem z` and `rem z < K`, for `K = S K'`. -/
theorem div_mod (z K' : PTm n) :
    Γ ⊢[PRAAx] (z ≐ succ K' * quo z (succ K') + rem z (succ K')) ⋏ lt (rem z (succ K')) (succ K') := by
  have h := inst (Γ := Γ) div_mod₀ (![z, K'] : Fin 2 → PTm n)
  simpa using h

/-- `x = y quo x y + rem x y` and `rem x y < y`, for `y = S c`. -/
theorem div_mod_at {x y c : PTm n} (hy : Γ ⊢[PRAAx] y ≐ succ c) :
    Γ ⊢[PRAAx] (x ≐ y * quo x y + rem x y) ⋏ lt (rem x y) y := by
  have d := div_mod (Γ := Γ) x c
  have hq : Γ ⊢[PRAAx] quo x (succ c) ≐ quo x y := congrAp2 quoF (.eqRefl _) hy.eqSymm
  have hr : Γ ⊢[PRAAx] rem x (succ c) ≐ rem x y := congrAp2 remF (.eqRefl _) hy.eqSymm
  refine .andI ((Prf.andE₁ d).eqTrans (congrAdd (congrMul hy.eqSymm hq) hr)) ?_
  exact lt_congr hr hy.eqSymm (Prf.andE₂ d)

/-! ## Uniqueness -/

theorem euclid_unique {K q q' r r' : PTm n} (h : Γ ⊢[PRAAx] K * q + r ≐ K * q' + r')
    (hr : Γ ⊢[PRAAx] lt r K) (hr' : Γ ⊢[PRAAx] lt r' K) :
    Γ ⊢[PRAAx] (q ≐ q') ⋏ (r ≐ r') := by
  -- From q < q' derive K ≤ r, contradicting r < K.
  have key : ∀ {Δ : List (Fm PTm n)} {q₁ q₂ r₁ r₂ : PTm n}, (Δ ⊢[PRAAx] K * q₁ + r₁ ≐ K * q₂ + r₂) →
      (Δ ⊢[PRAAx] lt r₁ K) → (Δ ⊢[PRAAx] lt q₁ q₂) → (Δ ⊢[PRAAx] Fm.bot) := by
    intro Δ q₁ q₂ r₁ r₂ he h₁ hq
    refine le_lt_absurd _ (a := K) (b := r₁) ?_ h₁
    have w := eq_add_of_le hq
    refine le_of_eq_add (d := K * monus q₂ (succ q₁) + r₂) ?_
    refine add_left_cancel (a := K * q₁) ?_
    refine withEq he fun e₁ => withEq w fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₂] at e₁; linear_combination e₁
  have hq : Γ ⊢[PRAAx] q ≐ q' := by
    refine .orE (lt_or_le q q') (.botE _ (key h.wk hr.wk Prf.hyp0)) ?_
    refine .orE (lt_or_le q' q) (.botE _ (key h.wk.wk.eqSymm hr'.wk.wk Prf.hyp0)) ?_
    exact le_antisymm Prf.hyp0 Prf.hyp1
  refine .andI hq (add_left_cancel (a := K * q) (h.eqTrans (congrAdd (congrMul (.eqRefl _) hq.eqSymm)
    (.eqRefl _))))

/-- Uniqueness at a divisor known to be a successor. -/
theorem div_mod_unique_at {x d c q r : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ c)
    (hx : Γ ⊢[PRAAx] x ≐ d * q + r) (hr : Γ ⊢[PRAAx] lt r d) :
    Γ ⊢[PRAAx] (quo x d ≐ q) ⋏ (rem x d ≐ r) := by
  have div := div_mod_at (x := x) hd
  exact euclid_unique ((Prf.andE₁ div).eqSymm.eqTrans hx) (Prf.andE₂ div) hr

/-- `z = Kq + r` with `r < K` gives `quo z = q` and `rem z = r`, for `K = S K'`. -/
theorem div_mod_unique {z q r K' : PTm n} (hz : Γ ⊢[PRAAx] z ≐ succ K' * q + r)
    (hr : Γ ⊢[PRAAx] lt r (succ K')) :
    Γ ⊢[PRAAx] (quo z (succ K') ≐ q) ⋏ (rem z (succ K') ≐ r) :=
  div_mod_unique_at (.eqRefl _) hz hr

/-! ## Order bounds for the quotient -/

namespace Division

/-- The multiple selected by division is at most the dividend. -/
theorem mul_quo_le {x d c : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ c) :
    Γ ⊢[PRAAx] le (d * quo x d) x :=
  le_of_eq_add (Prf.andE₁ (div_mod_at hd))

theorem quo_mul_le {x d c : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ c) :
    Γ ⊢[PRAAx] le (quo x d * d) x :=
  le_congr (mul_comm _ _) (.eqRefl _) (mul_quo_le hd)

/-- The next multiple is strictly above the dividend. -/
theorem lt_mul_succ_quo {x d c : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ c) :
    Γ ⊢[PRAAx] lt x (d * succ (quo x d)) := by
  have div := div_mod_at (x := x) hd
  have shift := (congrSucc (Prf.andE₁ div)).eqTrans (add_succ _ _).eqSymm
  exact le_congr shift.eqSymm (mul_succ _ _).eqSymm (add_le_add_left _ (Prf.andE₂ div))

theorem le_quo_of_mul_le {x d c q : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ c)
    (h : Γ ⊢[PRAAx] le (d * q) x) : Γ ⊢[PRAAx] le q (quo x d) := by
  refine .orE (lt_or_le (quo x d) q) ?_ Prf.hyp0
  exact le_lt_absurd _ h.wk (lt_of_lt_of_le (lt_mul_succ_quo hd.wk) (mul_le_mul_left d Prf.hyp0))

theorem quo_lt_of_lt_mul {x d c q : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ c)
    (h : Γ ⊢[PRAAx] lt x (d * q)) : Γ ⊢[PRAAx] lt (quo x d) q := by
  refine .orE (lt_or_le (quo x d) q) Prf.hyp0 ?_
  exact le_lt_absurd _ (le_trans (mul_le_mul_left d Prf.hyp0) (mul_quo_le hd.wk)) h.wk

theorem quo_mono {x y d c : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ c) (h : Γ ⊢[PRAAx] le x y) :
    Γ ⊢[PRAAx] le (quo x d) (quo y d) :=
  le_quo_of_mul_le hd (le_trans (mul_quo_le hd) h)

theorem quo_le_self {x d c : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ c) :
    Γ ⊢[PRAAx] le (quo x d) x := by
  have hd1 := lt_congr (.eqRefl _) hd.eqSymm (zero_lt_succ c)
  exact le_trans (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (quo x d) hd1)) (mul_quo_le hd)

theorem quo_eq_mul {x d c q : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ c)
    (h : Γ ⊢[PRAAx] x ≐ d * q) : Γ ⊢[PRAAx] quo x d ≐ q :=
  Prf.andE₁ (div_mod_unique_at hd (h.eqTrans (add_zero _).eqSymm)
    (lt_congr (.eqRefl _) hd.eqSymm (zero_lt_succ c)))

end Division

end LeanProofs.IPRA
