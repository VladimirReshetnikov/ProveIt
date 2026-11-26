import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Signum
import IPRADerivations.Core.LinearCombination

/-!
# `X³ − 2` has no rational root (`three_impossibilities_ipra`)

The packet's first impossibility (`three_classical_impossibilities_ipra.tex`) is
that `X³ − 2` has no rational root; the doubling of the cube is impossible.
Clearing denominators and signs, this is the iPRA theorem

  `a³ = 2b³ → b = 0`  for natural numbers `a, b`,

derived here by 2-adic infinite descent. A solution with `b ≠ 0` makes `a` even,
then `b` even, and halving both gives a smaller solution. Inside quantifier-free
iPRA the descent is an induction on `N` for the statement `T(N) = 0`, where
`T(N) = ∑_{b<N} ∑_{a≤2b} [a³ = 2b³ ∧ b ≠ 0]` counts the solutions with `b < N`
(`a ≤ 2b` holds for every solution); the sums play the role of bounded
quantifiers (`Core.BoundedSums`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.CubeRootTwo

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Auxiliary lemmas -/

/-- `x³`. -/
abbrev cube (x : PTm n) : PTm n := x * x * x

/-- `sg x = 1 ∸ (1 ∸ x)`: `0` at `0` and `1` at successors. -/
abbrev sg (x : PTm n) : PTm n := LeanProofs.IPRA.Signum.sg x

theorem sg_zero : Γ ⊢[PRAAx] sg (zero : PTm n) ≐ zero :=
  LeanProofs.IPRA.Signum.sg_zero

theorem sg_succ (x : PTm n) : Γ ⊢[PRAAx] sg (succ x) ≐ one :=
  LeanProofs.IPRA.Signum.sg_succ x

/-- `2X = 2Y → X = Y`. -/
theorem double_cancel {x y : PTm n} (h : Γ ⊢[PRAAx] two * x ≐ two * y) : Γ ⊢[PRAAx] x ≐ y := by
  have key : ∀ {Δ : List (Fm PTm n)} {u v : PTm n}, (Δ ⊢[PRAAx] two * u ≐ two * v) →
      (Δ ⊢[PRAAx] le u v) → (Δ ⊢[PRAAx] u ≐ v) := by
    intro Δ u v h hle
    have w := eq_add_of_le hle
    -- 2v = 2u + 2d, so 2d = 0 and d = 0.
    have e : Δ ⊢[PRAAx] two * u + zero ≐ two * u + (monus v u + monus v u) := by
      refine withEq h fun e₁ => withEq w fun e₂ => ?_
      ipra_lc e₁ + 2 * e₂
    have hd := add_eq_zero_left (add_left_cancel e).eqSymm
    exact ((add_zero u).eqSymm.eqTrans (congrAdd (.eqRefl u) hd).eqSymm).eqTrans w.eqSymm
  refine .orE (le_total x y) (key h.wk Prf.hyp0) ?_
  exact (key h.wk.eqSymm Prf.hyp0).eqSymm

theorem cube_le_cube {x y : PTm n} (h : Γ ⊢[PRAAx] le x y) : Γ ⊢[PRAAx] le (cube x) (cube y) := by
  refine le_trans (mul_le_mul_right x (sq_le_sq h)) ?_
  refine le_congr ?_ ?_ (mul_le_mul_right (y * y) h)
  · exact mul_comm _ _
  · exact mul_comm _ _

/-- `a³ = 2b³` gives `a ≤ 2b`. -/
theorem cube_bound {a b : PTm n} (h : Γ ⊢[PRAAx] cube a ≐ two * cube b) :
    Γ ⊢[PRAAx] le a (two * b) := by
  refine .orE (lt_or_le (two * b) a) ?_ Prf.hyp0
  -- (2b + 1)³ ≤ a³ = 2b³, but (2b + 1)³ = S (2b³) + K.
  have hc := cube_le_cube (Prf.hyp0 : (lt (two * b) a :: Γ) ⊢[PRAAx] le (succ (two * b)) a)
  refine not_succ_le_self (two * cube b) _ (le_trans (le_of_eq_add
    (d := num 6 * cube b + num 12 * (b * b) + num 6 * b) ?_) (le_congr (.eqRefl _) h.wk hc))
  ipra_ring

theorem lt_succ_of_le {i M : PTm n} (h : Γ ⊢[PRAAx] le i M) : Γ ⊢[PRAAx] lt i (succ M) :=
  (succ_monus_succ i M).eqTrans h

/-! ## The counting sums -/

/-- `bad(a, b) = [a³ = 2b³] · [b ≠ 0]`; variables `0 = a`, `1 = b`. -/
abbrev badBody : PTm 2 := eqb (cube (var 0)) (two * cube (var 1)) * sg (var 1)

/-- `inner(M, b) = ∑_{a<M} bad(a, b)`. -/
abbrev innerF : PR 2 := sumF badBody

/-- The outer body `inner(2b + 1, b)`; variables `0 = b`, `1` unused. -/
abbrev outerBody : PTm 2 := ap2 innerF (succ (two * var 0)) (var 0)

abbrev outerF : PR 2 := sumF outerBody

/-- `T(N) = ∑_{b<N} ∑_{a<2b+1} bad(a, b)`. -/
abbrev T (N : PTm n) : PTm n := ap2 outerF N zero

theorem inst2_bad (a b : PTm n) :
    inst2 badBody a b = eqb (cube a) (two * cube b) * sg b := by
  simp [inst2, badBody]

theorem inst2_outer (b x : PTm n) : inst2 outerBody b x = ap2 innerF (succ (two * b)) b := by
  simp [inst2, outerBody]

/-! ## The descent -/

/-- The context of the induction step, over the variables `0 = a`, `1 = N`. -/
abbrev Λ : List (Fm PTm 2) := [T (var 1) ≐ zero]

/-- In the context `T(N) = 0`: `bad(a, N) = 0`. -/
theorem bad_zero : Λ ⊢[PRAAx] inst2 badBody (var 0) (var 1) ≐ zero := by
  rw [inst2_bad]
  refine .orE (eq_or_ne (cube (var 0)) (two * cube (var 1))) ?_ ?_
  swap
  · exact (congrMul (eqb_of_ne Prf.hyp0) (.eqRefl _)).eqTrans (zero_mul _)
  -- a³ = 2N³.
  refine .orE (zero_or_succ (var 1)) ?_ ?_
  · exact (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans
      sg_zero)).eqTrans (mul_zero _)
  refine .botE _ ?_
  -- Context: N = S N₀, a³ = 2N³, T(N) = 0.
  have hE : ((var 1 ≐ succ (pred (var 1))) :: (cube (var 0) ≐ two * cube (var 1)) :: Λ) ⊢[PRAAx]
      cube (var 0) ≐ two * cube (var 1) := Prf.hyp1
  have hT : ((var 1 ≐ succ (pred (var 1))) :: (cube (var 0) ≐ two * cube (var 1)) :: Λ) ⊢[PRAAx]
      T (var 1) ≐ zero := hyp2
  have hN : ((var 1 ≐ succ (pred (var 1))) :: (cube (var 0) ≐ two * cube (var 1)) :: Λ) ⊢[PRAAx]
      var 1 ≐ succ (pred (var 1)) := Prf.hyp0
  -- a is even.
  refine .orE (even_or_odd (var 0)) ?_ ?_
  swap
  · refine even_ne_odd (k := cube (var 1))
      (m := num 4 * cube (half (var 0)) + num 6 * (half (var 0) * half (var 0)) +
        num 3 * half (var 0)) _ ?_
    refine withEq hE.wk fun e₁ => withEq Prf.hyp0 fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [← e₁, e₂]; ring
  -- a = 2h, so N³ = 4h³.
  have hN3 : ((var 0 ≐ two * half (var 0)) :: (var 1 ≐ succ (pred (var 1))) ::
      (cube (var 0) ≐ two * cube (var 1)) :: Λ) ⊢[PRAAx]
      cube (var 1) ≐ two * (two * cube (half (var 0))) := by
    refine double_cancel ?_
    refine withEq hE.wk fun e₁ => withEq Prf.hyp0 fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [← e₁, e₂]; ring
  -- N is even.
  refine .orE (even_or_odd (var 1)) ?_ ?_
  swap
  · refine even_ne_odd (k := two * cube (half (var 0)))
      (m := num 4 * cube (half (var 1)) + num 6 * (half (var 1) * half (var 1)) +
        num 3 * half (var 1)) _ ?_
    refine withEq hN3.wk fun e₁ => withEq Prf.hyp0 fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [← e₁, e₂]; ring
  -- N = 2g; then h³ = 2g³.
  have hhg : ((var 1 ≐ two * half (var 1)) :: (var 0 ≐ two * half (var 0)) ::
      (var 1 ≐ succ (pred (var 1))) :: (cube (var 0) ≐ two * cube (var 1)) :: Λ) ⊢[PRAAx]
      cube (half (var 0)) ≐ two * cube (half (var 1)) := by
    refine double_cancel (double_cancel ?_)
    refine withEq hN3.wk fun e₁ => withEq Prf.hyp0 fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₂] at e₁; linear_combination -e₁
  -- g ≠ 0, since N ≠ 0.
  refine .orE (zero_or_succ (half (var 1))) ?_ ?_
  · refine succ_ne_zero' _ (a := pred (var 1)) ?_
    exact (hN.wk.wk.wk.eqSymm).eqTrans
      (Prf.hyp1.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)))
  -- g < N and h ≤ 2g, so bad(h, g) is counted in T(N) = 0; but bad(h, g) = 1.
  have hg : ((half (var 1) ≐ succ (pred (half (var 1)))) :: (var 1 ≐ two * half (var 1)) ::
      (var 0 ≐ two * half (var 0)) :: (var 1 ≐ succ (pred (var 1))) ::
      (cube (var 0) ≐ two * cube (var 1)) :: Λ) ⊢[PRAAx] lt (half (var 1)) (var 1) := by
    refine le_of_eq_add (d := pred (half (var 1))) ?_
    refine withEq Prf.hyp0 fun e₁ => withEq Prf.hyp1 fun e₂ => ?_
    ipra_lc e₂ + e₁
  have hinner := sum_zero_elim outerBody hT.wk.wk.wk hg
  rw [inst2_outer] at hinner
  have hbad := sum_zero_elim badBody hinner (lt_succ_of_le (cube_bound hhg.wk))
  rw [inst2_bad] at hbad
  exact succ_ne_zero (a := zero) (((one_mul one).eqSymm.eqTrans (congrMul (eqb_of_eq hhg.wk)
    ((congrMonus (.eqRefl one) (congrMonus (.eqRefl one) Prf.hyp0)).eqTrans
      (sg_succ _))).eqSymm).eqTrans hbad)

/-- `T(N) = 0` for every `N`, by induction on `N`. -/
theorem descent_open : ([] : List (Fm PTm 1)) ⊢[PRAAx] T (var 0) ≐ zero := by
  ipra_ind [subst_ap2]
  · exact sum_zero _ _
  · refine (sum_succ' outerBody (var 0) zero).eqTrans ?_
    rw [inst2_outer]
    refine (congrAdd Prf.hyp0 ?_).eqTrans (add_zero _)
    refine sum_zero_of_all badBody (var 0) (.allI ?_) _
    simpa [Fm.shift, Syn.shift] using bad_zero

/-- `a³ = 2b³ → b = 0`: `X³ − 2` has no rational root. -/
abbrev cubeRootFormula : Fm PTm 2 := (cube (var 0) ≐ two * cube (var 1)) ⟶ (var 1 ≐ zero)

theorem no_rational_cube_root_of_two : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 cubeRootFormula := by
  refine closeUniv 2 (.impI ?_)
  have hT : ([cube (var 0) ≐ two * cube (var 1)] : List (Fm PTm 2)) ⊢[PRAAx] T (succ (var 1)) ≐ zero := by
    have h := inst (Γ := [cube (var 0) ≐ two * cube (var 1)]) descent_open (![succ (var 1)] : Fin 1 → PTm 2)
    simpa using h
  have hinner := sum_zero_elim outerBody hT (lt_succ_of_le (le_refl _))
  rw [inst2_outer] at hinner
  have hbad := sum_zero_elim badBody hinner (lt_succ_of_le (cube_bound Prf.hyp0))
  rw [inst2_bad] at hbad
  refine .orE (zero_or_succ (var 1)) Prf.hyp0 ?_
  refine .botE _ ?_
  exact succ_ne_zero (a := zero) (((one_mul one).eqSymm.eqTrans (congrMul (eqb_of_eq Prf.hyp1)
    ((congrMonus (.eqRefl one) (congrMonus (.eqRefl one) Prf.hyp0)).eqTrans
      (sg_succ _))).eqSymm).eqTrans hbad.wk)

end LeanProofs.IPRA.Algebra.CubeRootTwo
