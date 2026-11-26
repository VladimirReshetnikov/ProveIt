import IPRADerivations.DiophantineNumberTheory.PellAll
import IPRADerivations.AnalyticNumberTheory.FactorVector
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# An explicit Pell family: `D = t² − 1`

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/diophantine.tex`, Corollary
`dio:pell-family`: for `t ≥ 2`, the nonsquare `D = t² − 1` has fundamental solution `(t, 1)`, and all its positive
solutions are powers of this pair.

With `D = pred (t · t)`:

* `family_solution`: `t² = 1 + D · 1²` for `t ≥ 1`;
* `min_one`: the second coordinate `1` is minimal among the solutions with `y ≥ 1` (`PellAll.minimal D 1`);
* **`nonsquare`**: for `t ≥ 2` no `s` has `s² = D`, since `(t − 1)² < D < t²`;
* **`pell_family`**: every solution `x² = 1 + D y²` is the power `(X_c, Y_c)` of `(t, 1)` with the exponent
  `c = C(y) ≤ y` of `PellAll.pell_all_at`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellFamily

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (one_le_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.PellAll (minimal pell_all_at Xp Yp C p3)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The solution `(t, 1)` -/

theorem sol_alg {T D : PTm n} (e : Γ ⊢[PRAAx] T ≐ succ D) : Γ ⊢[PRAAx] T ≐ one + D * (one * one) := by
  ipra_lc natEq e

/-- `t² = 1 + (t² − 1) · 1²` for `t ≥ 1`. -/
theorem family_solution {t : PTm n} (ht : Γ ⊢[PRAAx] t ≐ succ (pred t)) :
    Γ ⊢[PRAAx] t * t ≐ one + pred (t * t) * (one * one) :=
  sol_alg (pos_mul ht ht)

/-- The second coordinate `1` is minimal. -/
theorem min_one (D : PTm n) : Γ ⊢[PRAAx] minimal D one := by
  refine .allI (.allI (.impI (.impI ?_)))
  have e : Syn.shift (Syn.shift (one : PTm n)) = one := by simp [Syn.shift]
  rw [e]
  exact one_le_pos Prf.hyp0

/-! ## `t² − 1` is not a square -/

theorem below_s {s t u D : PTm n} (e1 : Γ ⊢[PRAAx] t ≐ succ s + u) (e2 : Γ ⊢[PRAAx] s * s ≐ D)
    (e3 : Γ ⊢[PRAAx] t * t ≐ succ D) :
    Γ ⊢[PRAAx] zero ≐ s + (s + two * u + two * (s * u) + u * u) := by
  ipra_lc natEq e2 - natEq e3 + (𝔞 t + 𝔞 s + 1 + 𝔞 u) * natEq e1

theorem below_u {s t u D : PTm n} (e1 : Γ ⊢[PRAAx] t ≐ succ s + u) (e2 : Γ ⊢[PRAAx] s * s ≐ D)
    (e3 : Γ ⊢[PRAAx] t * t ≐ succ D) :
    Γ ⊢[PRAAx] zero ≐ u + (two * s + u + two * (s * u) + u * u) := by
  ipra_lc natEq e2 - natEq e3 + (𝔞 t + 𝔞 s + 1 + 𝔞 u) * natEq e1

theorem t_one {s t u : PTm n} (e1 : Γ ⊢[PRAAx] t ≐ succ s + u) (hs : Γ ⊢[PRAAx] s ≐ zero)
    (hu : Γ ⊢[PRAAx] u ≐ zero) : Γ ⊢[PRAAx] t ≐ one := by
  ipra_lc natEq e1 + natEq hs + natEq hu

theorem above_alg {s t v D : PTm n} (e1 : Γ ⊢[PRAAx] s ≐ t + v) (e2 : Γ ⊢[PRAAx] s * s ≐ D)
    (e3 : Γ ⊢[PRAAx] t * t ≐ succ D) : Γ ⊢[PRAAx] succ (two * (t * v) + v * v) ≐ zero := by
  ipra_lc natEq e2 - natEq e3 - (𝔞 s + 𝔞 t + 𝔞 v) * natEq e1

theorem zero_of_le_zero {X : PTm n} (h : Γ ⊢[PRAAx] le X zero) : Γ ⊢[PRAAx] X ≐ zero :=
  (monus_zero X).eqSymm.eqTrans h

/-- **`t² − 1` is not a square** for `t ≥ 2`. -/
theorem nonsquare {t s : PTm n} (h2 : Γ ⊢[PRAAx] le two t) :
    Γ ⊢[PRAAx] neg (s * s ≐ pred (t * t)) := by
  have ht : Γ ⊢[PRAAx] t ≐ succ (pred t) := LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul.p_pos h2
  have e3 := pos_mul ht ht
  refine .impI ?_
  refine .orE (lt_or_le s t) ?_ ?_
  · let C : List (Fm PTm n) := lt s t :: (s * s ≐ pred (t * t)) :: Γ
    have hlt : C ⊢[PRAAx] le (succ s) t := Prf.hyp0
    have e2 : C ⊢[PRAAx] s * s ≐ pred (t * t) := Prf.hyp1
    have e1 := eq_add_of_le hlt
    have e3' : C ⊢[PRAAx] t * t ≐ succ (pred (t * t)) := e3.wk.wk
    have hs := zero_of_le_zero (le_of_eq_add (below_s e1 e2 e3'))
    have hu := zero_of_le_zero (le_of_eq_add (below_u e1 e2 e3'))
    have t1 := t_one e1 hs hu
    have l : C ⊢[PRAAx] lt one one := le_congr (.eqRefl _) t1 h2.wk.wk
    exact lt_irrefl one _ l
  · let C : List (Fm PTm n) := le t s :: (s * s ≐ pred (t * t)) :: Γ
    have hle : C ⊢[PRAAx] le t s := Prf.hyp0
    have e2 : C ⊢[PRAAx] s * s ≐ pred (t * t) := Prf.hyp1
    have e3' : C ⊢[PRAAx] t * t ≐ succ (pred (t * t)) := e3.wk.wk
    exact succ_ne_zero' _ (above_alg (eq_add_of_le hle) e2 e3')

/-! ## All solutions -/

/-- The data of the family: `A = t`, `B = 1`, `D = t² − 1`, and a solution `(x, y)`. -/
abbrev fam (t x y : PTm n) : Fin 5 → PTm n := ![t, one, pred (t * t), x, y]

/-- **`dio:pell-family`**: every solution `x² = 1 + (t² − 1) y²` is the power `(X_c, Y_c)` of `(t, 1)`, with
`c = C(y) ≤ y`. -/
theorem pell_family {t x y : PTm n} (ht : Γ ⊢[PRAAx] t ≐ succ (pred t))
    (hx : Γ ⊢[PRAAx] x * x ≐ one + pred (t * t) * (y * y)) :
    Γ ⊢[PRAAx] (x ≐ Xp (C y (fam t x y)) (p3 (fam t x y))) ⋏
      (y ≐ Yp (C y (fam t x y)) (p3 (fam t x y))) ⋏ le (C y (fam t x y)) y := by
  have hB : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm
  exact pell_all_at (ps := fam t x y) (family_solution ht) hB (min_one _) hx

end LeanProofs.IPRA.DiophantineNumberTheory.PellFamily
