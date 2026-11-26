import IPRADerivations.DiophantineNumberTheory.ConicNonzero
import IPRADerivations.DiophantineNumberTheory.ConicGcd
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# The unit circle `X² + Y² = Z²`

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Section `sec:conics`, "The unit circle": the
parametrization `[s : t] ↦ [s² − t² : 2st : s² + t²]` (its defining identity is in `Identities`), its inverse and
the exact common divisor of the coordinates.

* `circle_exceptional`: "if `Z + X = 0`, the conic equation gives `Y² = 0` and hence `Y = 0`";
* `circle_recover`: "substitution into the parametrization, followed by use of `X² + Y² = Z²`, recovers
  `[X : Y : Z]`": with `s = Z + X`, `t = Y` the image is `2s (X, Y, Z)`;
* `circle_gcd_two`: "any common divisor divides `2s²` and `2t²`, and `gcd(s², t²) = 1` therefore makes it divide
  `2`" (natural coordinates with `D + t² = s²`, `D = s² − t²`);
* `circle_both_odd`: "If the inputs are both odd, all three coordinates are even";
* `circle_mixed_parity`: "if their parities differ, the ... third [is] odd";
* `circle_le_D`, `circle_le_2st`: "`|s² − t²| ≤ s² + t²` and `|2st| ≤ s² + t²`", so the height is `(s² + t²)/ε`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.CircleParam

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.ConicNonzero (zt_sq_zero)
open LeanProofs.IPRA.DiophantineNumberTheory.ConicGcd (dvd_of_coprime_pair coprime_squares)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_add' dvd_sub')

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Signed identities -/

/-- `X² + Y² = Z²` and `Z + X = 0` give `Y = 0`. -/
theorem circle_exceptional {X Y Z : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (X * X + Y * Y) (Z * Z))
    (hz : Γ ⊢[PRAAx] ZT.eq (Z + X) (ZT.natLit 0)) : Γ ⊢[PRAAx] ZT.eq Y (ZT.natLit 0) := by
  refine zt_sq_zero (ZT.derive ?_)
  have eh := ZT.toZ_eq h
  have ez := ZT.toZ_eq hz
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at eh ez ⊢
  try push_cast at eh ez ⊢
  linear_combination eh + (ZT.toZ Γ Z - ZT.toZ Γ X) * ez

/-- With `s = Z + X`, `t = Y` on `X² + Y² = Z²`: `(s² − t², 2st, s² + t²) = 2s (X, Y, Z)`. -/
theorem circle_recover {X Y Z : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (X * X + Y * Y) (Z * Z)) :
    (Γ ⊢[PRAAx] ZT.eq ((Z + X) * (Z + X) - Y * Y) (ZT.natLit 2 * (Z + X) * X)) ∧
    (Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * (Z + X) * Y) (ZT.natLit 2 * (Z + X) * Y)) ∧
    (Γ ⊢[PRAAx] ZT.eq ((Z + X) * (Z + X) + Y * Y) (ZT.natLit 2 * (Z + X) * Z)) := by
  have eh := ZT.toZ_eq h
  simp only [ZT.toZ_add, ZT.toZ_mul] at eh
  refine ⟨ZT.derive ?_, ZT.derive rfl, ZT.derive ?_⟩
  · simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]
    linear_combination -eh
  · simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit]
    linear_combination eh

/-! ## The common divisor `ε` -/

theorem two_pos : Γ ⊢[PRAAx] num 2 ≐ succ (pred (num 2)) := congrSucc (pred_succ (num 1)).eqSymm

/-- A common divisor of `s² − t²` and `s² + t²` divides `2`, when `gcd(s, t) = 1` (here `D = s² − t²`). -/
theorem circle_gcd_two {g s t D : PTm n} (hg : Γ ⊢[PRAAx] g ≐ succ (pred g)) (hs : Γ ⊢[PRAAx] s ≐ succ (pred s))
    (ht : Γ ⊢[PRAAx] t ≐ succ (pred t)) (hst : Γ ⊢[PRAAx] gcd s t ≐ one) (hD : Γ ⊢[PRAAx] D + t * t ≐ s * s)
    (h1 : Γ ⊢[PRAAx] dvd g D) (h3 : Γ ⊢[PRAAx] dvd g (s * s + t * t)) : Γ ⊢[PRAAx] dvd g (num 2) := by
  have a : Γ ⊢[PRAAx] dvd g (num 2 * (s * s)) := by
    refine dvd_congr ?_ (dvd_add' hg h3 h1)
    ipra_lc natEq hD
  have b : Γ ⊢[PRAAx] dvd g (num 2 * (t * t)) := by
    refine dvd_sub' hg (dvd_congr ?_ h3) h1
    ipra_lc -natEq hD
  exact dvd_of_coprime_pair hg a b (coprime_squares hs ht hst)

/-- Both inputs odd: all three coordinates are even. -/
theorem circle_both_odd {s t a b D : PTm n} (hs : Γ ⊢[PRAAx] s ≐ num 2 * a + one)
    (ht : Γ ⊢[PRAAx] t ≐ num 2 * b + one) (hD : Γ ⊢[PRAAx] D + t * t ≐ s * s) :
    Γ ⊢[PRAAx] dvd (num 2) D ⋏ (dvd (num 2) (num 2 * s * t) ⋏ dvd (num 2) (s * s + t * t)) := by
  have es := natEq hs
  have et := natEq ht
  have e := natEq hD
  have hsum : Γ ⊢[PRAAx] dvd (succ (num 1)) (D + num 4 * (b * b + b)) := by
    refine dvd_of_eq (w := num 2 * (a * a + a)) ?_
    apply deriveNat; ipra_simps
    rw [es, et] at e
    linear_combination e
  have h4 : Γ ⊢[PRAAx] dvd (succ (num 1)) (num 4 * (b * b + b)) := by
    refine dvd_of_eq (w := num 2 * (b * b + b)) ?_
    ipra_ring
  have h2 : Γ ⊢[PRAAx] dvd (succ (num 1)) (num 2 * s * t) := by
    refine dvd_of_eq (w := s * t) ?_
    ipra_ring
  have h3 : Γ ⊢[PRAAx] dvd (succ (num 1)) (s * s + t * t) := by
    refine dvd_of_eq (w := num 2 * (a * a + a + b * b + b) + one) ?_
    apply deriveNat; ipra_simps
    rw [es, et]; ring
  exact .andI (dvd_sub hsum h4) (.andI h2 h3)

/-- Inputs of opposite parity: `s² + t²` is odd. -/
theorem circle_mixed_parity {s t a b : PTm n} (hs : Γ ⊢[PRAAx] s ≐ num 2 * a)
    (ht : Γ ⊢[PRAAx] t ≐ num 2 * b + one) : Γ ⊢[PRAAx] neg (dvd (num 2) (s * s + t * t)) := by
  have es := natEq hs
  have et := natEq ht
  have lt12 : Γ ⊢[PRAAx] lt one (succ (num 1)) := (le_refl _ : Γ ⊢[PRAAx] le (succ one) (succ (num 1)))
  have r : Γ ⊢[PRAAx] rem (s * s + t * t) (succ (num 1)) ≐ one := by
    refine Prf.andE₂ (div_mod_unique (q := num 2 * (a * a + b * b + b)) ?_ lt12)
    apply deriveNat; ipra_simps
    rw [es, et]; ring
  refine .impI ?_
  exact succ_ne_zero (r.wk.eqSymm.eqTrans (Prf.hyp0 : (dvd (num 2) (s * s + t * t) :: Γ) ⊢[PRAAx] _))

/-! ## The height -/

/-- `s² − t² ≤ s² + t²`. -/
theorem circle_le_D {s t D : PTm n} (hD : Γ ⊢[PRAAx] D + t * t ≐ s * s) : Γ ⊢[PRAAx] le D (s * s + t * t) := by
  refine le_of_eq_add (d := t * t + t * t) ?_
  ipra_lc -natEq hD

/-- `2st ≤ s² + t²` (for `s = t + u`). -/
theorem circle_le_2st {s t u : PTm n} (hu : Γ ⊢[PRAAx] s ≐ t + u) :
    Γ ⊢[PRAAx] le (num 2 * s * t) (s * s + t * t) := by
  refine le_of_eq_add (d := u * u) ?_
  have e := natEq hu
  apply deriveNat; ipra_simps
  rw [e]; ring

end LeanProofs.IPRA.DiophantineNumberTheory.CircleParam
