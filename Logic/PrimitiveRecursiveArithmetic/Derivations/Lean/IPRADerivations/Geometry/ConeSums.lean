import IPRADerivations.Core.Order
import IPRADerivations.Core.LinearCombination

/-!
# The sums of squares behind the volume of the cone

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/limits.tex`, Lemma `lim:sums`. With
`Q(m) = ∑_{i<m} i²` (`sqF`), so that `S_m^- = Q(m)/m³` and `S_m^+ = Q(m + 1)/m³`, and `T(m) = ∑_{i<m} i` of
`Core/Sums`, uniformly in the term `m`:

* `pyramidal`: `6 Q(m) + 3 m² = 2 m³ + m`, the integer identity "`6 ∑_{i=0}^{m−1} i² = m (m − 1)(2m − 1)`"
  with its negative terms moved to the other side; it is (L7) for `S_m^-` after division by `6 m³`;
* `upper_sum`: `Q(m + 1) = Q(m) + m²`, that is "`S_m^+ − S_m^- = 1/m`";
* `lower_third`, `upper_third`: `6 Q(m) ≤ 2 m³ ≤ 6 Q(m + 1)`, that is "`S_m^- ≤ 1/3 ≤ S_m^+`";
* `refine_lower`, `refine_upper`: `6 · 8 Q(m) ≤ 6 Q(2m)` and `6 Q(2m + 1) ≤ 6 · 8 Q(m + 1)`, that is
  "`S_m^- ≤ S_{2m}^-`, `S_{2m}^+ ≤ S_m^+`", with the explicit differences `6 m² + 12 T(m) = 6 m (2m − 1)` and
  `12 m² + 6 m`.

Not derived: the products with the polygon areas `p_k`, `q_k` and the resulting volume observations.
-/

namespace LeanProofs.IPRA.Geometry.ConeSums

open_ipra

local notation "𝟚" => succ (succ zero)
local notation "𝟛" => succ (succ (succ zero))
local notation "𝟞" => succ (succ (succ (succ (succ (succ zero)))))

/-- `Q(m) = ∑_{i<m} i²`. -/
abbrev sqF : PR 2 := sumF (var 0 * var 0)

/-- `6 Q(m) + 3 m² = 2 m³ + m`. -/
abbrev pyramidalFormula : Fm PTm 1 :=
  𝟞 * ap2 sqF (var 0) zero + 𝟛 * (var 0 * var 0) ≐ 𝟚 * (var 0 * var 0 * var 0) + var 0

theorem pyramidal_open : ([] : List (Fm PTm 1)) ⊢[PRAAx] pyramidalFormula := by
  refine ind _ trivial ?_ ?_
  · ipra_subst
    apply deriveNat
    have e := natEq (sum_zero (Γ := []) (var 0 * var 0) (zero : PTm 0))
    ipra_simps
    linear_combination 6 * e
  · ipra_subst
    apply deriveNat
    have h := natEq (Γ := [pyramidalFormula]) Prf.hyp0
    have e := natEq (sum_succ (Γ := [pyramidalFormula]) (var 0 * var 0) (var 0) zero)
    simp only [PTm.subst_mul, Syn.subst_var, Matrix.cons_val_zero] at e
    ipra_simps
    linear_combination h + 6 * e

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `6 Q(m) + 3 m² = 2 m³ + m`. -/
theorem pyramidal (m : PTm n) :
    Γ ⊢[PRAAx] 𝟞 * ap2 sqF m zero + 𝟛 * (m * m) ≐ 𝟚 * (m * m * m) + m := by
  have h := inst (Γ := Γ) pyramidal_open (![m] : Fin 1 → PTm n)
  simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Matrix.cons_val_zero] at h
  exact h

/-- `2 T(m) + m = m²`, for an arbitrary term. -/
theorem gauss_at (m : PTm n) : Γ ⊢[PRAAx] 𝟚 * ap2 Sums.triF m zero + m ≐ m * m := by
  have h := inst (Γ := Γ) Sums.gauss_open (![m] : Fin 1 → PTm n)
  simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Matrix.cons_val_zero] at h
  exact h

/-- `Q(m + 1) = Q(m) + m²`. -/
theorem upper_sum (m : PTm n) : Γ ⊢[PRAAx] ap2 sqF (succ m) zero ≐ ap2 sqF m zero + m * m := by
  have e := sum_succ (Γ := Γ) (var 0 * var 0) m zero
  simp only [PTm.subst_mul, Syn.subst_var, Matrix.cons_val_zero] at e
  exact e

/-- `S_m^- ≤ 1/3`: `6 Q(m) ≤ 2 m³`. -/
theorem lower_third (m : PTm n) : Γ ⊢[PRAAx] le (𝟞 * ap2 sqF m zero) (𝟚 * (m * m * m)) := by
  refine le_of_eq_add (d := 𝟚 * (m * m) + 𝟚 * ap2 Sums.triF m zero) ?_
  ipra_lc -natEq (pyramidal (Γ := Γ) m) - natEq (gauss_at (Γ := Γ) m)

/-- `1/3 ≤ S_m^+`: `2 m³ ≤ 6 Q(m + 1)`. -/
theorem upper_third (m : PTm n) : Γ ⊢[PRAAx] le (𝟚 * (m * m * m)) (𝟞 * ap2 sqF (succ m) zero) := by
  refine le_of_eq_add (d := 𝟛 * (m * m) + m) ?_
  ipra_lc 6 * natEq (upper_sum (Γ := Γ) m) + natEq (pyramidal (Γ := Γ) m)

/-- `S_m^- ≤ S_{2m}^-`: `6 · 8 Q(m) ≤ 6 Q(2m)`. -/
theorem refine_lower (m : PTm n) :
    Γ ⊢[PRAAx] le (𝟞 * ((𝟚 * 𝟚 * 𝟚) * ap2 sqF m zero)) (𝟞 * ap2 sqF (𝟚 * m) zero) := by
  refine le_of_eq_add (d := 𝟞 * (m * m) + 𝟞 * (𝟚 * ap2 Sums.triF m zero)) ?_
  ipra_lc natEq (pyramidal (Γ := Γ) (𝟚 * m)) - 8 * natEq (pyramidal (Γ := Γ) m) - 6 * natEq (gauss_at (Γ := Γ) m)

/-- `S_{2m}^+ ≤ S_m^+`: `6 Q(2m + 1) ≤ 6 · 8 Q(m + 1)`. -/
theorem refine_upper (m : PTm n) :
    Γ ⊢[PRAAx] le (𝟞 * ap2 sqF (succ (𝟚 * m)) zero) (𝟞 * ((𝟚 * 𝟚 * 𝟚) * ap2 sqF (succ m) zero)) := by
  refine le_of_eq_add (d := 𝟞 * (𝟚 * (m * m)) + 𝟞 * m) ?_
  ipra_lc 48 * natEq (upper_sum (Γ := Γ) m) - 6 * natEq (upper_sum (Γ := Γ) (𝟚 * m)) +
    8 * natEq (pyramidal (Γ := Γ) m) - natEq (pyramidal (Γ := Γ) (𝟚 * m))

end LeanProofs.IPRA.Geometry.ConeSums
