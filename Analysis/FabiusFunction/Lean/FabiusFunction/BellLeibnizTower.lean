import FabiusFunction.BellComposition
import FabiusFunction.BellDerivative

/-!
# Faà di Bruno for a Leibniz tower

The transseries volume's `plt:lem:bell-abstract-faa`, in the algebraic
form the volume actually uses.  Fix a commutative `ℚ`-algebra `A` with a
derivation `D`, an element `γ` of `A` (the "inner derivative"), and a
*Leibniz tower over `γ`*: a sequence `u : ℕ → A` with

`D (u k) = u (k+1) · γ`   for every `k`.

(The motivating case is `u k = f^{(k)} ∘ y` for a scalar function `f` and
`γ = y'`, where the chain rule supplies exactly this law.)  Then the
iterated derivative of the bottom of the tower is the Bell expansion

`D^[n] (u 0) = ∑_{k ≤ n} u k · B_{n,k}(γ, Dγ, D²γ, …)`,

with the *exponential* partial Bell polynomials already carried by the
corpus.  No analysis, no composition of functions and no formal-series
substitution is involved: the statement holds in any commutative
`ℚ`-algebra with a derivation, and the classical Faà di Bruno formula
is the instance `A = C^∞`.

The proof is self-contained given the corpus's Bell machinery.  Its
engine is `derivation_partialBell_tower`, the **inhomogeneous recurrence**

`D B_{n,k+1} = B_{n+1,k+1} - γ · B_{n,k}`,

obtained by differentiating the column identity
`Ξ^(k+1) = (k+1)!·∑ B_{n,k+1} zⁿ/n!` coefficientwise: applying `D` to
the coefficients of `Ξ` shifts the tower up, which is the formal
derivative `d/dz` of `Ξ` minus the constant `γ` that the shift drops.
The main theorem then follows by induction, the correction terms
`-γ·B_{n,k}` telescoping against the tower's own Leibniz terms.

* `derivationTower` — the argument sequence `(γ, Dγ, D²γ, …)` fed to the
  Bell polynomials, indexed from `1` as the corpus expects.
* `coeffDerivation_bellWeightSeries_tower` — differentiating the tower's
  weight series coefficientwise is `d/dz` minus `C γ`.
* `derivation_partialBell_tower` — **the engine**, the inhomogeneous Bell
  recurrence.
* `iterate_derivation_eq_sum_partialBell` — **abstract Faà di Bruno**.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section Tower

variable {A : Type*} [CommRing A] [Algebra ℚ A] (D : Derivation ℚ A A)

/-- The **derivation tower** of `γ`: the sequence `j ↦ D^{j-1} γ` fed to
the partial Bell polynomials.  The corpus indexes Bell arguments from
`1`, so `derivationTower D γ 1 = γ`, `derivationTower D γ 2 = D γ`, and
so on; the value at `0` is irrelevant and is `γ` by the truncated
subtraction. -/
noncomputable def derivationTower (γ : A) (j : ℕ) : A := (D^[j - 1]) γ

/-- The first entry of the derivation tower is the original element. -/
@[simp] theorem derivationTower_one (γ : A) : derivationTower D γ 1 = γ := by
  rw [derivationTower]
  simp

/-- Differentiating the tower shifts it up one step (away from the
irrelevant index `0`). -/
theorem derivation_derivationTower (γ : A) {j : ℕ} (hj : j ≠ 0) :
    D (derivationTower D γ j) = derivationTower D γ (j + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  rw [derivationTower, derivationTower]
  simp [Function.iterate_succ_apply']

private theorem derivation_algebraMap_mul (q : ℚ) (a : A) :
    D (algebraMap ℚ A q * a) = algebraMap ℚ A q * D a := by
  rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
    smul_eq_mul]

private theorem derivation_natCast_mul (m : ℕ) (a : A) :
    D ((m : A) * a) = (m : A) * D a := by
  rw [show ((m : A)) = algebraMap ℚ A (m : ℚ) from (map_natCast _ _).symm,
    derivation_algebraMap_mul]

/-- Applying `D` to every coefficient of the tower's weight series
`Ξ = ∑_{j≥1} (D^{j-1} γ) z^j/j!` shifts the tower up, and a shift of an
exponential generating series is its formal derivative — except that the
derivative also produces the constant term `γ`, which the coefficientwise
derivation does not.  Hence `coeffDerivation D Ξ = d⁄dz Ξ - C γ`. -/
theorem coeffDerivation_bellWeightSeries_tower (γ : A) :
    coeffDerivation D (bellWeightSeries A (derivationTower D γ)) =
      d⁄dX A (bellWeightSeries A (derivationTower D γ)) - PowerSeries.C γ := by
  ext n
  rw [map_sub, coeff_coeffDerivation, derivative_bellWeightSeries, coeff_egfA,
    bellWeightSeries, coeff_egfA, coeff_C]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [if_pos rfl, if_pos rfl]
    simp
  · rw [if_neg hn.ne', if_neg hn.ne', sub_zero, derivation_algebraMap_mul]
    congr 1
    rw [Bell.shift, derivation_derivationTower D γ hn.ne']

/-- **The engine: the inhomogeneous Bell recurrence.**  For a derivation
tower the partial Bell polynomials satisfy

`D B_{n,k+1} = B_{n+1,k+1} - γ·B_{n,k}`.

Both the shift `B_{n,k+1} ↦ B_{n+1,k+1}` and the correction `-γ·B_{n,k}`
come from the previous lemma, read off the `k+1`-st power of the weight
series.  Only columns `k+1 ≥ 1` are covered — column `0` is constant. -/
theorem derivation_partialBell_tower (γ : A) (n k : ℕ) :
    D (partialBell (derivationTower D γ) n (k + 1)) =
      partialBell (derivationTower D γ) (n + 1) (k + 1) -
        γ * partialBell (derivationTower D γ) n k := by
  have hpowder := PowerSeries.derivative_pow A
    (bellWeightSeries A (derivationTower D γ)) (k + 1)
  rw [Nat.add_sub_cancel] at hpowder
  have hleib := (coeffDerivation D).leibniz_pow
    (a := bellWeightSeries A (derivationTower D γ)) (n := k + 1)
  rw [Nat.add_sub_cancel, coeffDerivation_bellWeightSeries_tower] at hleib
  have hseries : coeffDerivation D
        (bellWeightSeries A (derivationTower D γ) ^ (k + 1)) =
      d⁄dX A (bellWeightSeries A (derivationTower D γ) ^ (k + 1)) -
        PowerSeries.C ((k + 1 : ℕ) : A) *
          bellWeightSeries A (derivationTower D γ) ^ k * PowerSeries.C γ := by
    rw [hleib, hpowder]
    rw [show (PowerSeries.C ((k + 1 : ℕ) : A)) = ((k + 1 : ℕ) : A⟦X⟧) from
      map_natCast (PowerSeries.C (R := A)) _]
    simp only [nsmul_eq_mul, smul_eq_mul]
    ring
  have hco := congrArg (fun f => coeff (R := A) n f) hseries
  simp only [coeff_coeffDerivation, map_sub, coeff_derivative,
    coeff_bellWeightSeries_pow, coeff_C_mul, coeff_mul_C] at hco
  rw [derivation_natCast_mul, derivation_algebraMap_mul] at hco
  -- two scalar identities
  have ha : algebraMap ℚ A (1 / (n + 1).factorial) * ((n : A) + 1) =
      algebraMap ℚ A (1 / n.factorial) := by
    have h1 : algebraMap ℚ A ((n : ℚ) + 1) = (n : A) + 1 := by
      rw [map_add, map_natCast, map_one]
    rw [← h1, ← map_mul]
    congr 1
    have hfac : ((n + 1).factorial : ℚ) = ((n : ℚ) + 1) * (n.factorial : ℚ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hfac]
    have hn : ((n.factorial : ℚ)) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
    field_simp
  have hb : ((k + 1 : ℕ) : A) * (k.factorial : A) = ((k + 1).factorial : A) := by
    rw [← Nat.cast_mul, Nat.factorial_succ]
  -- clear the common unit factor
  have key : ((k + 1).factorial : A) *
        (algebraMap ℚ A (1 / n.factorial) *
          D (partialBell (derivationTower D γ) n (k + 1))) =
      ((k + 1).factorial : A) *
        (algebraMap ℚ A (1 / n.factorial) *
          (partialBell (derivationTower D γ) (n + 1) (k + 1) -
            γ * partialBell (derivationTower D γ) n k)) := by
    rw [hco, ← ha, ← hb]
    ring
  have hq : ((n.factorial : ℚ)) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hq' : (((k + 1).factorial : ℚ)) ≠ 0 := by
    exact_mod_cast (k + 1).factorial_ne_zero
  have hinv : algebraMap ℚ A ((n.factorial : ℚ) / ((k + 1).factorial : ℚ)) *
      (((k + 1).factorial : A) * algebraMap ℚ A (1 / n.factorial)) = 1 := by
    rw [show (((k + 1).factorial : A)) =
        algebraMap ℚ A (((k + 1).factorial : ℚ)) from (map_natCast _ _).symm,
      ← map_mul, ← map_mul]
    rw [show ((n.factorial : ℚ) / ((k + 1).factorial : ℚ) *
        (((k + 1).factorial : ℚ) * (1 / (n.factorial : ℚ)))) = 1 by field_simp]
    exact map_one _
  set e := algebraMap ℚ A ((n.factorial : ℚ) / ((k + 1).factorial : ℚ)) with he
  calc D (partialBell (derivationTower D γ) n (k + 1))
      = (e * (((k + 1).factorial : A) *
          algebraMap ℚ A (1 / n.factorial))) *
          D (partialBell (derivationTower D γ) n (k + 1)) := by
        rw [hinv, one_mul]
    _ = e * (((k + 1).factorial : A) * (algebraMap ℚ A (1 / n.factorial) *
          D (partialBell (derivationTower D γ) n (k + 1)))) := by ring
    _ = e * (((k + 1).factorial : A) * (algebraMap ℚ A (1 / n.factorial) *
          (partialBell (derivationTower D γ) (n + 1) (k + 1) -
            γ * partialBell (derivationTower D γ) n k))) := by rw [key]
    _ = (e * (((k + 1).factorial : A) *
          algebraMap ℚ A (1 / n.factorial))) *
          (partialBell (derivationTower D γ) (n + 1) (k + 1) -
            γ * partialBell (derivationTower D γ) n k) := by ring
    _ = _ := by rw [hinv, one_mul]

/-- **Abstract Faà di Bruno.**  If `u` is a Leibniz tower over `γ`, i.e.
`D (u k) = u (k+1)·γ` for all `k`, then

`D^[n] (u 0) = ∑_{k ≤ n} u k · B_{n,k}(γ, Dγ, D²γ, …)`.

Taking `A` to be a ring of smooth functions, `u k = f^{(k)} ∘ y` and
`γ = y'` recovers the classical formula; but the identity is purely
algebraic and holds in every commutative `ℚ`-algebra with a derivation. -/
theorem iterate_derivation_eq_sum_partialBell (γ : A) (u : ℕ → A)
    (hu : ∀ k, D (u k) = u (k + 1) * γ) (n : ℕ) :
    (D^[n]) (u 0) =
      ∑ k ∈ range (n + 1), u k * partialBell (derivationTower D γ) n k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, map_sum]
      have hterm : ∀ k ∈ range (n + 1),
          D (u k * partialBell (derivationTower D γ) n k) =
            u k * D (partialBell (derivationTower D γ) n k) +
              partialBell (derivationTower D γ) n k * (u (k + 1) * γ) := by
        intro k _
        rw [Derivation.leibniz, hu k, smul_eq_mul, smul_eq_mul]
      rw [Finset.sum_congr rfl hterm]
      rcases n with _ | m
      · simp [Finset.sum_range_succ, partialBell_self, derivationTower_one,
          Derivation.map_one_eq_zero]
      · rw [Finset.sum_range_succ' _ (m + 1), Finset.sum_range_succ' _ (m + 2),
          partialBell_succ_zero, partialBell_succ_zero]
        simp only [map_zero, mul_zero, zero_mul, add_zero, zero_add]
        simp only [derivation_partialBell_tower]
        have key := Finset.sum_range_sub
          (fun j => u (j + 1) * γ *
            partialBell (derivationTower D γ) (m + 1) j) (m + 1)
        have hsplit : ∀ x ∈ range (m + 1),
            u (x + 1) *
                (partialBell (derivationTower D γ) (m + 1 + 1) (x + 1) -
                  γ * partialBell (derivationTower D γ) (m + 1) x) +
              partialBell (derivationTower D γ) (m + 1) (x + 1) *
                (u (x + 1 + 1) * γ) =
              u (x + 1) *
                  partialBell (derivationTower D γ) (m + 1 + 1) (x + 1) +
                ((fun j => u (j + 1) * γ *
                    partialBell (derivationTower D γ) (m + 1) j) (x + 1) -
                  (fun j => u (j + 1) * γ *
                    partialBell (derivationTower D γ) (m + 1) j) x) := by
          intro x _
          simp only
          ring
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, key]
        conv_rhs => rw [Finset.sum_range_succ]
        rw [partialBell_succ_zero, partialBell_self, partialBell_self,
          derivationTower_one]
        ring

end Tower

end Fabius
