import FabiusFunction.SincEulerProduct
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The canonical product of the Rvachev sinc product

The audit's zero-multiplicity theorem (`prop:canonical`): regrouping
the double Euler product of
`Φ(z) = ∏_h sinc (πz/2ʰ) = ∏_h ∏_r (1 - z²/((r+1)²·4ʰ))`
by the value `m + 1 = (r+1)·2ʰ` gives the canonical (Hadamard) form

`Φ(z) = ∏_{m ≥ 1} (1 - z²/m²)^{1 + v₂(m)}`,

so the zero of `Φ` at the nonzero integer `m` has multiplicity exactly
`1 + v₂(m)` — the arithmetic input behind the audit's two-adic valley
laws and the strict-log-concavity layer.

The regrouping is performed on the index set: the map
`(h, r) ↦ (r+1)·2ʰ` has fiber `{h : h ≤ v₂(m+1)}` over `m+1`, giving
an explicit equivalence
`ℕ × ℕ ≃ Σ m, Fin (v₂(m+1) + 1)` (`dyadicFactorEquiv`), and the factor
`1 - z²/((r+1)²4ʰ)` depends only on the fiber base `m`.  Absolute
convergence (norm-summability of the double family, a product of a
geometric and a `p`-series) makes the unordered regrouping exact.

* `dyadicFactorEquiv` — the fiber equivalence.
* `summable_norm_sineTerm_pair` — norm-summability of the double
  family.
* `rvachevFourierProduct_eq_canonical` — the canonical product, for
  every `z : ℂ`.
-/

set_option autoImplicit false

open Complex Real Filter

namespace Fabius

/-- The dyadic fiber equivalence: `(h, r) ↦ ⟨m, h⟩` with
`m + 1 = (r+1)·2ʰ`; the fiber over `m` is `{h : h ≤ v₂(m+1)}`. -/
def dyadicFactorEquiv : ℕ × ℕ ≃ Σ m : ℕ, Fin (padicValNat 2 (m + 1) + 1) where
  toFun p := ⟨(p.2 + 1) * 2 ^ p.1 - 1, ⟨p.1, by
    have hpos : 0 < (p.2 + 1) * 2 ^ p.1 := by positivity
    have h1 : (p.2 + 1) * 2 ^ p.1 - 1 + 1 = (p.2 + 1) * 2 ^ p.1 := by omega
    rw [h1, padicValNat.mul (Nat.succ_ne_zero p.2) (Nat.two_pow_pos p.1).ne',
      padicValNat.prime_pow]
    omega⟩⟩
  invFun σ := (σ.2.val, (σ.1 + 1) / 2 ^ σ.2.val - 1)
  left_inv p := by
    obtain ⟨h, r⟩ := p
    have hpos : 0 < (r + 1) * 2 ^ h := by positivity
    have h1 : (r + 1) * 2 ^ h - 1 + 1 = (r + 1) * 2 ^ h := by omega
    have h2 : (r + 1) * 2 ^ h / 2 ^ h = r + 1 :=
      Nat.mul_div_cancel _ (by positivity)
    simp only [h1, h2]
    rfl
  right_inv σ := by
    obtain ⟨m, j⟩ := σ
    have hdvd : 2 ^ (j : ℕ) ∣ m + 1 :=
      dvd_trans (pow_dvd_pow 2 (Nat.lt_succ_iff.mp j.isLt))
        pow_padicValNat_dvd
    have hquot : 0 < (m + 1) / 2 ^ (j : ℕ) :=
      Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos m) hdvd)
        (by positivity)
    have h1 : (m + 1) / 2 ^ (j : ℕ) - 1 + 1 = (m + 1) / 2 ^ (j : ℕ) := by
      omega
    have h2 : (m + 1) / 2 ^ (j : ℕ) * 2 ^ (j : ℕ) = m + 1 :=
      Nat.div_mul_cancel hdvd
    have hm : ((m + 1) / 2 ^ (j : ℕ) - 1 + 1) * 2 ^ (j : ℕ) - 1 = m := by
      rw [h1, h2]
      omega
    refine Sigma.ext hm ?_
    rw [Fin.heq_ext_iff (congrArg (fun k : ℕ => padicValNat 2 (k + 1) + 1) hm)]

/-- Norm-summability of the double sineTerm family: the norms form the
product of a geometric series in `h` and a `p`-series in `r`. -/
theorem summable_norm_sineTerm_pair (z : ℂ) :
    Summable fun p : ℕ × ℕ => ‖sineTerm (z / 2 ^ p.1) p.2‖ := by
  have hgeo : Summable fun h : ℕ => ‖z‖ ^ 2 * ((1:ℝ) / 4) ^ h :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hp2 : Summable fun r : ℕ => ((1:ℝ) / ((r + 1) ^ 2)) := by
    have h := Real.summable_one_div_nat_pow.mpr one_lt_two
    exact_mod_cast (summable_nat_add_iff 1).mpr h
  have hprod := hgeo.mul_of_nonneg hp2
    (fun h => by positivity) (fun r => by positivity)
  refine hprod.congr fun p => ?_
  obtain ⟨h, r⟩ := p
  simp only [sineTerm, norm_div, norm_neg, norm_pow]
  have hn2 : ‖(2:ℂ)‖ = 2 := by
    simp
  have hnr : ‖(r:ℂ) + 1‖ = (r:ℝ) + 1 := by
    have := Complex.norm_natCast (r + 1)
    push_cast at this
    exact this
  have hpow4 : (((2:ℝ)) ^ h) ^ 2 = 4 ^ h := by
    rw [← pow_mul, mul_comm h 2, pow_mul]
    norm_num
  have hr1 : ((r:ℝ) + 1) ^ 2 ≠ 0 := by positivity
  have h4h : ((4:ℝ)) ^ h ≠ 0 := by positivity
  rw [hn2, hnr]
  conv_rhs => rw [div_pow, hpow4]
  conv_lhs => rw [div_pow, one_pow]
  field_simp

/-- **The canonical product of the Rvachev sinc product** (the audit's
`prop:canonical`): for every `z : ℂ`,
`Φ(z) = ∏'_{m} (1 - z²/(m+1)²)^{1 + v₂(m+1)}` — indexing `m ≥ 1` by
`m + 1`, so the zero at the nonzero integer `n` has multiplicity
exactly `1 + v₂(n)`. -/
theorem rvachevFourierProduct_eq_canonical (z : ℂ) :
    rvachevFourierProduct z =
      ∏' m : ℕ, (1 - z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2) ^
        (padicValNat 2 (m + 1) + 1) := by
  classical
  set F : ℕ × ℕ → ℂ := fun p => 1 + sineTerm (z / 2 ^ p.1) p.2 with hF_def
  have hFmult : Multipliable F :=
    multipliable_one_add_of_summable (summable_norm_sineTerm_pair z)
  have hfib : ∀ h : ℕ, Multipliable fun r => F (h, r) := fun h =>
    multipliable_sineTerm (z / 2 ^ h)
  -- the factor depends only on the fiber base
  have hfactor : ∀ (m : ℕ) (j : Fin (padicValNat 2 (m + 1) + 1)),
      F (dyadicFactorEquiv.symm ⟨m, j⟩) =
        1 - z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2 := by
    intro m j
    have hdvd : 2 ^ (j : ℕ) ∣ m + 1 :=
      dvd_trans (pow_dvd_pow 2 (Nat.lt_succ_iff.mp j.isLt))
        pow_padicValNat_dvd
    have hquot : 0 < (m + 1) / 2 ^ (j : ℕ) :=
      Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos m) hdvd) (by positivity)
    have h1 : ((m + 1) / 2 ^ (j : ℕ) - 1) + 1 = (m + 1) / 2 ^ (j : ℕ) := by
      omega
    have h2 : 2 ^ (j : ℕ) * ((m + 1) / 2 ^ (j : ℕ)) = m + 1 :=
      Nat.mul_div_cancel' hdvd
    show 1 + sineTerm (z / 2 ^ (j : ℕ)) ((m + 1) / 2 ^ (j : ℕ) - 1) = _
    rw [sineTerm]
    have hcast : (((m + 1) / 2 ^ (j : ℕ) - 1 : ℕ) : ℂ) + 1 =
        (((m + 1) / 2 ^ (j : ℕ) : ℕ) : ℂ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℂ)) h1
    rw [hcast]
    have h2h : ((2:ℂ) ^ (j : ℕ)) ≠ 0 := pow_ne_zero _ two_ne_zero
    have hq0 : (((m + 1) / 2 ^ (j : ℕ) : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.pos_iff_ne_zero.mp hquot
    have hkey : ((2:ℂ) ^ (j : ℕ)) * (((m + 1) / 2 ^ (j : ℕ) : ℕ) : ℂ) =
        ((m + 1 : ℕ) : ℂ) := by
      have := congrArg (fun k : ℕ => (k : ℂ)) h2
      push_cast at this ⊢
      exact_mod_cast this
    have hexpand : (z / 2 ^ (j : ℕ)) ^ 2 /
        (((m + 1) / 2 ^ (j : ℕ) : ℕ) : ℂ) ^ 2 =
        z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2 := by
      rw [div_pow, div_div, ← mul_pow, hkey]
    rw [neg_div, hexpand]
    ring
  calc rvachevFourierProduct z
      = ∏' h : ℕ, complexSinc (π * (z / 2 ^ h)) :=
        rvachevFourierProduct_eq_tprod_scale z
    _ = ∏' h : ℕ, ∏' r : ℕ, F (h, r) := by
        refine tprod_congr fun h => ?_
        rw [← tprod_one_add_sineTerm (z / 2 ^ h)]
    _ = ∏' p : ℕ × ℕ, F p := (hFmult.tprod_prod' hfib).symm
    _ = ∏' σ : Σ m : ℕ, Fin (padicValNat 2 (m + 1) + 1),
          F (dyadicFactorEquiv.symm σ) :=
        (dyadicFactorEquiv.symm.tprod_eq F).symm
    _ = ∏' m : ℕ, ∏' j : Fin (padicValNat 2 (m + 1) + 1),
          F (dyadicFactorEquiv.symm ⟨m, j⟩) := by
        refine Multipliable.tprod_sigma' (fun m => ⟨_, hasProd_fintype _⟩) ?_
        exact (dyadicFactorEquiv.symm.multipliable_iff).mpr hFmult
    _ = ∏' m : ℕ, (1 - z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2) ^
          (padicValNat 2 (m + 1) + 1) := by
        refine tprod_congr fun m => ?_
        rw [tprod_congr fun j => hfactor m j, tprod_fintype,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Fabius
