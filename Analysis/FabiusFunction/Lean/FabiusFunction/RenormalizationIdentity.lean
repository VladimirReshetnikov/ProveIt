import FabiusFunction.FourierProduct

/-!
# The renormalization identity for `Φ`

The audits' scaling relation, at the level of the sinc product itself:

`Φ(z) = sinc(πz) · Φ(z/2)`,   `Φ(z) = (∏_{k<n} sinc(πz/2ᵏ)) · Φ(z/2ⁿ)`.

The obvious route — splitting the `ℕ`-indexed product at its zeroth
term — is unavailable: the index-shift lemmas
(`Multipliable.tprod_eq_zero_mul` and friends) need a commutative
*group*, and `ℂ` under multiplication is only a monoid, so instance
search there does not merely fail, it spins.  Instead we peel the
factor as a *set* complement: `HasProd.mul_compl` needs only a
commutative monoid, `hasProd_singleton` supplies the block `{0}`, and
an explicit equivalence `ℕ ≃ ↥({0}ᶜ)` identifies the rest with the
factors of `Φ(z/2)`.

* `succEquivComplZero` — the shift equivalence.
* `rvachevFourierProduct_scaling` — **the renormalization identity**.
* `rvachevFourierProduct_shell` — its `n`-fold form.
-/

set_option autoImplicit false

open Filter Topology Real

namespace Fabius

/-- `ℕ` enumerates the nonzero naturals. -/
def succEquivComplZero : ℕ ≃ ↥(({0} : Set ℕ)ᶜ) where
  toFun k := ⟨k + 1, by simp⟩
  invFun p := p.val - 1
  left_inv k := by simp
  right_inv := by
    rintro ⟨n, hn⟩
    have hn0 : n ≠ 0 := by simpa using hn
    apply Subtype.ext
    show n - 1 + 1 = n
    omega

/-- **The renormalization identity**: `Φ(z) = sinc(πz)·Φ(z/2)`. -/
theorem rvachevFourierProduct_scaling (z : ℂ) :
    rvachevFourierProduct z =
      complexSinc (Real.pi * z) * rvachevFourierProduct (z / 2) := by
  set f : ℕ → ℂ := fun n => complexSinc ((Real.pi : ℂ) * z / 2 ^ n)
    with hf
  have hfull : HasProd f (rvachevFourierProduct z) :=
    (sincFactors_multipliable z).hasProd
  -- the zeroth factor
  have hzero : HasProd (f ∘ (↑) : ({0} : Set ℕ) → ℂ) (f 0) :=
    hasProd_singleton 0 f
  -- the remaining factors are those of `Φ(z/2)`
  have hhalf : HasProd
      (fun k : ℕ => complexSinc ((Real.pi : ℂ) * (z / 2) / 2 ^ k))
      (rvachevFourierProduct (z / 2)) :=
    (sincFactors_multipliable (z / 2)).hasProd
  have hcompl : HasProd (f ∘ (↑) : (({0} : Set ℕ)ᶜ : Set ℕ) → ℂ)
      (rvachevFourierProduct (z / 2)) := by
    rw [← Equiv.hasProd_iff succEquivComplZero]
    have hfun : ((f ∘ (↑) : (({0} : Set ℕ)ᶜ : Set ℕ) → ℂ) ∘
        succEquivComplZero) =
        fun k : ℕ => complexSinc ((Real.pi : ℂ) * (z / 2) / 2 ^ k) := by
      funext k
      show complexSinc ((Real.pi : ℂ) * z / 2 ^ (k + 1)) =
        complexSinc ((Real.pi : ℂ) * (z / 2) / 2 ^ k)
      congr 1
      rw [pow_succ]
      ring
    rw [hfun]
    exact hhalf
  have hmul := hzero.mul_compl hcompl
  have hzeroval : f 0 = complexSinc (Real.pi * z) := by
    show complexSinc ((Real.pi : ℂ) * z / 2 ^ (0:ℕ)) =
      complexSinc (Real.pi * z)
    rw [pow_zero, div_one]
  rw [hzeroval] at hmul
  exact hfull.unique hmul

/-- **The shell form**: `Φ(z) = (∏_{k<n} sinc(πz/2ᵏ))·Φ(z/2ⁿ)`. -/
theorem rvachevFourierProduct_shell (n : ℕ) (z : ℂ) :
    rvachevFourierProduct z =
      (∏ k ∈ Finset.range n,
        complexSinc ((Real.pi : ℂ) * z / 2 ^ k)) *
      rvachevFourierProduct (z / 2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := rvachevFourierProduct_scaling (z / 2 ^ n)
      have harg : (Real.pi : ℂ) * (z / 2 ^ n) =
          (Real.pi : ℂ) * z / 2 ^ n := by ring
      have hhalf : (z / 2 ^ n) / 2 = z / 2 ^ (n + 1) := by
        rw [pow_succ]
        ring
      rw [harg, hhalf] at hstep
      rw [ih, hstep, Finset.prod_range_succ]
      ring

end Fabius
