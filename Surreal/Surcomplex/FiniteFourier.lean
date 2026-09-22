import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Star.BigOperators
import Mathlib.RingTheory.RootsOfUnity.Complex
import Surreal.Surcomplex.FiniteTrigonometry
import Surreal.Surcomplex.ComplexEmbedding

/-!
# Finite Fourier calculus on the surreal circle

This file proves the finite quadrature identity `trigonometry:eq:orthogonalityfinite` and every
clause of `trigonometry:thm:fourier` (finite Fourier inversion, sampling and Parseval) of
`docs/surcomplex/trigonometry/article.tex`.

The identities are first proved over an arbitrary field `K` containing a primitive `M`-th root
of unity `ζ`; no characteristic assumption is needed, since such a root forces `(M : K) ≠ 0`.

* `orthogonality`: `(1/M) ∑_{j<M} ζ^{jk}` is `1` if `M ∣ k` and `0` otherwise, `k ∈ ℤ`.
* `fourier_inversion` (`trigonometry:eq:fourierinverse`): for `T(u) = ∑_{k=-N}^{N} c_k u^k`
  (`laurentEval`) and `M > 2N`, `c_k = (1/M) ∑_j T(u₀ζ^j) (u₀ζ^j)^{-k}` for `|k| ≤ N` and
  every nonzero base point `u₀`.
* `parseval_samples` (`trigonometry:eq:parsevalsample`): in a field with a star structure for
  which `star ζ = ζ⁻¹` and `star u₀ = u₀⁻¹`, `(1/M) ∑_j T(u₀ζ^j) · star T(u₀ζ^j)` equals
  `∑_{k=-N}^{N} c_k · star c_k`.
* `dft_inversion`, `dft_parseval` (`trigonometry:eq:dft`): for arbitrary `z_0, …, z_{M-1}` and
  `ẑ_k = (1/M) ∑_j z_j ζ^{-jk}` (`dft`), `z_j = ∑_{k<M} ẑ_k ζ^{jk}` for `j < M` and
  `∑_j z_j · star z_j = M ∑_k ẑ_k · star ẑ_k`.

These are then instantiated on the actual surcomplex field `SC` with `ζ = cis(2π/M)`, defined as
the project's finite phase `finitePhase` of the real angle `2π/M` (`zeta`). It is the ordinary
root `exp(2πi/M)` and a primitive `M`-th root of unity. A base direction `u₀ ∈ 𝕋(No)` is a
surcomplex of surreal modulus `1`, and `|z|²` is the square of the surreal-valued `modulus`,
so `surcomplex_parseval_samples` and `surcomplex_dft_parseval` are identities in `No`. The
coefficients `c_k` and samples `z_j` are arbitrary surcomplex numbers; inversion needs only
`u₀ ≠ 0`. Coefficient families are functions `ℤ → SC` (resp. `ℕ → SC`) of which only the
indices `-N, …, N` (resp. `0, …, M - 1`) enter.

Nothing in `trigonometry:eq:orthogonalityfinite` or `trigonometry:thm:fourier` remains pending.
The later coefficientwise integration and positivity statements of the same section are not
treated here.
-/

universe u

namespace Surreal.FiniteFourier

open Finset

noncomputable section

section Generic

variable {K : Type*} [Field K] {M N : ℕ} {ζ : K}

/-- A field containing a primitive `M`-th root of unity, `M > 0`, has `M ≠ 0`. -/
theorem cast_ne_zero_of_isPrimitiveRoot (hζ : IsPrimitiveRoot ζ M) (hM : 0 < M) :
    (M : K) ≠ 0 := by
  haveI : NeZero M := ⟨hM.ne'⟩
  exact hζ.neZero'.out

/-- The unnormalized finite geometric sum behind `trigonometry:eq:orthogonalityfinite`. -/
theorem sum_zpow_mul (hζ : IsPrimitiveRoot ζ M) (k : ℤ) :
    ∑ j ∈ range M, ζ ^ ((j : ℤ) * k) = if (M : ℤ) ∣ k then (M : K) else 0 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have hterm : ∀ j : ℕ, ζ ^ ((j : ℤ) * k) = (ζ ^ k) ^ j := by
    intro j
    rw [mul_comm, zpow_mul, zpow_natCast]
  simp_rw [hterm]
  split_ifs with hdvd
  · rw [(hζ.zpow_eq_one_iff_dvd k).mpr hdvd]
    simp
  · have hne : ζ ^ k ≠ 1 := fun h => hdvd ((hζ.zpow_eq_one_iff_dvd k).mp h)
    have hpow : (ζ ^ k) ^ M = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- `trigonometry:eq:orthogonalityfinite`: `(1/M) ∑_{j<M} ζ^{jk}` is `1` if `M ∣ k` and `0`
otherwise, for a primitive `M`-th root of unity `ζ` in any field. -/
theorem orthogonality (hζ : IsPrimitiveRoot ζ M) (hM : 0 < M) (k : ℤ) :
    (M : K)⁻¹ * ∑ j ∈ range M, ζ ^ ((j : ℤ) * k) = if (M : ℤ) ∣ k then 1 else 0 := by
  have hM0 := cast_ne_zero_of_isPrimitiveRoot hζ hM
  rw [sum_zpow_mul hζ k]
  split_ifs
  · exact inv_mul_cancel₀ hM0
  · exact mul_zero _

/-- Orthogonality inside a window of width below `M`: only the diagonal survives. -/
theorem sum_zpow_mul_sub (hζ : IsPrimitiveRoot ζ M) {l k : ℤ} (h : |l - k| < M) :
    ∑ j ∈ range M, ζ ^ ((j : ℤ) * (l - k)) = if l = k then (M : K) else 0 := by
  rw [sum_zpow_mul hζ]
  by_cases hlk : l = k
  · subst hlk
    simp
  · have hd : ¬ (M : ℤ) ∣ l - k := fun hd =>
      hlk (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hd h))
    rw [if_neg hd, if_neg hlk]

/-- The finite Laurent sum `T(u) = ∑_{k=-N}^{N} c_k u^k`. -/
def laurentEval (N : ℕ) (c : ℤ → K) (u : K) : K :=
  ∑ l ∈ Icc (-(N : ℤ)) N, c l * u ^ l

/-- Expanding one sampled term `T(u₀ζ^j) (u₀ζ^j)^{-k}` of the inversion formula. -/
theorem laurentEval_mul_zpow_sample (hζ0 : ζ ≠ 0) {u₀ : K} (hu₀ : u₀ ≠ 0) (c : ℤ → K)
    (j : ℕ) (k : ℤ) :
    laurentEval N c (u₀ * ζ ^ j) * (u₀ * ζ ^ j) ^ (-k) =
      ∑ l ∈ Icc (-(N : ℤ)) N, c l * u₀ ^ (l - k) * ζ ^ ((j : ℤ) * (l - k)) := by
  have hs : u₀ * ζ ^ j ≠ 0 := mul_ne_zero hu₀ (pow_ne_zero _ hζ0)
  rw [laurentEval, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, ← zpow_add₀ hs, ← sub_eq_add_neg, mul_zpow, ← zpow_natCast, ← zpow_mul,
    mul_assoc]

/-- `trigonometry:thm:fourier`, `trigonometry:eq:fourierinverse`, over any field: the `M`
samples `T(u₀ζ^j)` recover every coefficient `c_k`, `|k| ≤ N`, of a finite Laurent sum when
`M > 2N`, for any nonzero base point `u₀`. -/
theorem fourier_inversion (hζ : IsPrimitiveRoot ζ M) (hM : 2 * N < M) (c : ℤ → K) {u₀ : K}
    (hu₀ : u₀ ≠ 0) {k : ℤ} (hk : |k| ≤ N) :
    c k = (M : K)⁻¹ * ∑ j ∈ range M, laurentEval N c (u₀ * ζ ^ j) * (u₀ * ζ ^ j) ^ (-k) := by
  have hMpos : 0 < M := by omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hMpos.ne'
  have hM0 := cast_ne_zero_of_isPrimitiveRoot hζ hMpos
  have hk' := abs_le.mp hk
  simp_rw [laurentEval_mul_zpow_sample hζ0 hu₀]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_eq_single_of_mem k (mem_Icc.mpr ⟨hk'.1, hk'.2⟩)]
  · rw [sum_zpow_mul_sub hζ (by simpa using hMpos), if_pos rfl, sub_self, zpow_zero, mul_one,
      mul_comm (c k), ← mul_assoc, inv_mul_cancel₀ hM0, one_mul]
  · intro l hl hlk
    have hl' := mem_Icc.mp hl
    have hwin : |l - k| < M := by
      rw [abs_lt]
      constructor <;> omega
    rw [sum_zpow_mul_sub hζ hwin, if_neg hlk, mul_zero]

/-- On the unit circle of a star field, conjugating a sampled Laurent sum. -/
theorem star_laurentEval [StarRing K] (c : ℤ → K) {u : K} (hu : star u = u⁻¹) :
    star (laurentEval N c u) = ∑ l ∈ Icc (-(N : ℤ)) N, star (c l) * u ^ (-l) := by
  rw [laurentEval, star_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [star_mul', star_zpow₀, hu, inv_zpow']

/-- `trigonometry:thm:fourier`, `trigonometry:eq:parsevalsample`: sampled Parseval identity
for a finite Laurent sum, in any field with a conjugation for which `ζ` and the base point `u₀`
are unitary. -/
theorem parseval_samples [StarRing K] (hζ : IsPrimitiveRoot ζ M) (hM : 2 * N < M)
    (hζs : star ζ = ζ⁻¹) {u₀ : K} (hu₀ : u₀ ≠ 0) (hu₀s : star u₀ = u₀⁻¹) (c : ℤ → K) :
    (M : K)⁻¹ * ∑ j ∈ range M,
        laurentEval N c (u₀ * ζ ^ j) * star (laurentEval N c (u₀ * ζ ^ j)) =
      ∑ l ∈ Icc (-(N : ℤ)) N, c l * star (c l) := by
  have hMpos : 0 < M := by omega
  have hM0 := cast_ne_zero_of_isPrimitiveRoot hζ hMpos
  have hs : ∀ j : ℕ, star (u₀ * ζ ^ j) = (u₀ * ζ ^ j)⁻¹ := by
    intro j
    rw [star_mul', star_pow, hu₀s, hζs, mul_inv, inv_pow]
  have hexp : ∀ j : ℕ, laurentEval N c (u₀ * ζ ^ j) * star (laurentEval N c (u₀ * ζ ^ j)) =
      ∑ l ∈ Icc (-(N : ℤ)) N,
        star (c l) * (laurentEval N c (u₀ * ζ ^ j) * (u₀ * ζ ^ j) ^ (-l)) := by
    intro j
    rw [star_laurentEval c (hs j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := mem_Icc.mp hl
  have hinv := fourier_inversion hζ hM c hu₀ (k := l) (abs_le.mpr ⟨hl'.1, hl'.2⟩)
  have hsum : ∑ j ∈ range M, laurentEval N c (u₀ * ζ ^ j) * (u₀ * ζ ^ j) ^ (-l) =
      (M : K) * c l := by
    rw [hinv, ← mul_assoc, mul_inv_cancel₀ hM0, one_mul]
  rw [← Finset.mul_sum, hsum, mul_left_comm, inv_mul_cancel_left₀ hM0, mul_comm]

/-- The discrete Fourier coefficients `ẑ_k = (1/M) ∑_{j<M} z_j ζ^{-jk}`. -/
def dft (ζ : K) (M : ℕ) (z : ℕ → K) (k : ℕ) : K :=
  (M : K)⁻¹ * ∑ j ∈ range M, z j * ζ ^ (-((j : ℤ) * k))

/-- `trigonometry:thm:fourier`, `trigonometry:eq:dft`, inversion over any field:
`z_j = ∑_{k<M} ẑ_k ζ^{jk}` for `j < M`. -/
theorem dft_inversion (hζ : IsPrimitiveRoot ζ M) (z : ℕ → K) {j : ℕ} (hj : j < M) :
    z j = ∑ k ∈ range M, dft ζ M z k * ζ ^ ((j : ℤ) * k) := by
  have hMpos : 0 < M := by omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hMpos.ne'
  have hM0 := cast_ne_zero_of_isPrimitiveRoot hζ hMpos
  have hterm : ∀ k i : ℕ, z i * ζ ^ (-((i : ℤ) * k)) * ζ ^ ((j : ℤ) * k) =
      z i * ζ ^ ((k : ℤ) * ((j : ℤ) - i)) := by
    intro k i
    rw [mul_assoc, ← zpow_add₀ hζ0]
    congr 2
    ring
  symm
  calc ∑ k ∈ range M, dft ζ M z k * ζ ^ ((j : ℤ) * k)
      = ∑ k ∈ range M, ∑ i ∈ range M,
          (M : K)⁻¹ * (z i * ζ ^ ((k : ℤ) * ((j : ℤ) - i))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [dft, mul_assoc, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hterm k i]
    _ = (M : K)⁻¹ * ∑ i ∈ range M, z i * ∑ k ∈ range M, ζ ^ ((k : ℤ) * ((j : ℤ) - i)) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ = z j := by
        rw [Finset.sum_eq_single_of_mem j (mem_range.mpr hj)]
        · rw [sum_zpow_mul_sub hζ (by simpa using hMpos), if_pos rfl, mul_comm (z j),
            ← mul_assoc, inv_mul_cancel₀ hM0, one_mul]
        · intro i hi hij
          have hi' := mem_range.mp hi
          have hwin : |(j : ℤ) - i| < M := by
            rw [abs_lt]
            constructor <;> omega
          rw [sum_zpow_mul_sub hζ hwin, if_neg (fun h => hij (by exact_mod_cast h.symm)),
            mul_zero]

/-- `trigonometry:thm:fourier`, `trigonometry:eq:dft`, Parseval over a star field with
`star ζ = ζ⁻¹`: `∑_{j<M} z_j · star z_j = M ∑_{k<M} ẑ_k · star ẑ_k`. -/
theorem dft_parseval [StarRing K] (hζ : IsPrimitiveRoot ζ M) (hζs : star ζ = ζ⁻¹)
    (z : ℕ → K) :
    ∑ j ∈ range M, z j * star (z j) = M * ∑ k ∈ range M, dft ζ M z k * star (dft ζ M z k) := by
  rcases Nat.eq_zero_or_pos M with rfl | hMpos
  · simp
  have hM0 := cast_ne_zero_of_isPrimitiveRoot hζ hMpos
  have hstar : ∀ k : ℕ, star (dft ζ M z k) =
      (M : K)⁻¹ * ∑ j ∈ range M, star (z j) * ζ ^ ((j : ℤ) * k) := by
    intro k
    rw [dft, star_mul', star_inv₀, star_natCast, star_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', star_zpow₀, hζs, inv_zpow', neg_neg]
  symm
  calc (M : K) * ∑ k ∈ range M, dft ζ M z k * star (dft ζ M z k)
      = ∑ k ∈ range M, ∑ j ∈ range M,
          dft ζ M z k * (star (z j) * ζ ^ ((j : ℤ) * k)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hstar, mul_left_comm, mul_inv_cancel_left₀ hM0, Finset.mul_sum]
    _ = ∑ j ∈ range M, star (z j) * ∑ k ∈ range M, dft ζ M z k * ζ ^ ((j : ℤ) * k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = ∑ j ∈ range M, z j * star (z j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [← dft_inversion hζ z (mem_range.mp hj), mul_comm]

end Generic

section Surcomplex

open Surreal.Surcomplex Foundations

variable {M N : ℕ}

/-- The sampling root `ζ = cis(2π/M)`: the finite phase of the real angle `2π/M`. -/
def zeta (M : ℕ) : Surcomplex.{u} :=
  finitePhase (SignSequence.finiteOfReal (2 * Real.pi / M))

/-- `ζ = cis(2π/M)` is the ordinary complex root `exp(2πi/M)`. -/
theorem zeta_eq_ofComplex (M : ℕ) :
    zeta.{u} M = ofComplex (Complex.exp (2 * Real.pi * Complex.I / M)) := by
  rw [zeta, finitePhase_constant]
  congr 2
  push_cast
  ring

/-- `ζ = cis(2π/M)` is a primitive `M`-th root of unity in `SC`. -/
theorem isPrimitiveRoot_zeta (hM : 0 < M) : IsPrimitiveRoot (zeta.{u} M) M := by
  rw [zeta_eq_ofComplex]
  exact (Complex.isPrimitiveRoot_exp M hM.ne').map_of_injective ofComplex_injective

/-- The sampling root lies on the surreal unit circle: `|ζ| = 1`. -/
theorem modulus_zeta (M : ℕ) : modulus (zeta.{u} M) = 1 :=
  modulus_finitePhase _

/-- A point of the surreal unit circle `𝕋(No)` is nonzero. -/
theorem ne_zero_of_modulus_eq_one {z : Surcomplex.{u}} (hz : modulus z = 1) : z ≠ 0 := by
  rintro rfl
  rw [modulus_zero] at hz
  exact zero_ne_one hz

/-- On the surreal unit circle `𝕋(No)` conjugation is inversion. -/
theorem star_eq_inv_of_modulus_eq_one {z : Surcomplex.{u}} (hz : modulus z = 1) :
    star z = z⁻¹ := by
  rw [inv_eq_modulus, hz, one_pow, inv_one, one_smul]
  rfl

/-- The squared surreal modulus, viewed in `SC`, is `z * conj z`. -/
theorem ofReal_modulus_sq (z : Surcomplex.{u}) : ofReal (modulus z ^ 2) = z * star z := by
  rw [modulus_sq, ← mul_conj]
  rfl

/-- `trigonometry:eq:orthogonalityfinite` in `SC` for `ζ = cis(2π/M)`. -/
theorem surcomplex_orthogonality (hM : 0 < M) (k : ℤ) :
    (M : Surcomplex.{u})⁻¹ * ∑ j ∈ range M, zeta.{u} M ^ ((j : ℤ) * k) =
      if (M : ℤ) ∣ k then 1 else 0 :=
  orthogonality (isPrimitiveRoot_zeta hM) hM k

/-- `trigonometry:thm:fourier`, `trigonometry:eq:fourierinverse`: for surcomplex coefficients
`c_k` and `M > 2N`, the samples at `u₀ ζ^j` recover `c_k` for `|k| ≤ N`. The base point may be
any nonzero surcomplex, in particular any `u₀ ∈ 𝕋(No)`. -/
theorem surcomplex_fourier_inversion (hM : 2 * N < M) (c : ℤ → Surcomplex.{u})
    {u₀ : Surcomplex.{u}} (hu₀ : u₀ ≠ 0) {k : ℤ} (hk : |k| ≤ N) :
    c k = (M : Surcomplex.{u})⁻¹ * ∑ j ∈ range M,
      laurentEval N c (u₀ * zeta M ^ j) * (u₀ * zeta M ^ j) ^ (-k) :=
  fourier_inversion (isPrimitiveRoot_zeta (by omega)) hM c hu₀ hk

/-- `trigonometry:thm:fourier`, `trigonometry:eq:parsevalsample`: for surcomplex coefficients,
`M > 2N` and `u₀ ∈ 𝕋(No)`, `(1/M) ∑_j |T(u₀ζ^j)|^2 = ∑_{k=-N}^{N} |c_k|^2` in `No`. The circle
condition is encoded as `modulus u₀ = 1`, equivalent to `u₀ ū₀ = 1` since the modulus is
nonnegative with square the norm square. -/
theorem surcomplex_parseval_samples (hM : 2 * N < M) (c : ℤ → Surcomplex.{u})
    {u₀ : Surcomplex.{u}} (hu₀ : modulus u₀ = 1) :
    (M : SignSequence.{u})⁻¹ *
        ∑ j ∈ range M, modulus (laurentEval N c (u₀ * zeta M ^ j)) ^ 2 =
      ∑ l ∈ Icc (-(N : ℤ)) N, modulus (c l) ^ 2 := by
  apply ofReal_injective
  simp only [map_mul, map_inv₀, map_natCast, map_sum, ofReal_modulus_sq]
  exact parseval_samples (isPrimitiveRoot_zeta (by omega)) hM
    (star_eq_inv_of_modulus_eq_one (modulus_zeta M)) (ne_zero_of_modulus_eq_one hu₀)
    (star_eq_inv_of_modulus_eq_one hu₀) c

/-- `trigonometry:thm:fourier`, `trigonometry:eq:dft`, inversion: for arbitrary surcomplex
`z_0, …, z_{M-1}`, `z_j = ∑_{k<M} ẑ_k ζ^{jk}`. -/
theorem surcomplex_dft_inversion (z : ℕ → Surcomplex.{u}) {j : ℕ} (hj : j < M) :
    z j = ∑ k ∈ range M, dft (zeta M) M z k * zeta M ^ ((j : ℤ) * k) :=
  dft_inversion (isPrimitiveRoot_zeta (by omega)) z hj

/-- `trigonometry:thm:fourier`, `trigonometry:eq:dft`, Parseval:
`∑_{j<M} |z_j|^2 = M ∑_{k<M} |ẑ_k|^2` in `No`. -/
theorem surcomplex_dft_parseval (z : ℕ → Surcomplex.{u}) :
    ∑ j ∈ range M, modulus (z j) ^ 2 =
      M * ∑ k ∈ range M, modulus (dft (zeta M) M z k) ^ 2 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  apply ofReal_injective
  simp only [map_mul, map_natCast, map_sum, ofReal_modulus_sq]
  exact dft_parseval (isPrimitiveRoot_zeta hM) (star_eq_inv_of_modulus_eq_one (modulus_zeta M)) z

end Surcomplex

end

end Surreal.FiniteFourier
