import IPRADerivations.Core.IntCertificates

/-!
# The finite steps of the rational Gram certificate

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/07_sw_bv.tex`, Proposition "Rational Gram
certificate": for `K = A A*` over `ℚ(i)` with `|K_rs|² ≤ k_rs²` and `Σ_s k_rs ≤ L`,
`Σ_r |Σ_n A_rn a_n|² ≤ L Σ_n |a_n|²`. Its proof uses two finite inequalities, both by exact sums of squares:

"The needed Cauchy–Schwarz inequality has the exact sum-of-squares proof
`(Σ|u_i|²)(Σ|v_i|²) − |Σ ū_i v_i|² = Σ_{i<j} |u_i v_j − u_j v_i|² ≥ 0`", and "for `k > 0` and `|z|² ≤ k²`, expanding
the nonnegative square `|ku − zv|²` proves `2 Re(ū z v) ≤ k (|u|² + |v|²)`. Indeed multiply the desired inequality
by `k`, and bound `|z|² |v|²` by `k² |v|²`."

Gaussian numbers are pairs of integer terms (`ZT`, real and imaginary parts, denominators cleared), in a fixed
metalevel dimension `d`:

* `lagrange_c`: the complex Lagrange identity
  `Σ_i Σ_j |u_i v_j − u_j v_i|² = 2 (‖u‖² ‖v‖² − |⟨u, v⟩|²)` in every commutative ring;
* `gauss_cs`: `|Σ ū_i v_i|² ≤ (Σ |u_i|²)(Σ |v_i|²)`, an integer certificate from that identity;
* `pair_bound`: for a natural `k` with `|z|² ≤ k²`, `2k Re(ū z v) ≤ k² (|u|² + |v|²)`, from
  `k²(|u|² + |v|²) − 2k Re(ū z v) = |ku − zv|² + (k² − |z|²)|v|²`: the packet's inequality multiplied by `k`.

The assembly of the proposition (dividing by `k_rs`, the zero test for `k_rs = 0` and for `‖Aa‖ = 0`) is not
derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.GramCertificate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The complex Lagrange identity for `u = a + i b`, `v = c + i e`:
`Σ_i Σ_j |u_i v_j − u_j v_i|² = 2 (‖u‖² ‖v‖² − |⟨u, v⟩|²)`. -/
theorem lagrange_c {R : Type*} [CommRing R] {d : ℕ} (a b c e : Fin d → R) :
    ∑ i, ∑ j, ((a i * c j - b i * e j - a j * c i + b j * e i) ^ 2 +
        (a i * e j + b i * c j - a j * e i - b j * c i) ^ 2) =
      2 * ((∑ i, (a i ^ 2 + b i ^ 2)) * (∑ i, (c i ^ 2 + e i ^ 2)) -
        ((∑ i, (a i * c i + b i * e i)) ^ 2 + (∑ i, (a i * e i - b i * c i)) ^ 2)) := by
  have h : ∀ i j, (a i * c j - b i * e j - a j * c i + b j * e i) ^ 2 +
      (a i * e j + b i * c j - a j * e i - b j * c i) ^ 2 =
      (a i ^ 2 + b i ^ 2) * (c j ^ 2 + e j ^ 2) + (a j ^ 2 + b j ^ 2) * (c i ^ 2 + e i ^ 2) -
        2 * ((a i * c i + b i * e i) * (a j * c j + b j * e j)) -
        2 * ((a i * e i - b i * c i) * (a j * e j - b j * c j)) := fun i j => by ring
  simp only [h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

section Gauss

variable {d : ℕ} (a b c e : Fin d → ZT n)

/-- Cauchy–Schwarz for Gaussian vectors `u = a + i b`, `v = c + i e`:
`|Σ ū_i v_i|² ≤ (Σ |u_i|²)(Σ |v_i|²)`. -/
theorem gauss_cs :
    Γ ⊢[PRAAx] zle
      (ZT.sq (ZT.sumFin fun i => a i * c i + b i * e i) + ZT.sq (ZT.sumFin fun i => a i * e i - b i * c i))
      ((ZT.sumFin fun i => ZT.sq (a i) + ZT.sq (b i)) * (ZT.sumFin fun i => ZT.sq (c i) + ZT.sq (e i))) := by
  refine zle_of_comb_two (∑ i, ∑ j, (ZT.toZ Γ (a i * c j - b i * e j - a j * c i + b j * e i) ^ 2 +
      ZT.toZ Γ (a i * e j + b i * c j - a j * e i - b j * c i) ^ 2)) ?_
    (nn_sum _ _ fun i _ => nn_sum _ _ fun j _ => nn_add (nn_zsq _) (nn_zsq _))
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_sq, ZT.toZ_sumFin]
  exact (lagrange_c (fun i => ZT.toZ Γ (a i)) (fun i => ZT.toZ Γ (b i)) (fun i => ZT.toZ Γ (c i))
    (fun i => ZT.toZ Γ (e i))).symm

end Gauss

/-- For a natural `k` with `|z|² ≤ k²` (`z = z₁ + i z₂`): `2k Re(ū z v) ≤ k² (|u|² + |v|²)`. -/
theorem pair_bound {k : PTm n} {z₁ z₂ : ZT n} (u₁ u₂ v₁ v₂ : ZT n)
    (hz : Γ ⊢[PRAAx] zle (ZT.sq z₁ + ZT.sq z₂) (ZT.ofNat (k * k))) :
    Γ ⊢[PRAAx] zle
      (ZT.natLit 2 * ZT.ofNat k * (u₁ * (z₁ * v₁ - z₂ * v₂) + u₂ * (z₁ * v₂ + z₂ * v₁)))
      (ZT.ofNat (k * k) * (ZT.sq u₁ + ZT.sq u₂ + (ZT.sq v₁ + ZT.sq v₂))) := by
  refine zle_of_comb (ZT.toZ Γ (ZT.ofNat k * u₁ - (z₁ * v₁ - z₂ * v₂)) ^ 2 +
      ZT.toZ Γ (ZT.ofNat k * u₂ - (z₁ * v₂ + z₂ * v₁)) ^ 2 +
      zsl hz * (ZT.toZ Γ v₁ ^ 2 + ZT.toZ Γ v₂ ^ 2)) ?_
    (nn_add (nn_add (nn_zsq _) (nn_zsq _)) (nn_mul (nn_zsl _) (nn_add (nn_zsq _) (nn_zsq _))))
  simp only [zsl_def, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_sq, ZT.toZ_natLit, ZT.toZ_ofNat, Q.mk_mul, map_mul,
    Nat.cast_ofNat]
  ring

end LeanProofs.IPRA.AnalyticNumberTheory.GramCertificate
