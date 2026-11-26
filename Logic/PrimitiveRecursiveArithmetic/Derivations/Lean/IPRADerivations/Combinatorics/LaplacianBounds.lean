import IPRADerivations.Combinatorics.GraphIncidence

/-!
# Eigenvalue bounds for the graph Laplacian

Packet: `combinatorics/graph-ipra`, `tex/spectral.tex`, Theorem 9.1 (`spec:energy`, "Laplacian energy, nullity and
eigenvalue bounds"): "Every rational eigenvalue of `L` is an integer in `[0, 2Δ]`." The graph has vertex set
`Fin k` and a symmetric matrix `A v w` of nonnegative integer-term weights with row sums at most `Δ`; the energy
is `E = ∑_v ∑_w A_{vw} (x_v − x_w)² = 2 xᵀ L x` (`Combinatorics/GraphIncidence.laplacian_energy`). As iPRA
derivations:

* `energy_upper`: `E ≤ 4 Δ ∑_v x_v²`: "Since `(a − b)² ≤ 2a² + 2b²` by `(a + b)² ≥ 0`, summing over nonloops
  proves the upper bound";
* `eigen_range`: for an eigenpair with eigenvalue `p/q`, `q ≥ 0`, given as `q (L x)_v = p x_v`:
  `0 ≤ p N` and `p N ≤ 2 Δ q N` for `N = ∑_v x_v²` ("`xᵀ L x = λ ∑_v x_v²` has positive denominator sum");
* `mean_zero_pairs`: "all column sums of `L` vanish, hence `λ ≠ 0` forces `∑_v x_v = 0`. Expansion gives
  `∑_{u<v} (x_u − x_v)² = n ∑_v x_v²`", over ordered pairs.

Not derived: integrality of rational eigenvalues, the kernel basis, and the lower bound `λ ≥ 2/(n − 1)²`.
-/

namespace LeanProofs.IPRA.Combinatorics.LaplacianBounds

open_ipra
open LeanProofs.IPRA.Combinatorics.GraphIncidence (laplacian_identity)

variable {n k : ℕ} {Γ : List (Fm PTm n)}

/-! ## Identities in a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

/-- `∑ a (x_v + x_w)² + ∑ a (x_v − x_w)² = 4 ∑ d_v x_v²` for a symmetric matrix. -/
theorem energy_split (a : Fin k → Fin k → R) (x : Fin k → R) (hs : ∀ v w, a v w = a w v) :
    ∑ v, ∑ w, a v w * (x v + x w) ^ 2 + ∑ v, ∑ w, a v w * (x v - x w) ^ 2 =
      4 * ∑ v, (∑ w, a v w) * x v ^ 2 := by
  have h3 : ∑ v, ∑ w, a v w * x w ^ 2 = ∑ v, ∑ w, a v w * x v ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => by rw [hs w v]
  have hrow : ∑ v, ∑ w, a v w * x v ^ 2 = ∑ v, (∑ w, a v w) * x v ^ 2 :=
    Finset.sum_congr rfl fun v _ => (Finset.sum_mul _ _ _).symm
  have e : ∑ v, ∑ w, a v w * (x v + x w) ^ 2 + ∑ v, ∑ w, a v w * (x v - x w) ^ 2 =
      2 * ∑ v, ∑ w, a v w * x v ^ 2 + 2 * ∑ v, ∑ w, a v w * x w ^ 2 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [e, h3, hrow]
  ring

/-- The certificate identity of the upper bound. -/
theorem energy_upper_identity (a : Fin k → Fin k → R) (x : Fin k → R) (D : R) (hs : ∀ v w, a v w = a w v) :
    4 * D * ∑ v, x v ^ 2 - ∑ v, ∑ w, a v w * (x v - x w) ^ 2 =
      4 * ∑ v, (D - ∑ w, a v w) * x v ^ 2 + ∑ v, ∑ w, a v w * (x v + x w) ^ 2 := by
  have q : ∀ v, (D - ∑ w, a v w) * x v ^ 2 = D * x v ^ 2 - (∑ w, a v w) * x v ^ 2 := by
    intro v
    ring
  have hD : ∑ v, (D - ∑ w, a v w) * x v ^ 2 = D * ∑ v, x v ^ 2 - ∑ v, (∑ w, a v w) * x v ^ 2 := by
    rw [Finset.sum_congr rfl fun v _ => q v, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have es := energy_split a x hs
  rw [hD]
  linear_combination (-1 : R) * es

end Ring

/-! ## The derivations -/

/-- The Laplacian energy is at most `4 Δ ∑ x_v²`, that is `xᵀ L x ≤ 2 Δ xᵀ x`. -/
theorem energy_upper (A : Fin k → Fin k → ZT n) (x : Fin k → ZT n) (D : ZT n)
    (hs : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (A w v)) (hA : ∀ v w, Γ ⊢[PRAAx] zle (ZT.natLit 0) (A v w))
    (hd : ∀ v, Γ ⊢[PRAAx] zle (ZT.sumFin fun w => A v w) D) :
    Γ ⊢[PRAAx] zle (ZT.sumFin fun v => ZT.sumFin fun w => A v w * ZT.sq (x v - x w))
      (ZT.natLit 4 * D * ZT.sumFin fun v => ZT.sq (x v)) := by
  have hs1 : ∀ v w, ZT.toZ Γ (A v w) = ZT.toZ Γ (A w v) := fun v w => ZT.toZ_eq (hs v w)
  have L := energy_upper_identity (fun v w => ZT.toZ Γ (A v w)) (fun v => ZT.toZ Γ (x v)) (ZT.toZ Γ D) hs1
  beta_reduce at L
  refine zle_of_comb (4 * ∑ v, zsl (hd v) * ZT.toZ Γ (x v) ^ 2 +
      ∑ v, ∑ w, ZT.toZ Γ (A v w) * ZT.toZ Γ (x v + x w) ^ 2) ?_
    (nn_add (nn_mul (nn_ofNat 4) (nn_sum _ _ fun v _ => nn_mul (nn_zsl _) (nn_zsq _)))
      (nn_sum _ _ fun v _ => nn_sum _ _ fun w _ => nn_mul (nn_zle0 (hA v w)) (nn_zsq _)))
  zsimp
  exact L

/-- An eigenvalue `p/q` (`q ≥ 0`) of the Laplacian lies in `[0, 2Δ]`, cleared by `N = ∑ x_v²`. -/
theorem eigen_range (A : Fin k → Fin k → ZT n) (x : Fin k → ZT n) (D p q : ZT n)
    (hs : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (A w v)) (hA : ∀ v w, Γ ⊢[PRAAx] zle (ZT.natLit 0) (A v w))
    (hd : ∀ v, Γ ⊢[PRAAx] zle (ZT.sumFin fun w => A v w) D) (hq : Γ ⊢[PRAAx] zle (ZT.natLit 0) q)
    (he : ∀ v, Γ ⊢[PRAAx] ZT.eq
      (q * ((ZT.sumFin fun w => A v w) * x v - ZT.sumFin fun w => A v w * x w)) (p * x v)) :
    (Γ ⊢[PRAAx] zle (ZT.natLit 0) (p * ZT.sumFin fun v => ZT.sq (x v))) ∧
      (Γ ⊢[PRAAx] zle (p * ZT.sumFin fun v => ZT.sq (x v))
        (ZT.natLit 2 * D * q * ZT.sumFin fun v => ZT.sq (x v))) := by
  have hs1 : ∀ v w, ZT.toZ Γ (A v w) = ZT.toZ Γ (A w v) := fun v w => ZT.toZ_eq (hs v w)
  have he1 : ∀ v, ZT.toZ Γ q * ((∑ w, ZT.toZ Γ (A v w)) * ZT.toZ Γ (x v) -
      ∑ w, ZT.toZ Γ (A v w) * ZT.toZ Γ (x w)) = ZT.toZ Γ p * ZT.toZ Γ (x v) := fun v => by
    simpa only [ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_sumFin] using ZT.toZ_eq (he v)
  have lap := laplacian_identity (fun v w => ZT.toZ Γ (A v w)) (fun v => ZT.toZ Γ (x v)) hs1
  beta_reduce at lap
  have hpN : ZT.toZ Γ p * ∑ v, ZT.toZ Γ (x v) ^ 2 =
      ZT.toZ Γ q * ∑ v, ZT.toZ Γ (x v) * ((∑ w, ZT.toZ Γ (A v w)) * ZT.toZ Γ (x v) -
        ∑ w, ZT.toZ Γ (A v w) * ZT.toZ Γ (x w)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by linear_combination (-ZT.toZ Γ (x v)) * he1 v
  have hup := energy_upper A x D hs hA hd
  constructor
  · refine zle_of_comb_two (ZT.toZ Γ q * ∑ v, ∑ w, ZT.toZ Γ (A v w) * ZT.toZ Γ (x v - x w) ^ 2) ?_
      (nn_mul (nn_zle0 hq) (nn_sum _ _ fun v _ => nn_sum _ _ fun w _ => nn_mul (nn_zle0 (hA v w)) (nn_zsq _)))
    zsimp
    linear_combination (2 : Groth (Q Γ)) * hpN + ZT.toZ Γ q * lap
  · refine zle_of_comb_two (ZT.toZ Γ q * zsl hup) ?_ (nn_mul (nn_zle0 hq) (nn_zsl _))
    zsimp
    linear_combination (-2 : Groth (Q Γ)) * hpN - ZT.toZ Γ q * lap

/-- For a vector of sum zero, `∑_u ∑_v (x_u − x_v)² = 2 k ∑_v x_v²`. -/
theorem mean_zero_pairs (x : Fin k → ZT n) (h0 : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin x) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun u => ZT.sumFin fun v => ZT.sq (x u - x v))
      (ZT.natLit 2 * (ZT.natLit k * ZT.sumFin fun u => ZT.sq (x u))) := by
  have h : ∑ i, ZT.toZ Γ (x i) = 0 := by
    simpa only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_zero] using ZT.toZ_eq h0
  have e := pair_sq (fun i => ZT.toZ Γ (x i))
  beta_reduce at e
  apply ZT.derive
  zsimp
  rw [e, h]
  ring

end LeanProofs.IPRA.Combinatorics.LaplacianBounds
