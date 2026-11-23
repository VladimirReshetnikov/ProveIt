import IPRADerivations.Core.IntCertificates

/-!
# The Doeblin contraction of a finite Markov table

Packet: `combinatorics/Combinatorics-iPRA`, `words.tex`, result 70 ("Finite dynamics and a quantitative
Markov-chain bound"): for a nonnegative integer table `W` with row sums `D`, column minima `a_j` and
`s = ∑_j a_j`, "`‖u P^t − v P^t‖₁ ≤ (1 − s/D)^t ‖u − v‖₁`". One step of the proof: "Writing
`R_{ij} = w_{ij} − a_j ≥ 0`, its row sums are `D − s`. Any row difference `z = u − v` has sum zero, so
`D z P = z R`. The triangle inequality in each column gives
`D ‖zP‖₁ ≤ ∑_i |z_i| ∑_j R_{ij} = (D − s) ‖z‖₁`."

The table and the vectors are integer terms indexed by `Fin N`; the absolute values `|z_i|` are represented by
terms `t_i` with `−t_i ≤ z_i ≤ t_i`. As iPRA derivations:

* `column_upper`, `column_lower`: for a vector `z` of sum zero, `|∑_i z_i w_{ij}| ≤ ∑_i t_i (w_{ij} − a_j)` in
  every column `j`;
* `total`: these column bounds sum to `(D − s) ∑_i t_i`.

Together: the `ℓ¹` norm of `z W` is at most `(D − s) ‖z‖₁`. Not derived: the iteration over `t`, the stationary
tree formula, the estimate `(1 − x)^D (1 + D x) ≤ 1`, and the eventual periodicity of an orbit.
-/

namespace LeanProofs.IPRA.Combinatorics.MarkovContraction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n N : ℕ} {Γ : List (Fm PTm n)}

/-! ## Identities in a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

theorem col_upper_identity (z t c : Fin N → R) (a : R) (h : ∑ i, z i = 0) :
    ∑ i, t i * (c i - a) - ∑ i, z i * c i = ∑ i, (t i - z i) * (c i - a) := by
  have e : ∑ i, (t i - z i) * (c i - a) = ∑ i, t i * (c i - a) - ∑ i, z i * c i + a * ∑ i, z i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, h]
  ring

theorem col_lower_identity (z t c : Fin N → R) (a : R) (h : ∑ i, z i = 0) :
    ∑ i, z i * c i - -∑ i, t i * (c i - a) = ∑ i, (z i - -t i) * (c i - a) := by
  have e : ∑ i, (z i - -t i) * (c i - a) = ∑ i, z i * c i + ∑ i, t i * (c i - a) - a * ∑ i, z i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, h]
  ring

theorem total_identity (c : Fin N → Fin N → R) (a t : Fin N → R) (D : R) (h : ∀ i, ∑ j, c i j = D) :
    ∑ j, ∑ i, t i * (c i j - a j) = (D - ∑ j, a j) * ∑ i, t i := by
  have e : ∀ i, ∑ j, t i * (c i j - a j) = t i * (D - ∑ j, a j) := fun i => by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, h i]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => e i, ← Finset.sum_mul]
  ring

end Ring

/-! ## The derivations -/

/-- The upper column bound: `∑_i z_i w_{ij} ≤ ∑_i t_i (w_{ij} − a_j)`. -/
theorem column_upper (w : Fin N → Fin N → ZT n) (a z t : Fin N → ZT n)
    (hz : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin z) (ZT.natLit 0)) (hzt : ∀ i, Γ ⊢[PRAAx] zle (z i) (t i))
    (ha : ∀ i j, Γ ⊢[PRAAx] zle (a j) (w i j)) (j : Fin N) :
    Γ ⊢[PRAAx] zle (ZT.sumFin fun i => z i * w i j) (ZT.sumFin fun i => t i * (w i j - a j)) := by
  have h : ∑ i, ZT.toZ Γ (z i) = 0 := by
    have e := ZT.toZ_eq hz
    simpa only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_zero] using e
  have L := col_upper_identity (fun i => ZT.toZ Γ (z i)) (fun i => ZT.toZ Γ (t i))
    (fun i => ZT.toZ Γ (w i j)) (ZT.toZ Γ (a j)) h
  beta_reduce at L
  refine zle_of_comb (∑ i, zsl (hzt i) * zsl (ha i j)) ?_
    (nn_sum _ _ fun i _ => nn_mul (nn_zsl _) (nn_zsl _))
  zsimp
  exact L

/-- The lower column bound: `−∑_i t_i (w_{ij} − a_j) ≤ ∑_i z_i w_{ij}`. -/
theorem column_lower (w : Fin N → Fin N → ZT n) (a z t : Fin N → ZT n)
    (hz : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin z) (ZT.natLit 0)) (hzt : ∀ i, Γ ⊢[PRAAx] zle (-t i) (z i))
    (ha : ∀ i j, Γ ⊢[PRAAx] zle (a j) (w i j)) (j : Fin N) :
    Γ ⊢[PRAAx] zle (-ZT.sumFin fun i => t i * (w i j - a j)) (ZT.sumFin fun i => z i * w i j) := by
  have h : ∑ i, ZT.toZ Γ (z i) = 0 := by
    have e := ZT.toZ_eq hz
    simpa only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_zero] using e
  have L := col_lower_identity (fun i => ZT.toZ Γ (z i)) (fun i => ZT.toZ Γ (t i))
    (fun i => ZT.toZ Γ (w i j)) (ZT.toZ Γ (a j)) h
  beta_reduce at L
  refine zle_of_comb (∑ i, zsl (hzt i) * zsl (ha i j)) ?_
    (nn_sum _ _ fun i _ => nn_mul (nn_zsl _) (nn_zsl _))
  zsimp
  exact L

/-- The column bounds sum to `(D − s) ∑_i t_i`. -/
theorem total (w : Fin N → Fin N → ZT n) (a t : Fin N → ZT n) (D : ZT n)
    (hD : ∀ i, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => w i j) D) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => ZT.sumFin fun i => t i * (w i j - a j))
      ((D - ZT.sumFin a) * ZT.sumFin t) := by
  have hD1 : ∀ i, ∑ j, ZT.toZ Γ (w i j) = ZT.toZ Γ D := fun i => by
    have e := ZT.toZ_eq (hD i)
    simpa only [ZT.toZ_sumFin] using e
  have L := total_identity (fun i j => ZT.toZ Γ (w i j)) (fun j => ZT.toZ Γ (a j))
    (fun i => ZT.toZ Γ (t i)) (ZT.toZ Γ D) hD1
  beta_reduce at L
  apply ZT.derive
  zsimp
  exact L

end LeanProofs.IPRA.Combinatorics.MarkovContraction
