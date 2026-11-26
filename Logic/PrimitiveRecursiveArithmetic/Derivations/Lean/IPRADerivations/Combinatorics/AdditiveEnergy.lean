import IPRADerivations.Core.IntCertificates

/-!
# The additive energy bound

Packet: `combinatorics/Combinatorics-iPRA`, `additive.tex`, result 59 ("Three elementary estimates of Ruzsa
type"), third estimate: "If `r(s) = #{(a, b) ∈ A × B : a + b = s}`, then `(|A| |B|)² ≤ |A + B| ∑_s r(s)²`."
The sets are indexed by `Fin a` and `Fin b`, the support `A + B` by `Fin m`, and the addition table is a family
`T x y s` of integer terms with `∑_s T x y s = 1` (each pair has exactly one sum). As iPRA derivations:

* `total`: "`∑_s r(s) = |A| |B|`";
* `energy`: `(a b)² ≤ m ∑_s r(s)²`, by the finite Cauchy inequality (`Core/IntCertificates.cauchy_int`): "expand
  `m ∑_i u_i² − (∑_i u_i)² = ∑_{i<j} (u_i − u_j)²` and use nonnegativity. Apply this to the support `A + B`."

Not derived: the two covering estimates of result 59 (the Ruzsa triangle inequality and the covering lemma).
-/

namespace LeanProofs.IPRA.Combinatorics.AdditiveEnergy

open_ipra

variable {n a b m : ℕ} {Γ : List (Fm PTm n)}

/-- The representation counts sum to the number of pairs. -/
theorem total_sum {R : Type*} [CommRing R] (t : Fin a → Fin b → Fin m → R) (h : ∀ x y, ∑ s, t x y s = 1) :
    ∑ s, ∑ x, ∑ y, t x y s = (a : R) * b := by
  have e : ∀ x, ∑ s, ∑ y, t x y s = (b : R) := fun x => by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun y _ => h x y, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, _root_.mul_one]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun x _ => e x, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- `∑_s r(s) = |A| |B|`. -/
theorem total (T : Fin a → Fin b → Fin m → ZT n)
    (hT : ∀ x y, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun s => T x y s) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun s => ZT.sumFin fun x => ZT.sumFin fun y => T x y s) (ZT.natLit (a * b)) := by
  have hT1 : ∀ x y, ∑ s, ZT.toZ Γ (T x y s) = 1 := fun x y => by
    simpa only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_one] using ZT.toZ_eq (hT x y)
  have e := total_sum (fun x y s => ZT.toZ Γ (T x y s)) hT1
  beta_reduce at e
  apply ZT.derive
  zsimp
  rw [e]
  push_cast
  ring

/-- The energy bound `(|A| |B|)² ≤ |A + B| ∑_s r(s)²`. -/
theorem energy (T : Fin a → Fin b → Fin m → ZT n)
    (hT : ∀ x y, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun s => T x y s) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] zle (ZT.natLit (a * b * (a * b)))
      (ZT.natLit m * ZT.sumFin fun s => ZT.sq (ZT.sumFin fun x => ZT.sumFin fun y => T x y s)) := by
  have hT1 : ∀ x y, ∑ s, ZT.toZ Γ (T x y s) = 1 := fun x y => by
    simpa only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_one] using ZT.toZ_eq (hT x y)
  have e := total_sum (fun x y s => ZT.toZ Γ (T x y s)) hT1
  beta_reduce at e
  have hc := cauchy_int (Γ := Γ) (fun s => ZT.sumFin fun x => ZT.sumFin fun y => T x y s)
  refine zle_of_comb (zsl hc) ?_ (nn_zsl _)
  zsimp
  rw [e]
  push_cast
  ring

end LeanProofs.IPRA.Combinatorics.AdditiveEnergy
