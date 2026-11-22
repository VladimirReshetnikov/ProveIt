import IPRADerivations.Core.IntCertificates

/-!
# Finite rational Helly: the certificate identities

Packet: `geometry/helly-ipra`, `helly.tex`, Theorem `thm:main` ("Finite rational Helly with certificates") and
Lemma `lem:radon`, the finite identities of the elimination, the gluing and the compression, as iPRA
derivations about integer terms (`ZT`; rational weights and points cleared of denominators, one coordinate at
a time):

* `elim_pivot`, `elim_keep`, `elim_dual` (Radon's lemma without a rank assumption): for the new column
  `V'_j = a V_j − b_j v` with `a = r·v`, `b_j = r·V_j`, "The new columns annihilate `r` since
  `a b_j − b_j a = 0`, and they still annihilate every previous row", and `L'_i V'_j = δ_{ij}` cleared by `a`;
* `radon_mass`, `radon_moment`: for `z = z⁺ − z⁻` with `∑ z_j = 0` and `∑ z_j x_j = 0`, "The two sums of parts
  equal some `M`" and the weighted sums agree;
* `part_zero`: "If `M = 0`, all parts are zero by nonnegativity";
* `glue_mass`, `glue_bary` (gluing the local witnesses): for `w^S_{iT} = ∑_j a_j w^{S∖{j}}_{iT}`,
  "Interchange two finite sums to obtain `∑_T w^S_{iT} = ∑_j a_j = 1` and
  `∑_T w^S_{iT} p_T = ∑_j a_j x_j = y_S`";
* `compress_mass`, `compress_moment`, `compress_nonneg` (compressing the proof of membership): for
  `w'_T = w_T − θ z_T`, cleared by the pivot `z_0 > 0` (`θ = w_0/z_0`): "The zero mass and moment of `z`
  preserve the row's sum and barycentre", and the entries with `z_T ≤ 0` stay nonnegative;
* `fm_combine`, `fm_lift` (Theorem `thm:poly`, eliminating the last coordinate): the projected row obtained
  from a lower and an upper row, and the lift of a point of the projection by its lower bound;
* `centerpoint_count` (Corollary `cor:cent`): at most `d + 1` heavy subsets share a sample index.
-/

namespace LeanProofs.IPRA.Geometry.HellyCertificates

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n s t : ℕ} {Γ : List (Fm PTm n)}

/-! ## Identities in a commutative ring -/

section Ring

variable {A : Type*} [CommRing A]

theorem lin (r V v : Fin s → A) (a b : A) :
    ∑ i, r i * (a * V i - b * v i) = a * ∑ i, r i * V i - b * ∑ i, r i * v i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem lin_sum (w z : Fin s → A) (a b : A) : ∑ i, (a * w i - b * z i) = a * ∑ i, w i - b * ∑ i, z i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem lin_moment (w z p : Fin s → A) (a b : A) :
    ∑ i, (a * w i - b * z i) * p i = a * ∑ i, w i * p i - b * ∑ i, z i * p i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end Ring

/-! ## The elimination step of Radon's lemma -/

/-- The new column annihilates the pivot row: `r · ((r·v) V − (r·V) v) = 0`. -/
theorem elim_pivot (r V v : Fin s → ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.sumFin fun i => r i * ((ZT.sumFin fun k => r k * v k) * V i - (ZT.sumFin fun k => r k * V k) * v i))
      (ZT.natLit 0) := by
  have e := lin (fun i => ZT.toZ Γ (r i)) (fun i => ZT.toZ Γ (V i)) (fun i => ZT.toZ Γ (v i))
    (∑ k, ZT.toZ Γ (r k) * ZT.toZ Γ (v k)) (∑ k, ZT.toZ Γ (r k) * ZT.toZ Γ (V k))
  beta_reduce at e
  apply ZT.derive
  zsimp
  rw [e]
  ring

/-- The new column still annihilates every previous row. -/
theorem elim_keep (r V v : Fin s → ZT n) (a b : ZT n)
    (hV : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => r i * V i) (ZT.natLit 0))
    (hv : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => r i * v i) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => r i * (a * V i - b * v i)) (ZT.natLit 0) := by
  have e := lin (fun i => ZT.toZ Γ (r i)) (fun i => ZT.toZ Γ (V i)) (fun i => ZT.toZ Γ (v i)) (ZT.toZ Γ a)
    (ZT.toZ Γ b)
  beta_reduce at e
  have e₁ := ZT.toZ_eq hV
  have e₂ := ZT.toZ_eq hv
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero] at e₁ e₂
  apply ZT.derive
  zsimp
  rw [e, e₁, e₂]
  ring

/-- The dual rows: `L · V = δ` and `L · v = 0` (a dual row other than the pivot's) give
`L · (a V − b v) = a δ`, so `L/a` is dual to the new column. -/
theorem elim_dual (L V v : Fin s → ZT n) (a b δ : ZT n)
    (hV : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => L i * V i) δ)
    (hv : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => L i * v i) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => L i * (a * V i - b * v i)) (a * δ) := by
  have e := lin (fun i => ZT.toZ Γ (L i)) (fun i => ZT.toZ Γ (V i)) (fun i => ZT.toZ Γ (v i)) (ZT.toZ Γ a)
    (ZT.toZ Γ b)
  beta_reduce at e
  have e₁ := ZT.toZ_eq hV
  have e₂ := ZT.toZ_eq hv
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero] at e₁ e₂
  apply ZT.derive
  zsimp
  rw [e, e₁, e₂]
  ring

/-! ## The two convex combinations -/

/-- The positive and negative parts of an affine dependence have the same mass. -/
theorem radon_mass (zp zn : Fin s → ZT n)
    (hz : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => zp j - zn j) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin zp) (ZT.sumFin zn) := by
  have e := ZT.toZ_eq hz
  simp only [ZT.toZ_sumFin, ZT.toZ_sub, ZT.toZ_natLit, Nat.cast_zero, Finset.sum_sub_distrib] at e
  apply ZT.derive
  simp only [ZT.toZ_sumFin]
  linear_combination e

/-- The weighted sums of the two parts agree (one coordinate `x`). -/
theorem radon_moment (zp zn x : Fin s → ZT n)
    (hz : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => (zp j - zn j) * x j) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => zp j * x j) (ZT.sumFin fun j => zn j * x j) := by
  have e := ZT.toZ_eq hz
  simp only [ZT.toZ_sumFin, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero, sub_mul,
    Finset.sum_sub_distrib] at e
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_mul]
  linear_combination e

/-- "If `M = 0`, all parts are zero by nonnegativity." -/
theorem part_zero (zp : Fin s → ZT n) (h0 : ∀ j, Γ ⊢[PRAAx] zle (ZT.natLit 0) (zp j))
    (hM : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin zp) (ZT.natLit 0)) (j : Fin s) :
    Γ ⊢[PRAAx] zle (zp j) (ZT.natLit 0) := by
  have e := ZT.toZ_eq hM
  simp only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_zero] at e
  have e' : ∑ i ∈ Finset.univ.erase j, ZT.toZ Γ (zp i) = ∑ i, ZT.toZ Γ (zp i) - ZT.toZ Γ (zp j) :=
    Finset.sum_erase_eq_sub (Finset.mem_univ j)
  refine zle_of_comb (∑ i ∈ Finset.univ.erase j, zsl (h0 i)) ?_ (nn_sum _ _ fun i _ => nn_zsl _)
  simp only [zsl_def, ZT.toZ_natLit, Nat.cast_zero, sub_zero]
  linear_combination -e - e'

/-! ## Gluing the local witnesses -/

/-- `∑_T ∑_j a_j w_{jT} = (∑_j a_j) m` when every child row has mass `m`. -/
theorem glue_mass (a : Fin s → ZT n) (w : Fin s → Fin t → ZT n) (m M : ZT n)
    (hw : ∀ j, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin (w j)) m) (ha : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin a) M) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun T => ZT.sumFin fun j => a j * w j T) (M * m) := by
  have hw' : ∀ j, ∑ T, ZT.toZ Γ (w j T) = ZT.toZ Γ m := fun j => by
    have h := ZT.toZ_eq (hw j)
    simpa only [ZT.toZ_sumFin] using h
  have ha' := ZT.toZ_eq ha
  simp only [ZT.toZ_sumFin] at ha'
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hw']
  rw [← Finset.sum_mul, ha']

/-- `∑_T (∑_j a_j w_{jT}) p_T = m ∑_j a_j x_j` when child row `j` has barycentre `x_j` (cleared by its
mass `m`): the glued row has barycentre `y_S = ∑ a_j x_j`. -/
theorem glue_bary (a x : Fin s → ZT n) (w : Fin s → Fin t → ZT n) (p : Fin t → ZT n) (m : ZT n)
    (hb : ∀ j, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun T => w j T * p T) (m * x j)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun T => (ZT.sumFin fun j => a j * w j T) * p T)
      (m * ZT.sumFin fun j => a j * x j) := by
  have hb' : ∀ j, ∑ T, ZT.toZ Γ (w j T) * ZT.toZ Γ (p T) = ZT.toZ Γ m * ZT.toZ Γ (x j) := fun j => by
    have h := ZT.toZ_eq (hb j)
    simpa only [ZT.toZ_sumFin, ZT.toZ_mul] using h
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ∑ T, ZT.toZ Γ (a j) * ZT.toZ Γ (w j T) * ZT.toZ Γ (p T) =
      ZT.toZ Γ (a j) * ∑ T, ZT.toZ Γ (w j T) * ZT.toZ Γ (p T) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => _root_.mul_assoc _ _ _
  rw [e, hb' j]
  ring

/-! ## Compressing a row -/

/-- The compressed row `z_0 w − w_0 z` has mass `z_0 m`: the dependence `z` has zero mass. -/
theorem compress_mass (w z : Fin t → ZT n) (z0 w0 m : ZT n) (hw : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin w) m)
    (hz : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin z) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun T => z0 * w T - w0 * z T) (z0 * m) := by
  have e := lin_sum (fun T => ZT.toZ Γ (w T)) (fun T => ZT.toZ Γ (z T)) (ZT.toZ Γ z0) (ZT.toZ Γ w0)
  beta_reduce at e
  have e₁ := ZT.toZ_eq hw
  have e₂ := ZT.toZ_eq hz
  simp only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_zero] at e₁ e₂
  apply ZT.derive
  zsimp
  rw [e, e₁, e₂]
  ring

/-- The compressed row has the same barycentre: the dependence `z` has zero moment (one coordinate `p`). -/
theorem compress_moment (w z p : Fin t → ZT n) (z0 w0 Y : ZT n)
    (hw : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun T => w T * p T) Y)
    (hz : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun T => z T * p T) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun T => (z0 * w T - w0 * z T) * p T) (z0 * Y) := by
  have e := lin_moment (fun T => ZT.toZ Γ (w T)) (fun T => ZT.toZ Γ (z T)) (fun T => ZT.toZ Γ (p T))
    (ZT.toZ Γ z0) (ZT.toZ Γ w0)
  beta_reduce at e
  have e₁ := ZT.toZ_eq hw
  have e₂ := ZT.toZ_eq hz
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero] at e₁ e₂
  apply ZT.derive
  zsimp
  rw [e, e₁, e₂]
  ring

/-- An entry with `z_T ≤ 0` stays nonnegative: `0 ≤ z_0 w_T − w_0 z_T`. -/
theorem compress_nonneg {z0 w0 wT zT : ZT n} (hz0 : Γ ⊢[PRAAx] zle (ZT.natLit 0) z0)
    (hw0 : Γ ⊢[PRAAx] zle (ZT.natLit 0) w0) (hw : Γ ⊢[PRAAx] zle (ZT.natLit 0) wT)
    (hz : Γ ⊢[PRAAx] zle zT (ZT.natLit 0)) : Γ ⊢[PRAAx] zle (ZT.natLit 0) (z0 * wT - w0 * zT) := by
  ipra_zle zsl hz0 * zsl hw + zsl hw0 * zsl hz

/-! ## Eliminating one coordinate of a polyhedron -/

/-- The projected row of `thm:poly`: a lower row `a_L + p_L t ≤ b_L` (`p_L ≤ 0`) and an upper row
`a_U + p_U t ≤ b_U` (`p_U ≥ 0`), "multiply the lower row by `p_upper > 0` and the upper row by
`−p_lower > 0`, then add": `p_U a_L − p_L a_U ≤ p_U b_L − p_L b_U`, free of `t`. -/
theorem fm_combine {aL pL bL aU pU bU τ : ZT n} (hL : Γ ⊢[PRAAx] zle (aL + pL * τ) bL)
    (hU : Γ ⊢[PRAAx] zle (aU + pU * τ) bU) (hpL : Γ ⊢[PRAAx] zle pL (ZT.natLit 0))
    (hpU : Γ ⊢[PRAAx] zle (ZT.natLit 0) pU) :
    Γ ⊢[PRAAx] zle (pU * aL - pL * aU) (pU * bL - pL * bU) := by
  ipra_zle zsl hpU * zsl hL + zsl hpL * zsl hU

/-- The lift: at a point of the projection, the value `τ` of the lower bound (`p_L τ = b_L − a_L`) satisfies
the upper row, cleared by `−p_L > 0`. -/
theorem fm_lift {aL pL bL aU pU bU τ : ZT n}
    (hproj : Γ ⊢[PRAAx] zle (pU * aL - pL * aU) (pU * bL - pL * bU))
    (hτ : Γ ⊢[PRAAx] ZT.eq (pL * τ) (bL - aL)) :
    Γ ⊢[PRAAx] zle (-pL * (aU + pU * τ)) (-pL * bU) := by
  have e := ZT.toZ_eq hτ
  simp only [ZT.toZ_mul, ZT.toZ_sub] at e
  refine zle_of_comb (zsl hproj) ?_ (nn_zsl _)
  zsimp
  linear_combination ZT.toZ Γ pU * e

/-! ## The centerpoint count -/

/-- `cor:cent`: "Any `k ≤ d+1` such subsets share a sample index: the sum of their complement sizes is strictly
less than `kN/(d+1) ≤ N`". Here `d + 1 = k + e`, the complements `c_i` of heavy subsets satisfy
`(d+1) c_i < N`, and the conclusion is `∑ c_i < N` cleared by `d + 1`. -/
theorem centerpoint_count (k e : ℕ) (c : Fin k → ZT n) (N : ZT n) (hN : Γ ⊢[PRAAx] zle (ZT.natLit 1) N)
    (h : ∀ i, Γ ⊢[PRAAx] zle (ZT.natLit (k + e) * c i + ZT.natLit 1) N) :
    Γ ⊢[PRAAx] zle (ZT.natLit (k + e) * (ZT.sumFin c + ZT.natLit 1)) (ZT.natLit (k + e) * N) := by
  refine zle_of_comb (∑ i, zsl (h i) + (e : Groth (Q Γ)) * zsl hN) ?_
    (nn_add (nn_sum _ _ fun i _ => nn_zsl _) (nn_mul (nn_natCast e) (nn_zsl _)))
  zsimp
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, ← Finset.mul_sum,
    Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  push_cast
  ring

end LeanProofs.IPRA.Geometry.HellyCertificates
