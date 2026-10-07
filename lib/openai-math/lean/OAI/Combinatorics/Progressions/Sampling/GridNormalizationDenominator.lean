import Mathlib.Algebra.Order.Floor.Semiring
import OAI.Combinatorics.Progressions.Lattices.IntegerMinorNormalization
import OAI.Combinatorics.Progressions.Sampling.RationalSpanGrid

namespace OAI

section

namespace Erdos3

theorem exists_integer_scaled_grid_matrix {ι κ : Type*}
    (H : Matrix ι κ ℝ) (l : ℕ) (hgrid : ∀ j, H.col j ∈ realDenominatorGrid l) :
    ∃ Z : Matrix ι κ ℤ, Z.map (Int.castRingHom ℝ) = (l : ℝ) • H := by
  choose z hz using hgrid
  refine ⟨fun i j => z j i, ?_⟩
  ext i j
  exact congrFun (hz j) i

theorem scaled_integer_minor_eq {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (H : Matrix ι (Fin k) ℝ) (t : ℝ)
    (hZ : Z.map (Int.castRingHom ℝ) = t • H) (p : Fin k → ι) :
    ((Z.submatrix p id).det : ℝ) = t ^ k * (H.submatrix p id).det := by
  calc
    _ = ((Z.submatrix p id).map (Int.castRingHom ℝ)).det :=
      (Int.castRingHom ℝ).map_det _
    _ = (t • H.submatrix p id).det := by
      congr 1
      ext i j
      exact congrArg (fun M : Matrix ι (Fin k) ℝ => M (p i) j) hZ
    _ = _ := by rw [Matrix.det_smul, Fintype.card_fin]

theorem scaled_integer_minor_natAbs_bound {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (H : Matrix ι (Fin k) ℝ) (t C : ℝ) (ht : 0 < t)
    (hZ : Z.map (Int.castRingHom ℝ) = t • H)
    (hminor : ∀ p : Fin k → ι, |(H.submatrix p id).det| ≤ C) :
    ∀ p : Fin k → ι, (Z.submatrix p id).det.natAbs ≤ Nat.ceil (C * t ^ k) := by
  intro p
  have h : |((Z.submatrix p id).det : ℝ)| ≤ C * t ^ k := by
    rw [scaled_integer_minor_eq Z H t hZ, abs_mul, abs_of_pos (pow_pos ht _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hminor p) (pow_pos ht k).le
  have hc := h.trans (Nat.le_ceil (C * t ^ k))
  apply (Nat.cast_le (α := ℝ)).mp
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hc

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem exists_bounded_rational_grid_matrix {ι κ : Type*}
    (A : Matrix ι κ ℝ) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, A.col j ∈ realDenominatorGrid l)
    (C : ℝ) (hbound : ∀ i j, |A i j| ≤ C) :
    ∃ Q : Matrix ι κ ℚ, Q.map (Rat.castHom ℝ) = A ∧
      ∀ i j, RationalHeightLE (Q i j) (max l (Nat.ceil ((l : ℝ) * C))) := by
  obtain ⟨Z, hZ⟩ := exists_integer_scaled_grid_matrix A l hgrid
  let Q : Matrix ι κ ℚ := fun i j => (Z i j : ℚ) / l
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  refine ⟨Q, ?_, ?_⟩
  · ext i j
    change (((Z i j : ℚ) / l : ℚ) : ℝ) = A i j
    push_cast
    apply (div_eq_iff hlr.ne').mpr
    have h := congrArg (fun B : Matrix ι κ ℝ => B i j) hZ
    change (Z i j : ℝ) = (l : ℝ) * A i j at h
    simpa only [mul_comm] using h
  · intro i j
    have hz : (Z i j).natAbs ≤ Nat.ceil ((l : ℝ) * C) := by
      have he : (Z i j : ℝ) = (l : ℝ) * A i j :=
        congrArg (fun B : Matrix ι κ ℝ => B i j) hZ
      have hb : |(Z i j : ℝ)| ≤ (l : ℝ) * C := by
        rw [he, abs_mul, abs_of_pos hlr]
        exact mul_le_mul_of_nonneg_left (hbound i j) hlr.le
      have hc := hb.trans (Nat.le_ceil ((l : ℝ) * C))
      apply (Nat.cast_le (α := ℝ)).mp
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hc
    change RationalHeightLE ((Z i j : ℚ) / l) _
    have h := rationalHeightLE_fraction (Z i j) (l : ℤ)
      (by exact_mod_cast hl.ne') (hz.trans (le_max_right _ _))
      (by simpa only [Int.natAbs_natCast] using le_max_left l (Nat.ceil ((l : ℝ) * C)))
    simpa only [Int.cast_natCast] using h

theorem exists_bounded_rational_map_matrix {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : (κ → ℝ) →ₗ[ℝ] (ι → ℝ)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, f (Pi.single j 1) ∈ realDenominatorGrid l)
    (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ∃ Q : Matrix ι κ ℚ,
      (∀ i j, RationalHeightLE (Q i j) (max l (Nat.ceil ((l : ℝ) * C)))) ∧
      ∀ x, f x = Q.map (Rat.castHom ℝ) *ᵥ x := by
  have hcol (j : κ) : (LinearMap.toMatrix' f).col j = f (Pi.single j 1) := by
    funext i
    exact LinearMap.toMatrix'_apply f i j
  obtain ⟨Q, hQ, hheight⟩ := exists_bounded_rational_grid_matrix (LinearMap.toMatrix' f) l hl
    (fun j => by rw [hcol]; exact hgrid j) C (by
      intro i j
      rw [LinearMap.toMatrix'_apply]
      have h := (norm_le_pi_norm (f (Pi.single j 1)) i).trans (hbound (Pi.single j 1))
      simpa only [Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] using h)
  refine ⟨Q, hheight, fun x => ?_⟩
  rw [hQ]
  exact (LinearMap.toMatrix'_mulVec f x).symm

end Erdos3

end

section

namespace Erdos3

theorem scaled_integer_row_normalization_cast {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (H : Matrix ι (Fin k) ℝ) (t : ℝ) (ht : t ≠ 0)
    (hZ : Z.map (Int.castRingHom ℝ) = t • H)
    (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0)
    (hZp : (Z.submatrix p id).det ≠ 0) :
    let W := Z.map (Int.castRingHom ℚ)
    (W * (W.submatrix p id)⁻¹).map (Rat.castHom ℝ) = H * (H.submatrix p id)⁻¹ := by
  dsimp only
  ext i j
  have he := integer_row_normalization_entry Z p hZp i j
  change (((Z.map (Int.castRingHom ℚ) *
    ((Z.map (Int.castRingHom ℚ)).submatrix p id)⁻¹) i j : ℚ) : ℝ) = _
  rw [he]
  simp only [Rat.cast_div, Rat.cast_intCast]
  rw [scaled_integer_minor_eq Z H t hZ, scaled_integer_minor_eq Z H t hZ]
  rw [row_normalization_entry H p hp i j]
  field_simp

theorem exists_bounded_rational_row_normalization {ι : Type*} {k : ℕ}
    (H : Matrix ι (Fin k) ℝ) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, H.col j ∈ realDenominatorGrid l)
    (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0)
    (C : ℝ) (hminor : ∀ q : Fin k → ι, |(H.submatrix q id).det| ≤ C) :
    ∃ Q : Matrix ι (Fin k) ℚ,
      Q.map (Rat.castHom ℝ) = H * (H.submatrix p id)⁻¹ ∧
      (∀ i j, RationalHeightLE (Q i j) (Nat.ceil (C * (l : ℝ) ^ k))) ∧
      Q.submatrix p id = 1 := by
  obtain ⟨Z, hZ⟩ := exists_integer_scaled_grid_matrix H l hgrid
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hZp : (Z.submatrix p id).det ≠ 0 := by
    intro hz
    have hf := scaled_integer_minor_eq Z H (l : ℝ) hZ p
    rw [hz, Int.cast_zero] at hf
    exact (mul_ne_zero (pow_ne_zero _ hlr.ne') hp) hf.symm
  let W := Z.map (Int.castRingHom ℚ)
  let Q := W * (W.submatrix p id)⁻¹
  have hWp : (W.submatrix p id).det ≠ 0 := by
    have he : (W.submatrix p id).det = ((Z.submatrix p id).det : ℚ) := by
      change ((Z.submatrix p id).map (Int.castRingHom ℚ)).det = _
      exact ((Int.castRingHom ℚ).map_det _).symm
    rw [he]
    exact_mod_cast hZp
  refine ⟨Q, ?_, ?_, row_normalization_submatrix W p hWp⟩
  · exact scaled_integer_row_normalization_cast Z H (l : ℝ) hlr.ne' hZ p hp hZp
  · intro i j
    exact integer_row_normalization_height Z p hZp _
      (scaled_integer_minor_natAbs_bound Z H (l : ℝ) C hlr hZ hminor) i j

end Erdos3

end

section

namespace Erdos3

theorem integer_row_normalization_grid {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (p : Fin k → ι) (hp : (Z.submatrix p id).det ≠ 0) :
    let W := Z.map (Int.castRingHom ℚ)
    ∀ j, (W * (W.submatrix p id)⁻¹).col j ∈
      denominatorGrid (Z.submatrix p id).det.natAbs := by
  let d := (Z.submatrix p id).det
  have hd : (d : ℚ) ≠ 0 := by exact_mod_cast hp
  have habs : (d.natAbs : ℚ) = (d.sign : ℚ) * (d : ℚ) := by
    calc
      _ = ((d.natAbs : ℤ) : ℚ) := (Int.cast_natCast _).symm
      _ = ((d.sign * d : ℤ) : ℚ) :=
        congrArg (fun z : ℤ => (z : ℚ)) (Int.sign_mul_self_eq_natAbs d).symm
      _ = _ := Int.cast_mul _ _
  dsimp only
  intro j
  refine ⟨fun i => d.sign * (Z.submatrix (Function.update p j i) id).det, fun i => ?_⟩
  change (d.natAbs : ℚ) *
    ((Z.map (Int.castRingHom ℚ) * ((Z.map (Int.castRingHom ℚ)).submatrix p id)⁻¹) i j) = _
  rw [integer_row_normalization_entry Z p hp i j]
  change (d.natAbs : ℚ) * (_ / (d : ℚ)) = _
  rw [habs, Int.cast_mul]
  field_simp

theorem exists_grid_row_normalization {ι : Type*} {k : ℕ}
    (B : Matrix ι (Fin k) ℝ) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, B.col j ∈ realDenominatorGrid l)
    (p : Fin k → ι) (hp : (B.submatrix p id).det ≠ 0)
    (C : ℝ) (hminor : |(B.submatrix p id).det| ≤ C) :
    ∃ D : ℕ, 0 < D ∧ D ≤ Nat.ceil (C * (l : ℝ) ^ k) ∧
      ∃ Q : Matrix ι (Fin k) ℚ,
        (∀ j, Q.col j ∈ denominatorGrid D) ∧
        Q.map (Rat.castHom ℝ) = B * (B.submatrix p id)⁻¹ ∧
        Q.submatrix p id = 1 := by
  obtain ⟨Z, hZ⟩ := exists_integer_scaled_grid_matrix B l hgrid
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hZp : (Z.submatrix p id).det ≠ 0 := by
    intro hz
    have hf := scaled_integer_minor_eq Z B (l : ℝ) hZ p
    rw [hz, Int.cast_zero] at hf
    exact (mul_ne_zero (pow_ne_zero _ hlr.ne') hp) hf.symm
  have hbound : (Z.submatrix p id).det.natAbs ≤ Nat.ceil (C * (l : ℝ) ^ k) := by
    have h : |((Z.submatrix p id).det : ℝ)| ≤ C * (l : ℝ) ^ k := by
      rw [scaled_integer_minor_eq Z B (l : ℝ) hZ, abs_mul,
        abs_of_pos (pow_pos hlr _)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hminor (pow_pos hlr k).le
    have hc := h.trans (Nat.le_ceil (C * (l : ℝ) ^ k))
    apply (Nat.cast_le (α := ℝ)).mp
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hc
  let W := Z.map (Int.castRingHom ℚ)
  have hWp : (W.submatrix p id).det ≠ 0 := by
    have he : (W.submatrix p id).det = ((Z.submatrix p id).det : ℚ) := by
      change ((Z.submatrix p id).map (Int.castRingHom ℚ)).det = _
      exact ((Int.castRingHom ℚ).map_det _).symm
    rw [he]
    exact_mod_cast hZp
  refine ⟨_, Int.natAbs_pos.mpr hZp, hbound, W * (W.submatrix p id)⁻¹,
    integer_row_normalization_grid Z p hZp, ?_, row_normalization_submatrix W p hWp⟩
  exact scaled_integer_row_normalization_cast Z B (l : ℝ) hlr.ne' hZ p hp hZp

end Erdos3

end

end OAI
