import IPRADerivations.Core.CertificateTactics

/-!
# Radon partitions from an affine dependence

Packet: `geometry/helly-ipra`, `helly.tex`, Lemma `lem:radon` ("Two compatible convex combinations") and the
four-set example of `thm:main`: "Write `z_j^+ = max(z_j, 0)` and `z_j^- = max(−z_j, 0)`. The two sums of parts
equal some `M` … Their supports are disjoint and the weighted sums agree." The parts are terms (through
`monus`), so the two convex combinations are explicit in the dependence:

* `pp z`, `np z`: the positive and negative parts of an integer term;
* `max_symm`, `parts`: `z^+ − z^- = z`; `pp_nonneg`, `np_nonneg`; `parts_disjoint`: `z^+ = 0 ∨ z^- = 0`, an
  object-level disjunction (so for every index `i` one of the two combinations has weight zero at `i`: the
  row of the Helly certificate that avoids the point `p_i`);
* `parts_mass`, `parts_moment`: for a dependence `∑ z_j = 0`, `∑ z_j x_j = 0`, the two parts have equal mass
  and equal weighted sums (one coordinate `x`);
* `line_dependence`: three points on the line, `z = (x_1 − x_2, x_2 − x_0, x_0 − x_1)`;
* `plane_dependence`: four points in the plane, `z_j = ±` the signed area of the other three ("The independent
  minor construction": the cofactors of the matrix with columns `(x_j, y_j, 1)`), with zero mass and zero
  moments in both coordinates;
* `planeZ`, `radon_plane`: Radon's lemma for four points in the plane as one certificate.

When the dependence is nonzero the common mass `M` is positive (`Geometry/HellyCertificates.part_zero`), and
`y = M^{-1} ∑ z_j^+ p_j = M^{-1} ∑ z_j^- p_j` is the Radon point: the four-set Helly point in the plane.
-/

namespace LeanProofs.IPRA.Geometry.RadonPartition

open_ipra

variable {n s : ℕ} {Γ : List (Fm PTm n)}

/-- The positive part `max(z, 0)`. -/
def pp (z : ZT n) : ZT n := ZT.ofNat (monus z.pos z.neg)

/-- The negative part `max(−z, 0)`. -/
def np (z : ZT n) : ZT n := ZT.ofNat (monus z.neg z.pos)

/-- `(p ∸ q) + q = (q ∸ p) + p`: both sides are the maximum. -/
theorem max_symm (p q : PTm n) : Γ ⊢[PRAAx] monus p q + q ≐ monus q p + p := by
  refine .orE (le_total p q) ?_ ?_
  · have h : (le p q :: Γ) ⊢[PRAAx] le p q := Prf.hyp0
    have h0 : (le p q :: Γ) ⊢[PRAAx] monus p q ≐ zero := Prf.hyp0
    have e₀ := natEq h0
    have e₁ := natEq (eq_add_of_le h)
    apply deriveNat
    ipra_simps
    linear_combination e₀ + e₁
  · have h : (le q p :: Γ) ⊢[PRAAx] le q p := Prf.hyp0
    have h0 : (le q p :: Γ) ⊢[PRAAx] monus q p ≐ zero := Prf.hyp0
    have e₀ := natEq h0
    have e₁ := natEq (eq_add_of_le h)
    apply deriveNat
    ipra_simps
    linear_combination -e₀ - e₁

theorem toZ_parts (z : ZT n) : ZT.toZ Γ (pp z) - ZT.toZ Γ (np z) = ZT.toZ Γ z := by
  have e := natEq (max_symm (Γ := Γ) z.pos z.neg)
  simp only [pp, np, ZT.toZ_ofNat]
  rw [toZ_def z]
  ipra_simps
  linear_combination e

/-- `z^+ − z^- = z`. -/
theorem parts (z : ZT n) : Γ ⊢[PRAAx] ZT.eq (pp z - np z) z := by
  apply ZT.derive
  rw [ZT.toZ_sub]
  exact toZ_parts z

theorem pp_nonneg (z : ZT n) : Γ ⊢[PRAAx] zle (ZT.natLit 0) (pp z) := by
  refine zle_of_comb (Groth.ι (Q.mk Γ (monus z.pos z.neg))) ?_ (nn_term _)
  simp only [pp, ZT.toZ_ofNat, ZT.toZ_natLit, Nat.cast_zero, sub_zero]

theorem np_nonneg (z : ZT n) : Γ ⊢[PRAAx] zle (ZT.natLit 0) (np z) := by
  refine zle_of_comb (Groth.ι (Q.mk Γ (monus z.neg z.pos))) ?_ (nn_term _)
  simp only [np, ZT.toZ_ofNat, ZT.toZ_natLit, Nat.cast_zero, sub_zero]

/-- The supports are disjoint: one of the two parts vanishes. -/
theorem parts_disjoint (z : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (pp z) (ZT.natLit 0) ⋎ ZT.eq (np z) (ZT.natLit 0) := by
  refine .orE (le_total z.pos z.neg) (.orI₁ ?_) (.orI₂ ?_)
  · have h0 : (le z.pos z.neg :: Γ) ⊢[PRAAx] monus z.pos z.neg ≐ zero := Prf.hyp0
    have e := natEq h0
    apply ZT.derive
    simp only [pp, ZT.toZ_ofNat, ZT.toZ_natLit, Nat.cast_zero]
    ipra_simps
    exact e
  · have h0 : (le z.neg z.pos :: Γ) ⊢[PRAAx] monus z.neg z.pos ≐ zero := Prf.hyp0
    have e := natEq h0
    apply ZT.derive
    simp only [np, ZT.toZ_ofNat, ZT.toZ_natLit, Nat.cast_zero]
    ipra_simps
    exact e

/-- The two parts of a dependence have the same mass. -/
theorem parts_mass (Z : Fin s → ZT n) (hZ : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin Z) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => pp (Z j)) (ZT.sumFin fun j => np (Z j)) := by
  have e := ZT.toZ_eq hZ
  simp only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_zero] at e
  apply ZT.derive
  simp only [ZT.toZ_sumFin]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun j _ => toZ_parts (Γ := Γ) (Z j), e]

/-- The two parts of a dependence have the same weighted sum (one coordinate `x`). -/
theorem parts_moment (Z x : Fin s → ZT n)
    (hZ : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => Z j * x j) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => pp (Z j) * x j) (ZT.sumFin fun j => np (Z j) * x j) := by
  have e := ZT.toZ_eq hZ
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero] at e
  have hp : ∀ j, ZT.toZ Γ (pp (Z j)) * ZT.toZ Γ (x j) - ZT.toZ Γ (np (Z j)) * ZT.toZ Γ (x j) =
      ZT.toZ Γ (Z j) * ZT.toZ Γ (x j) := fun j => by rw [← sub_mul, toZ_parts]
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_mul]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun j _ => hp j, e]

/-- Three points on the line: the dependence `(x₁ − x₂, x₂ − x₀, x₀ − x₁)`. -/
theorem line_dependence (x₀ x₁ x₂ : ZT n) :
    (Γ ⊢[PRAAx] ZT.eq ((x₁ - x₂) + (x₂ - x₀) + (x₀ - x₁)) (ZT.natLit 0)) ∧
      (Γ ⊢[PRAAx] ZT.eq ((x₁ - x₂) * x₀ + (x₂ - x₀) * x₁ + (x₀ - x₁) * x₂) (ZT.natLit 0)) := by
  refine ⟨?_, ?_⟩
  · ipra_lc
  · ipra_lc

/-- Twice the signed area of the triangle `a b c`. -/
def area (xa ya xb yb xc yc : ZT n) : ZT n := (xb - xa) * (yc - ya) - (xc - xa) * (yb - ya)

@[simp] theorem toZ_area (xa ya xb yb xc yc : ZT n) :
    ZT.toZ Γ (area xa ya xb yb xc yc) =
      (ZT.toZ Γ xb - ZT.toZ Γ xa) * (ZT.toZ Γ yc - ZT.toZ Γ ya) -
        (ZT.toZ Γ xc - ZT.toZ Γ xa) * (ZT.toZ Γ yb - ZT.toZ Γ ya) := by
  simp only [area, ZT.toZ_sub, ZT.toZ_mul]

/-- Four points in the plane: the signed areas of the complementary triangles are an affine dependence. -/
theorem plane_dependence (x₀ y₀ x₁ y₁ x₂ y₂ x₃ y₃ : ZT n) :
    (Γ ⊢[PRAAx] ZT.eq (area x₁ y₁ x₂ y₂ x₃ y₃ - area x₀ y₀ x₂ y₂ x₃ y₃ + area x₀ y₀ x₁ y₁ x₃ y₃ -
        area x₀ y₀ x₁ y₁ x₂ y₂) (ZT.natLit 0)) ∧
      (Γ ⊢[PRAAx] ZT.eq (area x₁ y₁ x₂ y₂ x₃ y₃ * x₀ - area x₀ y₀ x₂ y₂ x₃ y₃ * x₁ +
        area x₀ y₀ x₁ y₁ x₃ y₃ * x₂ - area x₀ y₀ x₁ y₁ x₂ y₂ * x₃) (ZT.natLit 0)) ∧
      (Γ ⊢[PRAAx] ZT.eq (area x₁ y₁ x₂ y₂ x₃ y₃ * y₀ - area x₀ y₀ x₂ y₂ x₃ y₃ * y₁ +
        area x₀ y₀ x₁ y₁ x₃ y₃ * y₂ - area x₀ y₀ x₁ y₁ x₂ y₂ * y₃) (ZT.natLit 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · ipra_lc [toZ_area]
  · ipra_lc [toZ_area]
  · ipra_lc [toZ_area]

/-- The dependence of four points `(x j, y j)` in the plane. -/
def planeZ (x y : Fin 4 → ZT n) : Fin 4 → ZT n :=
  ![area (x 1) (y 1) (x 2) (y 2) (x 3) (y 3), -area (x 0) (y 0) (x 2) (y 2) (x 3) (y 3),
    area (x 0) (y 0) (x 1) (y 1) (x 3) (y 3), -area (x 0) (y 0) (x 1) (y 1) (x 2) (y 2)]

theorem planeZ_mass (x y : Fin 4 → ZT n) : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin (planeZ x y)) (ZT.natLit 0) := by
  apply ZT.derive
  rw [ZT.toZ_sumFin, Fin.sum_univ_four, ZT.toZ_natLit, Nat.cast_zero]
  show ZT.toZ Γ (area (x 1) (y 1) (x 2) (y 2) (x 3) (y 3)) + ZT.toZ Γ (-area (x 0) (y 0) (x 2) (y 2) (x 3) (y 3)) +
    ZT.toZ Γ (area (x 0) (y 0) (x 1) (y 1) (x 3) (y 3)) + ZT.toZ Γ (-area (x 0) (y 0) (x 1) (y 1) (x 2) (y 2)) = 0
  simp only [ZT.toZ_neg, toZ_area]
  ring

theorem planeZ_moment_x (x y : Fin 4 → ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => planeZ x y j * x j) (ZT.natLit 0) := by
  apply ZT.derive
  rw [ZT.toZ_sumFin, Fin.sum_univ_four, ZT.toZ_natLit, Nat.cast_zero]
  show ZT.toZ Γ (area (x 1) (y 1) (x 2) (y 2) (x 3) (y 3) * x 0) +
    ZT.toZ Γ (-area (x 0) (y 0) (x 2) (y 2) (x 3) (y 3) * x 1) +
    ZT.toZ Γ (area (x 0) (y 0) (x 1) (y 1) (x 3) (y 3) * x 2) +
    ZT.toZ Γ (-area (x 0) (y 0) (x 1) (y 1) (x 2) (y 2) * x 3) = 0
  simp only [ZT.toZ_mul, ZT.toZ_neg, toZ_area]
  ring

theorem planeZ_moment_y (x y : Fin 4 → ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => planeZ x y j * y j) (ZT.natLit 0) := by
  apply ZT.derive
  rw [ZT.toZ_sumFin, Fin.sum_univ_four, ZT.toZ_natLit, Nat.cast_zero]
  show ZT.toZ Γ (area (x 1) (y 1) (x 2) (y 2) (x 3) (y 3) * y 0) +
    ZT.toZ Γ (-area (x 0) (y 0) (x 2) (y 2) (x 3) (y 3) * y 1) +
    ZT.toZ Γ (area (x 0) (y 0) (x 1) (y 1) (x 3) (y 3) * y 2) +
    ZT.toZ Γ (-area (x 0) (y 0) (x 1) (y 1) (x 2) (y 2) * y 3) = 0
  simp only [ZT.toZ_mul, ZT.toZ_neg, toZ_area]
  ring

/-- Radon's lemma for four points in the plane, as an explicit certificate: the positive and negative parts
of the area dependence have the same mass and the same weighted sums in both coordinates, and for every
point one of the two combinations has weight zero there. -/
theorem radon_plane (x y : Fin 4 → ZT n) :
    (Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => pp (planeZ x y j)) (ZT.sumFin fun j => np (planeZ x y j))) ∧
      (Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => pp (planeZ x y j) * x j)
        (ZT.sumFin fun j => np (planeZ x y j) * x j)) ∧
      (Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => pp (planeZ x y j) * y j)
        (ZT.sumFin fun j => np (planeZ x y j) * y j)) ∧
      ∀ i, Γ ⊢[PRAAx] ZT.eq (pp (planeZ x y i)) (ZT.natLit 0) ⋎ ZT.eq (np (planeZ x y i)) (ZT.natLit 0) :=
  ⟨parts_mass _ (planeZ_mass x y), parts_moment _ x (planeZ_moment_x x y),
    parts_moment _ y (planeZ_moment_y x y), fun i => parts_disjoint _⟩

end LeanProofs.IPRA.Geometry.RadonPartition
