import GowersSzemeredi.Sections06_07

/-!
# Generalized progressions from coefficient boxes

Auxiliary constructions for the proofs of Theorems 7.1 and 7.2 in
`Proofs07FreimanClosure`:

* `GeneralizedAP.mem_carrier_iff` describes the carrier by natural-number
  coefficient vectors;
* `GeneralizedAP.sum` concatenates two progressions, adding their carriers
  and multiplying their formal sizes;
* `boxGAP` turns the image `base + Φ(box)` of a symmetric coefficient box under
  an additive map `Φ : (Fin r → ℤ) →+ G` into a progression of formal size
  `∏ (2 R_i + 1)`;
* `posBoxGAP` does the same over `ℤ` with every common difference positive;
* `finsetGAP` covers a nonempty finite set of integers by a progression with
  positive steps, one coordinate of length two per element.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

namespace GeneralizedAP

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

theorem mem_carrier_iff (P : GeneralizedAP G) (y : G) :
    y ∈ P.carrier ↔ ∃ c : Fin P.dimension → ℕ,
      (∀ i, c i < P.length i) ∧ P.base + ∑ i, c i • P.step i = y := by
  classical
  unfold GeneralizedAP.carrier
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨fun i => a i, fun i => (a i).isLt, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun i => ⟨c i, hc i⟩, rfl⟩

/-- Concatenation of two generalized progressions. -/
def sum (P Q : GeneralizedAP G) : GeneralizedAP G where
  dimension := P.dimension + Q.dimension
  base := P.base + Q.base
  step := Fin.append P.step Q.step
  length := Fin.append P.length Q.length

theorem sum_size (P Q : GeneralizedAP G) : (P.sum Q).size = P.size * Q.size := by
  show ∏ i : Fin (P.dimension + Q.dimension), Fin.append P.length Q.length i =
    (∏ i, P.length i) * ∏ i, Q.length i
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem sum_dimension (P Q : GeneralizedAP G) :
    (P.sum Q).dimension = P.dimension + Q.dimension := rfl

theorem add_mem_sum {P Q : GeneralizedAP G} {y z : G}
    (hy : y ∈ P.carrier) (hz : z ∈ Q.carrier) : y + z ∈ (P.sum Q).carrier := by
  obtain ⟨c, hc, rfl⟩ := (mem_carrier_iff P y).mp hy
  obtain ⟨d, hd, rfl⟩ := (mem_carrier_iff Q z).mp hz
  refine (mem_carrier_iff _ _).mpr ⟨Fin.append c d, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa [GeneralizedAP.sum] using hc i
    · simpa [GeneralizedAP.sum] using hd j
  · show P.base + Q.base + ∑ i : Fin (P.dimension + Q.dimension),
        Fin.append c d i • Fin.append P.step Q.step i =
      P.base + ∑ i, c i • P.step i + (Q.base + ∑ i, d i • Q.step i)
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    abel

theorem sum_step_pos {P Q : GeneralizedAP ℤ} (hP : ∀ i, 0 < P.step i ∧ 0 < P.length i)
    (hQ : ∀ i, 0 < Q.step i ∧ 0 < Q.length i) (i : Fin (P.sum Q).dimension) :
    0 < (P.sum Q).step i ∧ 0 < (P.sum Q).length i := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simpa [GeneralizedAP.sum] using hP i
  · simpa [GeneralizedAP.sum] using hQ j

theorem sum_length_pos {P Q : GeneralizedAP G} (hP : ∀ i, 0 < P.length i)
    (hQ : ∀ i, 0 < Q.length i) (i : Fin (P.sum Q).dimension) :
    0 < (P.sum Q).length i := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simpa [GeneralizedAP.sum] using hP i
  · simpa [GeneralizedAP.sum] using hQ j

end GeneralizedAP

section Box

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- An additive map on integer vectors is the sum of its values on unit vectors. -/
theorem addMonoidHom_pi_eq_sum {r : ℕ} (Φ : (Fin r → ℤ) →+ G) (x : Fin r → ℤ) :
    Φ x = ∑ i, x i • Φ (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_zsmul]
  congr 1
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_apply, h]

/-- The progression `base + Φ({x : |x_i| ≤ R_i})`. -/
def boxGAP {r : ℕ} (Φ : (Fin r → ℤ) →+ G) (R : Fin r → ℕ) (base : G) : GeneralizedAP G where
  dimension := r
  base := base - ∑ i, R i • Φ (Pi.single i 1)
  step := fun i => Φ (Pi.single i 1)
  length := fun i => 2 * R i + 1

theorem boxGAP_size {r : ℕ} (Φ : (Fin r → ℤ) →+ G) (R : Fin r → ℕ) (base : G) :
    (boxGAP Φ R base).size = ∏ i, (2 * R i + 1) := rfl

theorem boxGAP_length_pos {r : ℕ} (Φ : (Fin r → ℤ) →+ G) (R : Fin r → ℕ) (base : G)
    (i : Fin (boxGAP Φ R base).dimension) : 0 < (boxGAP Φ R base).length i :=
  Nat.succ_pos _

theorem mem_boxGAP {r : ℕ} (Φ : (Fin r → ℤ) →+ G) (R : Fin r → ℕ) (base : G)
    (x : Fin r → ℤ) (hx : ∀ i, |x i| ≤ (R i : ℤ)) :
    base + Φ x ∈ (boxGAP Φ R base).carrier := by
  refine (GeneralizedAP.mem_carrier_iff _ _).mpr ⟨fun i => (x i + R i).toNat, fun i => ?_, ?_⟩
  · have h := abs_le.mp (hx i)
    change (x i + R i).toNat < 2 * R i + 1
    omega
  · change base - ∑ i, R i • Φ (Pi.single i 1) +
        ∑ i, (x i + R i).toNat • Φ (Pi.single i 1) = base + Φ x
    rw [addMonoidHom_pi_eq_sum Φ x, sub_add_eq_add_sub, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := abs_le.mp (hx i)
    have hc : (((x i + R i).toNat : ℕ) : ℤ) = x i + R i := Int.toNat_of_nonneg (by omega)
    rw [← natCast_zsmul, ← natCast_zsmul, hc, add_smul, add_sub_cancel_right]

end Box

section PosBox

/-- The positive common difference used for the `i`-th axis of `posBoxGAP`. -/
def posStep (g : ℤ) : ℤ := if g = 0 then 1 else |g|

theorem posStep_pos (g : ℤ) : 0 < posStep g := by
  unfold posStep
  split_ifs with h
  · exact one_pos
  · exact abs_pos.mpr h

/-- The coefficient of `posBoxGAP` representing the coordinate value `z`. -/
def posCoeff (g z : ℤ) (R : ℕ) : ℕ :=
  if 0 < g then (z + R).toNat else if g < 0 then (R - z).toNat else R

theorem posCoeff_lt {g z : ℤ} {R : ℕ} (hz : |z| ≤ (R : ℤ)) : posCoeff g z R < 2 * R + 1 := by
  have h := abs_le.mp hz
  unfold posCoeff
  split_ifs <;> omega

theorem posCoeff_spec {g z : ℤ} {R : ℕ} (hz : |z| ≤ (R : ℤ)) :
    ((posCoeff g z R : ℤ) - R) * posStep g = z * g := by
  have h := abs_le.mp hz
  unfold posCoeff posStep
  rcases lt_trichotomy g 0 with hg | hg | hg
  · have h1 : ¬ 0 < g := by omega
    have h2 : g ≠ 0 := by omega
    rw [if_neg h1, if_pos hg, if_neg h2, abs_of_neg hg,
      Int.toNat_of_nonneg (by omega)]
    ring
  · subst hg
    simp
  · have h2 : g ≠ 0 := by omega
    rw [if_pos hg, if_neg h2, abs_of_pos hg, Int.toNat_of_nonneg (by omega)]
    ring

/-- The progression `base + Φ({x : |x_i| ≤ R_i})` over `ℤ`, with positive
common differences: an axis with a negative value of `Φ` is reflected, and an
axis on which `Φ` vanishes gets the step `1`. -/
def posBoxGAP {r : ℕ} (Φ : (Fin r → ℤ) →+ ℤ) (R : Fin r → ℕ) (base : ℤ) :
    GeneralizedAP ℤ where
  dimension := r
  base := base - ∑ i, (R i : ℤ) * posStep (Φ (Pi.single i 1))
  step := fun i => posStep (Φ (Pi.single i 1))
  length := fun i => 2 * R i + 1

theorem posBoxGAP_size {r : ℕ} (Φ : (Fin r → ℤ) →+ ℤ) (R : Fin r → ℕ) (base : ℤ) :
    (posBoxGAP Φ R base).size = ∏ i, (2 * R i + 1) := rfl

theorem posBoxGAP_pos {r : ℕ} (Φ : (Fin r → ℤ) →+ ℤ) (R : Fin r → ℕ) (base : ℤ)
    (i : Fin (posBoxGAP Φ R base).dimension) :
    0 < (posBoxGAP Φ R base).step i ∧ 0 < (posBoxGAP Φ R base).length i :=
  ⟨posStep_pos _, Nat.succ_pos _⟩

theorem mem_posBoxGAP {r : ℕ} (Φ : (Fin r → ℤ) →+ ℤ) (R : Fin r → ℕ) (base : ℤ)
    (x : Fin r → ℤ) (hx : ∀ i, |x i| ≤ (R i : ℤ)) :
    base + Φ x ∈ (posBoxGAP Φ R base).carrier := by
  refine (GeneralizedAP.mem_carrier_iff _ _).mpr
    ⟨fun i => posCoeff (Φ (Pi.single i 1)) (x i) (R i), fun i => posCoeff_lt (hx i), ?_⟩
  change base - ∑ i, (R i : ℤ) * posStep (Φ (Pi.single i 1)) +
      ∑ i, posCoeff (Φ (Pi.single i 1)) (x i) (R i) • posStep (Φ (Pi.single i 1)) =
    base + Φ x
  rw [addMonoidHom_pi_eq_sum Φ x, sub_add_eq_add_sub, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nsmul_eq_mul, smul_eq_mul, ← sub_mul, posCoeff_spec (hx i)]

end PosBox

section FinsetGAP

/-- A progression with positive steps containing a nonempty finite set `X` of
integers: one axis of length two per element. -/
def finsetGAP (X : Finset ℤ) (hX : X.Nonempty) : GeneralizedAP ℤ where
  dimension := X.card
  base := X.min' hX - 1
  step := fun j => (X.equivFin.symm j : ℤ) - X.min' hX + 1
  length := fun _ => 2

theorem finsetGAP_size (X : Finset ℤ) (hX : X.Nonempty) :
    (finsetGAP X hX).size = 2 ^ X.card := by
  show ∏ _i : Fin X.card, 2 = 2 ^ X.card
  simp

theorem finsetGAP_pos (X : Finset ℤ) (hX : X.Nonempty) (i : Fin (finsetGAP X hX).dimension) :
    0 < (finsetGAP X hX).step i ∧ 0 < (finsetGAP X hX).length i := by
  refine ⟨?_, by simp [finsetGAP]⟩
  have h := X.min'_le _ (X.equivFin.symm i).2
  change 0 < (X.equivFin.symm i : ℤ) - X.min' hX + 1
  omega

theorem mem_finsetGAP (X : Finset ℤ) (hX : X.Nonempty) {x : ℤ} (hx : x ∈ X) :
    x ∈ (finsetGAP X hX).carrier := by
  classical
  let j : Fin X.card := X.equivFin ⟨x, hx⟩
  refine (GeneralizedAP.mem_carrier_iff _ _).mpr
    ⟨fun i => if i = j then 1 else 0, fun i => by
      change (if i = j then 1 else 0) < 2
      split_ifs <;> omega, ?_⟩
  change X.min' hX - 1 + ∑ i : Fin X.card,
      (if i = j then 1 else 0) • ((X.equivFin.symm i : ℤ) - X.min' hX + 1) = x
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
  have hj : (X.equivFin.symm j : ℤ) = x := by simp [j]
  simp only [↓reduceIte, one_smul, hj]
  ring

end FinsetGAP

end LeanProofs.GowersSzemeredi
