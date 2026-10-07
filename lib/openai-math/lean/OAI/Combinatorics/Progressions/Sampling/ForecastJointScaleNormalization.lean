/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.ForecastIntegerAxisSplit

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {X : Type*} [Fintype X]

noncomputable def forecastJointGridScale (R : Fin m → ℝ) (L : ℕ)
    (physicalN : X → ℕ) (τ : ℝ) : X ⊕ AllocatedActiveIntegerAxis U basis L → ℝ :=
  Sum.elim (fun i => τ * physicalN i / 8) (allocatedActiveIntegerGridScale U basis R L)

def forecastJointGridCenter (L : ℕ) (base : X → ℤ) :
    X ⊕ AllocatedActiveIntegerAxis U basis L → ℤ :=
  Sum.elim base (fun _ => 0)

omit [Fintype X] in
theorem forecastJointGridScale_pos {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (L : ℕ) (physicalN : X → ℕ) (hN : ∀ i, 0 < physicalN i) {τ : ℝ} (hτ : 0 < τ) :
    ∀ j, 0 < forecastJointGridScale U basis R L physicalN τ j := by
  intro j
  cases j with
  | inl i =>
    have hi : 0 < (physicalN i : ℝ) := by exact_mod_cast hN i
    change 0 < τ * physicalN i / 8
    positivity
  | inr a => exact allocatedActiveIntegerGridScale_pos U basis hR L a

omit [Fintype X] in
theorem forecastJointGridScale_mesh {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    {L : ℕ} (hL : 0 < L) (physicalN : X → ℕ) (hN : ∀ i, 0 < physicalN i)
    {τ H q cutoff δ : ℝ} (hτ : 0 < τ) (hq : 0 ≤ q) (hcutoff : 0 ≤ cutoff)
    (hRinv : ∀ j, (R j)⁻¹ ≤ H)
    (hspatial : ∀ i, q * cutoff * 8 * τ⁻¹ / physicalN i ≤ δ)
    (hactive : q * cutoff * H / L ≤ δ) :
    ∀ j, q * cutoff / forecastJointGridScale U basis R L physicalN τ j ≤ δ := by
  intro j
  cases j with
  | inl i =>
    have hi : (physicalN i : ℝ) ≠ 0 := by exact_mod_cast (hN i).ne'
    have he : q * cutoff / (τ * physicalN i / 8) =
        q * cutoff * 8 * τ⁻¹ / physicalN i := by
      field_simp [hτ.ne', hi]
    exact he.trans_le (hspatial i)
  | inr a =>
    exact (allocatedActiveIntegerGridScale_mesh U basis hR hL
      (mul_nonneg hq hcutoff) hRinv a).trans hactive

theorem forecastJointGridScale_prod (R : Fin m → ℝ) (L : ℕ)
    (physicalN : X → ℕ) (τ : ℝ) :
    (∏ j, forecastJointGridScale U basis R L physicalN τ j) =
      (τ / 8) ^ Fintype.card X * (∏ i, (physicalN i : ℝ)) *
        ∏ a, allocatedActiveIntegerGridScale U basis R L a := by
  rw [Fintype.prod_sum_type]
  change (∏ i : X, τ * physicalN i / 8) * _ = _
  have hterm (i : X) : τ * physicalN i / 8 = (τ / 8) * physicalN i := by ring
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rfl

theorem forecastJointGridScale_prod_eq_card [DecidableEq X]
    (R : Fin m → ℝ) (L : ℕ) (physicalN : X → ℕ) (τ : ℝ) :
    (∏ j, forecastJointGridScale U basis R L physicalN τ j) =
      (τ / 8) ^ Fintype.card X * (integerBox physicalN).card *
        ∏ a, allocatedActiveIntegerGridScale U basis R L a := by
  rw [forecastJointGridScale_prod, card_integerBox, Nat.cast_prod]

theorem forecastJointGridScale_prod_div_card [DecidableEq X]
    (R : Fin m → ℝ) (L : ℕ) (physicalN : X → ℕ) (τ : ℝ)
    (hN : ∀ i, 0 < physicalN i) :
    (∏ j, forecastJointGridScale U basis R L physicalN τ j) / (integerBox physicalN).card =
      (τ / 8) ^ Fintype.card X * ∏ a, allocatedActiveIntegerGridScale U basis R L a := by
  have hc : ((integerBox physicalN).card : ℝ) ≠ 0 := by
    rw [card_integerBox, Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast (hN i).ne')
  rw [forecastJointGridScale_prod_eq_card]
  field_simp

omit [Fintype X] in
theorem forecastJointGrid_normalized_join (R : Fin m → ℝ) (L : ℕ)
    (physicalN : X → ℕ) (τ : ℝ) (base u : X → ℤ)
    (v : AllocatedActiveIntegerAxis U basis L → ℤ) :
    (fun j => ((Sum.elim u v j : ℤ) - forecastJointGridCenter U basis L base j : ℝ) /
      forecastJointGridScale U basis R L physicalN τ j) =
    Sum.elim (fun i => ((u i : ℝ) - base i) / (τ * physicalN i / 8))
      (fun a => (v a : ℝ) / allocatedActiveIntegerGridScale U basis R L a) := by
  funext j
  cases j <;> simp [forecastJointGridScale, forecastJointGridCenter]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

noncomputable def forecastJointGridSamplerLog (d : ℕ) (P E Q PR : ℝ) : ℝ :=
  Q + (P + E + 5) + PR + forecastJointGridMeshLog d P E

noncomputable def forecastJointGridAmbientLog (d : ℕ) (P E Q Pτ : ℝ) : ℝ :=
  Q + (P + E + 5) + Pτ + forecastJointGridMeshLog d P E + 3

noncomputable def forecastJointGridSamplerFloor (d : ℕ) (P E Q PR : ℝ) : ℕ :=
  ⌈Real.exp (forecastJointGridSamplerLog d P E Q PR)⌉₊

theorem forecastJointGridSamplerFloor_lower (d : ℕ) (P E Q PR : ℝ) :
    Real.exp (forecastJointGridSamplerLog d P E Q PR) ≤
      (forecastJointGridSamplerFloor d P E Q PR : ℝ) := Nat.le_ceil _

theorem forecastJointGridSamplerFloor_pos (d : ℕ) (P E Q PR : ℝ) :
    0 < forecastJointGridSamplerFloor d P E Q PR := by
  exact_mod_cast (Real.exp_pos _).trans_le (forecastJointGridSamplerFloor_lower d P E Q PR)

theorem forecastJointGridSamplerFloor_le_exp (d : ℕ) {P E Q PR : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) (hQ : 0 ≤ Q) (hPR : 0 ≤ PR) :
    (forecastJointGridSamplerFloor d P E Q PR : ℝ) ≤
      Real.exp (forecastJointGridSamplerLog d P E Q PR + 1) := by
  have hlog : 0 ≤ forecastJointGridSamplerLog d P E Q PR := by
    unfold forecastJointGridSamplerLog
    have hmesh := forecastJointGridMeshLog_nonneg d hP hE
    positivity
  calc
    _ ≤ Real.exp (forecastJointGridSamplerLog d P E Q PR) + 1 :=
      (Nat.ceil_lt_add_one (Real.exp_nonneg _)).le
    _ = 1 + Real.exp (forecastJointGridSamplerLog d P E Q PR) := add_comm _ _
    _ ≤ _ := one_add_le_exp_succ hlog le_rfl

private theorem forecastGrid_exp_div_le {a B H : ℝ} {N : ℕ}
    (ha : a ≤ Real.exp B) (hN : Real.exp (B + H) ≤ (N : ℝ)) :
    a / N ≤ Real.exp (-H) := by
  have hNpos : (0 : ℝ) < N := (Real.exp_pos _).trans_le hN
  apply (div_le_iff₀ hNpos).mpr
  calc
    a ≤ Real.exp B := ha
    _ = Real.exp (-H) * Real.exp (B + H) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg _)

namespace VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {X : Type*} [Fintype X]

omit [Fintype X] in
theorem forecastJointGridScale_mesh_of_exp_bounds
    (d : ℕ) {P E Q Pτ PR : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) {τ : ℝ} (hτ : 0 < τ)
    (q L : ℕ) (physicalN : X → ℕ)
    (hq : (q : ℝ) ≤ Real.exp Q) (hτinv : τ⁻¹ ≤ Real.exp Pτ)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp PR)
    (hL : Real.exp (forecastJointGridSamplerLog d P E Q PR) ≤ (L : ℝ))
    (hN : ∀ i, Real.exp (forecastJointGridAmbientLog d P E Q Pτ) ≤ (physicalN i : ℝ)) :
    ∀ j, (((q * forecastJointGridCutoff P E : ℕ) : ℝ) /
      forecastJointGridScale U basis R L physicalN τ j) ≤ forecastJointGridMesh d P E := by
  have hLpos : 0 < L := Nat.cast_pos.mp ((Real.exp_pos _).trans_le hL)
  have hNpos (i : X) : 0 < physicalN i :=
    Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hN i))
  have hT := forecastJointGridCutoff_le_exp hP hE
  have hqT : (q : ℝ) * forecastJointGridCutoff P E ≤ Real.exp (Q + (P + E + 5)) := by
    rw [Real.exp_add]
    exact mul_le_mul hq hT (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hactive : (q : ℝ) * forecastJointGridCutoff P E * Real.exp PR / L ≤
      forecastJointGridMesh d P E := by
    apply forecastGrid_exp_div_le (B := Q + (P + E + 5) + PR)
    · rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hqT (Real.exp_nonneg _)
    · exact hL
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hspatial (i : X) : (q : ℝ) * forecastJointGridCutoff P E * 8 * τ⁻¹ / physicalN i ≤
      forecastJointGridMesh d P E := by
    apply forecastGrid_exp_div_le (B := Q + (P + E + 5) + 3 + Pτ)
    · have hnum := mul_le_mul
        (mul_le_mul hqT h8 (by norm_num) (Real.exp_nonneg _))
        hτinv (inv_nonneg.mpr hτ.le) (by positivity)
      exact hnum.trans_eq (by rw [← Real.exp_add, ← Real.exp_add])
    · convert hN i using 1
      congr 1
      unfold forecastJointGridAmbientLog
      ring
  have hm := forecastJointGridScale_mesh U basis hR hLpos physicalN hNpos hτ
    (Nat.cast_nonneg q) (Nat.cast_nonneg (forecastJointGridCutoff P E)) hRinv hspatial hactive
  intro j
  simpa only [Nat.cast_mul] using hm j

omit [Fintype X] in
theorem forecastJointGridScale_mesh_of_floor
    (d : ℕ) {P E Q Pτ PR : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) {τ : ℝ} (hτ : 0 < τ)
    (q L : ℕ) (physicalN : X → ℕ)
    (hq : (q : ℝ) ≤ Real.exp Q) (hτinv : τ⁻¹ ≤ Real.exp Pτ)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp PR)
    (hL : forecastJointGridSamplerFloor d P E Q PR ≤ L)
    (hN : ∀ i, Real.exp (forecastJointGridAmbientLog d P E Q Pτ) ≤ (physicalN i : ℝ)) :
    ∀ j, (((q * forecastJointGridCutoff P E : ℕ) : ℝ) /
      forecastJointGridScale U basis R L physicalN τ j) ≤ forecastJointGridMesh d P E := by
  apply forecastJointGridScale_mesh_of_exp_bounds U basis d hP hE hR hτ q L physicalN
    hq hτinv hRinv _ hN
  exact (forecastJointGridSamplerFloor_lower d P E Q PR).trans (by exact_mod_cast hL)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

private theorem forecastJacobian_product_le_exp {A : Type*} [Fintype A] {P : ℝ} (f : A → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hb : ∀ a, f a ≤ Real.exp P) :
    (∏ a, f a) ≤ Real.exp ((Fintype.card A : ℝ) * P) := by
  calc
    _ ≤ ∏ _a : A, Real.exp P := Finset.prod_le_prod₀ (fun a _ => hf a) (fun a _ => hb a)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]

variable {m : ℕ} {X : Type*} [Fintype X]
variable {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

noncomputable def forecastGeometricJacobian (R : Fin m → ℝ) (L : ℕ)
    (gridVolume τ : ℝ) : ℝ :=
  (coveredJetArrayScale (O := fun _ : Fin m => Unit) U * gridVolume *
    (τ / 8) ^ Fintype.card X * (∏ a : Σ j, I j, R a.1) *
    (∏ a, allocatedActiveIntegerGridScale U basis R L a))⁻¹

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

 theorem forecastGeometricJacobian_pos {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (L : ℕ) {gridVolume τ : ℝ} (hgrid : 0 < gridVolume) (hτ : 0 < τ) :
    0 < forecastGeometricJacobian (X := X) (I := I) U basis R L gridVolume τ := by
  unfold forecastGeometricJacobian
  apply inv_pos.mpr
  exact mul_pos (mul_pos (mul_pos (mul_pos (coveredJetArrayScale_pos U) hgrid)
    (pow_pos (div_pos hτ (by norm_num)) _))
    (Finset.prod_pos (fun a _ => hR a.1)))
    (Finset.prod_pos (fun a _ => allocatedActiveIntegerGridScale_pos U basis hR L a))

 theorem forecastGeometricJacobian_cancel {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (L : ℕ) {gridVolume τ : ℝ} (hgrid : 0 < gridVolume) (hτ : 0 < τ) :
    forecastGeometricJacobian (X := X) (I := I) U basis R L gridVolume τ *
      (coveredJetArrayScale (O := fun _ : Fin m => Unit) U * gridVolume *
        (τ / 8) ^ Fintype.card X * (∏ a : Σ j, I j, R a.1) *
        (∏ a, allocatedActiveIntegerGridScale U basis R L a)) = 1 := by
  have hp := forecastGeometricJacobian_pos (X := X) (I := I) U basis hR L hgrid hτ
  unfold forecastGeometricJacobian at hp ⊢
  exact inv_mul_cancel₀ (inv_pos.mp hp).ne'

 theorem forecastGeometricJacobian_le_exp {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (L : ℕ) {gridVolume τ P : ℝ} (hgrid : 1 ≤ gridVolume) (hτ : 0 < τ)
    (hτinv : τ⁻¹ ≤ Real.exp P) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hcovol : ∀ j, ZLattice.covolume
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))) ≤ Real.exp P) :
    forecastGeometricJacobian (X := X) (I := I) U basis R L gridVolume τ ≤
      Real.exp ((m : ℝ) * P + (Fintype.card X : ℝ) * (P + 3) +
        (Fintype.card (Σ j, I j) : ℝ) * P +
        (Fintype.card (AllocatedActiveIntegerAxis U basis L) : ℝ) * P) := by
  have hchart : (coveredJetArrayScale (O := fun _ : Fin m => Unit) U)⁻¹ ≤ Real.exp ((m : ℝ) * P) := by
    simpa only [coveredJetArrayScale, Fintype.card_unit, pow_one, ← Finset.prod_inv_distrib,
      inv_inv, Fintype.card_fin] using
      forecastJacobian_product_le_exp (fun j : Fin m => ZLattice.covolume
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))) volume)
        (fun j : Fin m => (ZLattice.covolume_pos
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))) volume).le) hcovol
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by convert Real.add_one_le_exp (1 : ℝ) using 1; norm_num
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hsp : ((τ / 8) ^ Fintype.card X)⁻¹ ≤
      Real.exp ((Fintype.card X : ℝ) * (P + 3)) := by
    rw [← inv_pow]
    have hi : (τ / 8)⁻¹ ≤ Real.exp (P + 3) := by
      calc
        _ = 8 * τ⁻¹ := by rw [inv_div, div_eq_mul_inv]
        _ ≤ Real.exp 3 * Real.exp P := mul_le_mul h8 hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    exact (pow_le_pow_left₀ (inv_nonneg.mpr (div_pos hτ (by norm_num)).le) hi _).trans_eq
      (Real.exp_nat_mul _ _).symm
  have hcontinuous : (∏ a : Σ j, I j, R a.1)⁻¹ ≤
      Real.exp ((Fintype.card (Σ j, I j) : ℝ) * P) := by
    simpa only [← Finset.prod_inv_distrib] using forecastJacobian_product_le_exp (fun a : Σ j, I j => (R a.1)⁻¹)
      (fun a => inv_nonneg.mpr (hR a.1).le) (fun a => hRinv a.1)
  have hactive : (∏ a, allocatedActiveIntegerGridScale U basis R L a)⁻¹ ≤
      Real.exp ((Fintype.card (AllocatedActiveIntegerAxis U basis L) : ℝ) * P) := by
    apply (show _ = ∏ a, (allocatedActiveIntegerGridScale U basis R L a)⁻¹ from by simp).trans_le
    apply forecastJacobian_product_le_exp (fun a : AllocatedActiveIntegerAxis U basis L =>
      (allocatedActiveIntegerGridScale U basis R L a)⁻¹) (fun a => inv_nonneg.mpr (allocatedActiveIntegerGridScale_pos U basis hR L a).le)
    intro a
    have hheight : (1 : ℝ) ≤ basisAxisScale (basis a.val.1) a.val.2 := by
      exact_mod_cast basisAxisScale_pos (basis a.val.1) a.val.2
    have hscale : R a.val.1 ≤ allocatedActiveIntegerGridScale U basis R L a := by
      simpa only [allocatedActiveIntegerGridScale, mul_one] using
        mul_le_mul_of_nonneg_left hheight (hR a.val.1).le
    exact (inv_anti₀ (hR a.val.1) hscale).trans (hRinv a.val.1)
  have hgridinv : gridVolume⁻¹ ≤ (1 : ℝ) := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hgrid
  have hcg := mul_le_mul hchart hgridinv
    (inv_nonneg.mpr (show 0 ≤ gridVolume by linarith)) (Real.exp_pos _).le
  have hcgs := mul_le_mul hcg hsp
    (inv_nonneg.mpr (pow_nonneg (div_pos hτ (by norm_num)).le _)) (by positivity)
  have hcgsc := mul_le_mul hcgs hcontinuous
    (inv_nonneg.mpr (Finset.prod_nonneg (fun a _ => (hR a.1).le))) (by positivity)
  have hfull := mul_le_mul hcgsc hactive
    (inv_nonneg.mpr (Finset.prod_nonneg
      (fun a _ => (allocatedActiveIntegerGridScale_pos U basis hR L a).le))) (by positivity)
  simpa only [forecastGeometricJacobian, mul_inv_rev, mul_one, ← Real.exp_add,
    one_mul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using hfull

theorem forecastGeometricJacobian_uniform_le_exp {R : Fin m → ℝ}
    (hR : ∀ j, 0 < R j) (L : ℕ) {gridVolume τ P : ℝ} (hP : 0 ≤ P)
    (hgrid : 1 ≤ gridVolume) (hτ : 0 < τ)
    (hτinv : τ⁻¹ ≤ Real.exp P) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hcovol : ∀ j, ZLattice.covolume
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))) ≤ Real.exp P) :
    forecastGeometricJacobian (X := X) (I := I) U basis R L gridVolume τ ≤
      Real.exp (((m : ℝ) + Fintype.card X + Fintype.card (Σ j, I j) +
        Fintype.card (Σ j : Fin m, Fin (n j))) * (P + 3)) := by
  apply (forecastGeometricJacobian_le_exp (X := X) (I := I) U basis hR L
    hgrid hτ hτinv hRinv hcovol).trans
  apply Real.exp_le_exp.mpr
  have hcard : (Fintype.card (AllocatedActiveIntegerAxis U basis L) : ℝ) ≤
      Fintype.card (Σ j : Fin m, Fin (n j)) := by
    exact_mod_cast (Fintype.card_subtype_le
      (fun a : Σ j : Fin m, Fin (n j) =>
        L ^ (a.1.val + 1) < basisAxisScale (basis a.1) a.2))
  have hmul := mul_le_mul_of_nonneg_right hcard hP
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hi0 : (0 : ℝ) ≤ Fintype.card (Σ j, I j) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ Fintype.card (Σ j : Fin m, Fin (n j)) := Nat.cast_nonneg _
  nlinarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
variable {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem forecastJointScale_normalization {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (L : ℕ) (physicalN : X → ℕ) (hN : ∀ x, 0 < physicalN x)
    {gridVolume τ : ℝ} (hgrid : 0 < gridVolume) (hτ : 0 < τ) :
    forecastGeometricJacobian (X := X) (I := I) U basis R L gridVolume τ *
      coveredJetArrayScale (O := fun _ : Fin m => Unit) U *
      (∏ a : Σ j, I j, R a.1) * gridVolume *
      (∏ j, forecastJointGridScale U basis R L physicalN τ j) /
      (integerBox physicalN).card = 1 := by
  rw [mul_div_assoc, forecastJointGridScale_prod_div_card U basis R L physicalN τ hN]
  convert forecastGeometricJacobian_cancel (X := X) (I := I) U basis hR L hgrid hτ using 1; ring

theorem forecastJointScale_complex_normalization {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (L : ℕ) (physicalN : X → ℕ) (hN : ∀ x, 0 < physicalN x)
    {gridVolume τ : ℝ} (hgrid : 0 < gridVolume) (hτ : 0 < τ) :
    (forecastGeometricJacobian (X := X) (I := I) U basis R L gridVolume τ : ℂ) *
      (coveredJetArrayScale (O := fun _ : Fin m => Unit) U : ℂ) *
      ((∏ a : Σ j, I j, R a.1) : ℂ) * (gridVolume : ℂ) *
      ((∏ j, forecastJointGridScale U basis R L physicalN τ j) : ℂ) /
      ((integerBox physicalN).card : ℂ) = 1 := by
  exact_mod_cast forecastJointScale_normalization U basis hR L physicalN hN hgrid hτ

end Erdos3.VectorPolynomial

end

end OAI
