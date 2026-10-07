import Mathlib.Analysis.Normed.Group.AddCircle
import OAI.Combinatorics.Progressions.Polynomial.ConstantPolynomialSingleSiteRealization

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset (Fin q))

noncomputable def coefficientAmbientRowsJet
    (z : CoefficientAmbientIndex (Fin q) J → UnitAddCircle) : JetAmbientIndex O J → UnitAddCircle :=
  fun t => ∑ e : BoundedCoefficientExponent (Fin q) (t.1.val + 1),
    (if rows t.1 t.2.1 = e.val.support then (1 : ℤ) else 0) • z ⟨⟨t.1, e⟩, t.2.2⟩

omit [∀ j, Fintype (O j)] in
theorem coefficientAmbientRowsJet_eq (U : ∀ j, Submodule ℝ (J j → ℝ))
    (z : CoefficientTorus (K := Fin q) U) :
    coefficientAmbientRowsJet rows (coefficientAmbientTorus U z) =
      coveredJetAmbientTorus U 1 (euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) rows z) := by
  funext t
  rcases t with ⟨j, t, i⟩
  simp only [coefficientAmbientRowsJet,
    coveredJetAmbientTorus_coefficient, Nat.cast_one, one_mul, boundedCoefficientJetMatrix_standard]

theorem coefficientAmbientRowsJet_lipschitz :
    LipschitzWith (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0))
      (coefficientAmbientRowsJet (q := q) (J := J) rows) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨j, t, i⟩
  have hterm (e : BoundedCoefficientExponent (Fin q) (j.val + 1)) :
      dist ((if rows j t = e.val.support then (1 : ℤ) else 0) • z ⟨⟨j,e⟩,i⟩)
        ((if rows j t = e.val.support then (1 : ℤ) else 0) • w ⟨⟨j,e⟩,i⟩) ≤ dist z w := by
    split_ifs
    · simpa only [one_zsmul] using dist_le_pi_dist z w ⟨⟨j,e⟩,i⟩
    · simp only [zero_zsmul, dist_self]
      exact dist_nonneg
  have hc : (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0) ≤
      ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0) :=
    Finset.single_le_sum (f := fun j : Fin m => (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0)) (fun _ _ => zero_le) (Finset.mem_univ j)
  calc
    _ ≤ ∑ _e : BoundedCoefficientExponent (Fin q) (j.val + 1), dist z w :=
      (dist_sum_sum_le _ _ _).trans (Finset.sum_le_sum (fun e _ => hterm e))
    _ = (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ) * dist z w := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg

noncomputable def coefficientAmbientRowsSite
    (rowSets : Fin m → Finset (Finset (Fin q))) (s : Finset (Fin q))
    (z : CoefficientAmbientIndex (Fin q) J → UnitAddCircle) :
    JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle :=
  rowSiteAmbientTorus rowSets s (coefficientAmbientRowsJet (fun _ => Subtype.val) z)

theorem coefficientAmbientRowsSite_lipschitz
    (rowSets : Fin m → Finset (Finset (Fin q))) (s : Finset (Fin q)) :
    LipschitzWith ((∑ j, ((rowSets j).card : ℝ≥0)) *
      (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0)))
      (coefficientAmbientRowsSite (J := J) rowSets s) :=
  (rowSiteAmbientTorus_lipschitz rowSets s).comp (coefficientAmbientRowsJet_lipschitz (fun _ => Subtype.val))

theorem coefficientAmbientRowsSite_eq
    (rowSets : Fin m → Finset (Finset (Fin q))) (s : Finset (Fin q))
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (z : CoefficientTorus (K := Fin q) U) :
    coefficientAmbientRowsSite rowSets s (coefficientAmbientTorus U z) =
      coveredJetAmbientTorus U 1 (coveredRowsSiteValue rowSets U
        (euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ)
          (fun j => (Subtype.val : rowSets j → Finset (Fin q))) z) s) := by
  unfold coefficientAmbientRowsSite
  rw [coefficientAmbientRowsJet_eq, coveredRowsSiteValue_ambient]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3
open scoped NNReal

theorem torus_nsmul_reindex_lipschitz {A B : Type*} [Fintype A] [Fintype B]
    (r : B → A) (n : ℕ) : LipschitzWith (n : ℝ≥0)
      (fun z : A → UnitAddCircle => fun i : B => n • z (r i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  calc
    _ = ‖n • (x (r i) - y (r i))‖ := by rw [dist_eq_norm, nsmul_sub]
    _ ≤ n * ‖x (r i) - y (r i)‖ := norm_nsmul_le
    _ ≤ (n : ℝ≥0) * dist x y := by
      rw [← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y (r i)) (Nat.cast_nonneg _)

namespace VectorPolynomial
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def physicalFactorCoverMap (period gridPeriod : ℕ)
    (z : (Σ j, J j) → UnitAddCircle) :
    (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
      ((Σ j, J j) → UnitAddCircle)) :=
  ((fun a => (period * gridPeriod) • z ⟨a.1, a.2.2⟩, fun a => gridPeriod • z a),
    fun a => period • z a)

theorem physicalFactorCoverMap_lipschitz (period gridPeriod : ℕ) :
    LipschitzWith (max (max ((period * gridPeriod : ℕ) : ℝ≥0) gridPeriod) period)
      (physicalFactorCoverMap (J := J) period gridPeriod) :=
  ((torus_nsmul_reindex_lipschitz (fun a : JetAmbientIndex (fun _ : Fin m => Unit) J =>
    (⟨a.1, a.2.2⟩ : Σ j, J j)) (period * gridPeriod)).prodMk
      (torus_nsmul_reindex_lipschitz id gridPeriod)).prodMk
        (torus_nsmul_reindex_lipschitz id period)

theorem physicalFactorCoverMap_lipschitz_mul (period gridPeriod : ℕ)
    [NeZero period] [NeZero gridPeriod] :
    LipschitzWith ((period * gridPeriod : ℕ) : ℝ≥0) (physicalFactorCoverMap (J := J) period gridPeriod) := by
  have hp : (period : ℝ≥0) ≤ ((period * gridPeriod : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.le_mul_of_pos_right period (Nat.pos_of_neZero gridPeriod)
  have hg : (gridPeriod : ℝ≥0) ≤ ((period * gridPeriod : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.le_mul_of_pos_left gridPeriod (Nat.pos_of_neZero period)
  exact (physicalFactorCoverMap_lipschitz period gridPeriod).weaken (max_le (max_le le_rfl hg) hp)

omit [∀ j, Fintype (J j)] in
theorem physicalFactorCoverMap_input {X : Type*} (period gridPeriod : ℕ)
    [NeZero period] [NeZero gridPeriod]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ) :
    physicalFactorCoverMap period gridPeriod (physicalGridFactorInput (period * gridPeriod) p t) =
      (physicalMaskedFactorInput period p t, physicalGridFactorInput gridPeriod p t) := by
  have hp : (period : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne period)
  have hg : (gridPeriod : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne gridPeriod)
  apply Prod.ext
  · apply Prod.ext
    · funext a
      simp only [physicalFactorCoverMap, physicalGridFactorInput, physicalMaskedFactorInput,
        ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul]
      congr 1
      field_simp
    · funext a
      simp only [physicalFactorCoverMap, physicalGridFactorInput, physicalMaskedFactorInput,
        ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul]
      congr 1
      field_simp
  · funext a
    simp only [physicalFactorCoverMap, physicalGridFactorInput,
      ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul]
    congr 1
    field_simp

theorem physical_factor_on_common_cover {X : Type*} (period gridPeriod : ℕ)
    [NeZero period] [NeZero gridPeriod]
    (g : (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
      ((Σ j, J j) → UnitAddCircle)) → ℂ) {L : ℝ≥0}
    (hg : LipschitzWith L g) (hb : ∀ z, ‖g z‖ ≤ 1) :
    ∃ f : ((Σ j, J j) → UnitAddCircle) → ℂ,
      LipschitzWith (L * ((period * gridPeriod : ℕ) : ℝ≥0)) f ∧
      (∀ z, ‖f z‖ ≤ 1) ∧
      ∀ (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ),
        f (physicalGridFactorInput (period * gridPeriod) p t) =
          g (physicalMaskedFactorInput period p t, physicalGridFactorInput gridPeriod p t) := by
  refine ⟨g ∘ physicalFactorCoverMap period gridPeriod,
    hg.comp (physicalFactorCoverMap_lipschitz_mul period gridPeriod), fun z => hb _, ?_⟩
  intro p t
  exact congrArg g (physicalFactorCoverMap_input period gridPeriod p t)

noncomputable def physicalCoverPolynomial {X D : Type*} (q : ℕ)
    (p : VectorPolynomial X ℝ (D → ℝ)) : VectorPolynomial X ℝ (D → ℝ) :=
  map ((q : ℝ)⁻¹ • LinearMap.id) p

theorem physicalCoverPolynomial_eval {X D : Type*} (q : ℕ)
    (p : VectorPolynomial X ℝ (D → ℝ)) (t : X → ℝ) :
    eval t (physicalCoverPolynomial q p) = fun i => eval t p i / q := by
  rw [physicalCoverPolynomial, eval_map]
  funext i
  change (q : ℝ)⁻¹ * eval t p i = eval t p i / q
  ring

theorem physicalCoverPolynomial_degree {X D : Type*} (q : ℕ)
    (p : VectorPolynomial X ℝ (D → ℝ)) {w : X → ℕ} {d : ℕ} (hp : DegreeLE w d p) :
    DegreeLE w d (physicalCoverPolynomial q p) := hp.map _

omit [∀ j, Fintype (J j)] in
theorem physicalGridFactorInput_coverPolynomial {X : Type*} (q : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ) :
    physicalGridFactorInput q p t = fun a => (eval t (physicalCoverPolynomial q (p a.1)) a.2 : UnitAddCircle) := by
  funext a
  rw [physicalCoverPolynomial_eval]
  rfl

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical NNReal

variable {X : Type*} {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

include hp in
theorem coefficientCoverSample_physicalRows {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin q)) (v : X → (Unit ⊕ Fin q) → ℤ) :
    euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) rows
      (affineCoefficientCoverSample U p hm d (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))) =
      physicalCubeRowSample U d rows p hm v := by
  let D : Fin q → Fin q → ℤ := fun i j => if i = j then 1 else 0
  have hD : Matrix.of D = (1 : Matrix (Fin q) (Fin q) ℤ) := by
    ext i j
    simp [D, Matrix.one_apply]
  have h := coefficientCoverSample_sites U (fun _ : Fin q => 0) D d p hp hm
    (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))
  rw [affineCoveredSiteSample_zero_base_physical, hD,
    physicalCubeRootDifferences_standard, standardPhysicalCubeOutput_frame] at h
  have hjet := congrArg (fun t : SiteTorus (Finset (Fin q)) U =>
    euclideanJetEquiv U (siteBooleanJetTorusMap U rows t)) h
  change euclideanCoefficientJetMap U (fun _ : Fin q => 0) (Matrix.of D) rows
    (affineCoefficientCoverSample U p hm d (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))) =
      physicalCubeRowSample U d rows p hm v at hjet
  simpa only [hD] using hjet

theorem physicalSingleSiteValue_ambient_one (w : X → ℝ) :
    coveredJetAmbientTorus U 1 (physicalSingleSiteValue U d p hm w) =
      fun a : JetAmbientIndex (fun _ : Fin m => Unit) J =>
        ((eval w (p a.1) a.2.2 / d : ℝ) : UnitAddCircle) := by
  funext a
  rcases a with ⟨j, t, i⟩
  cases t
  change subspaceAmbientTorus (U j) (euclideanSubspaceTorusEquiv (U j)
    (1 • (euclideanSubspaceTorusEquiv (U j)).symm
      (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j))
        (fun _ => (d : ℝ)⁻¹ • eval w (restrictCoefficients (U j) (p j) (hm j)))))) i = _
  rw [one_nsmul, AddEquiv.apply_symm_apply, subspaceAmbientTorus_mk]
  simp only [Pi.smul_apply, Submodule.coe_smul_of_tower, smul_eq_mul,
    eval_restrictCoefficients, div_eq_mul_inv, mul_comm]

noncomputable def coefficientAmbientVertex
    (s : Finset (Fin q)) (z : CoefficientAmbientIndex (Fin q) J → UnitAddCircle) :
    (Σ j, J j) → UnitAddCircle :=
  fun a => coefficientAmbientRowsSite
    (fun j : Fin m => boundedBooleanJetRows (Fin q) (j.val + 1)) s z ⟨a.1, (), a.2⟩

theorem coefficientAmbientVertex_lipschitz (s : Finset (Fin q)) :
    LipschitzWith ((∑ j : Fin m, ((boundedBooleanJetRows (Fin q) (j.val + 1)).card : ℝ≥0)) *
      (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0)))
      (coefficientAmbientVertex (J := J) s) := by
  have h := (torus_nsmul_reindex_lipschitz
    (fun a : Σ j, J j => (⟨a.1, (), a.2⟩ : JetAmbientIndex (fun _ : Fin m => Unit) J)) 1).comp
    (coefficientAmbientRowsSite_lipschitz (J := J)
      (fun j : Fin m => boundedBooleanJetRows (Fin q) (j.val + 1)) s)
  simp only [Nat.cast_one, one_mul, one_nsmul, Function.comp_def] at h
  convert h using 1
  congr! (transparency := .reducible)

include hp in
theorem coefficientAmbientVertex_sample (s : Finset (Fin q))
    (v : X → (Unit ⊕ Fin q) → ℤ) :
    coefficientAmbientVertex s (coefficientAmbientTorus U
      (affineCoefficientCoverSample U p hm d (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ)))) =
      physicalGridFactorInput d p (fun x => (physicalCubeVertexValue v s x : ℝ)) := by
  unfold coefficientAmbientVertex
  rw [coefficientAmbientRowsSite_eq, coefficientCoverSample_physicalRows U d p hp hm,
    coveredRowsSiteValue_physical U d p hm hp, physicalSingleSiteValue_ambient_one]
  rfl

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped BigOperators Classical NNReal

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {pw cw pv cv : ℝ} {Lw Lv : ℝ≥0}

private theorem complex_dist_product (a b c d : ℂ) :
    dist (a * b) (c * d) ≤ ‖a‖ * dist b d + dist a c * ‖d‖ := by
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  calc
    _ = ‖a * (b - d) + (a - c) * d‖ := by congr 1; ring
    _ ≤ ‖a * (b - d)‖ + ‖(a - c) * d‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_mul]

noncomputable def product
    (W : NormalizedPolynomialTwist X Y pw cw Lw)
    (V : NormalizedPolynomialTwist X Y pv cv Lv) :
    NormalizedPolynomialTwist X Y (pw * pv) (cw * cv)
      (Lw * max 1 (V.cover : ℝ≥0) + Lv * max 1 (W.cover : ℝ≥0)) where
  modulus := W.modulus * V.modulus
  modulus_pos := Nat.mul_pos W.modulus_pos V.modulus_pos
  modulus_bound := by
    rw [Nat.cast_mul]
    exact mul_le_mul W.modulus_bound V.modulus_bound (Nat.cast_nonneg _)
      ((Nat.cast_nonneg _).trans W.modulus_bound)
  cover := W.cover * V.cover
  cover_pos := Nat.mul_pos W.cover_pos V.cover_pos
  cover_bound := by
    rw [Nat.cast_mul]
    exact mul_le_mul W.cover_bound V.cover_bound (Nat.cast_nonneg _)
      ((Nat.cast_nonneg _).trans W.cover_bound)
  mask := fun r => W.mask (fun x => ZMod.castHom (dvd_mul_right W.modulus V.modulus)
      (ZMod W.modulus) (r x)) *
    V.mask (fun x => ZMod.castHom (dvd_mul_left V.modulus W.modulus) (ZMod V.modulus) (r x))
  mask_bound := by
    intro r
    rw [norm_mul]
    exact (mul_le_mul (W.mask_bound _) (V.mask_bound _) (norm_nonneg _) zero_le_one).trans_eq
      (mul_one 1)
  smooth := fun z => W.smooth (z.1, fun y => V.cover • z.2 y) *
    V.smooth (z.1, fun y => W.cover • z.2 y)
  smooth_bound := by
    intro z
    rw [norm_mul]
    exact (mul_le_mul (W.smooth_bound _) (V.smooth_bound _) (norm_nonneg _) zero_le_one).trans_eq
      (mul_one 1)
  smooth_lipschitz := by
    have hmap (n : ℕ) : LipschitzWith (max 1 (n : ℝ≥0))
        (fun z : (X → ℝ) × (Y → UnitAddCircle) => (z.1, fun y => n • z.2 y)) := by
      have hn : LipschitzWith (n : ℝ≥0)
          (fun z : (X → ℝ) × (Y → UnitAddCircle) => fun y => n • z.2 y) := by
        simpa only [mul_one, Function.comp_def] using
          (torus_nsmul_reindex_lipschitz (fun y : Y => y) n).comp
            (LipschitzWith.prod_snd (α := X → ℝ))
      exact LipschitzWith.prod_fst.prodMk hn
    have hf := W.smooth_lipschitz.comp (hmap V.cover)
    have hg := V.smooth_lipschitz.comp (hmap W.cover)
    apply LipschitzWith.of_dist_le_mul
    intro z w
    calc
      _ ≤ ‖W.smooth (z.1, fun y => V.cover • z.2 y)‖ *
          dist (V.smooth (z.1, fun y => W.cover • z.2 y))
            (V.smooth (w.1, fun y => W.cover • w.2 y)) +
        dist (W.smooth (z.1, fun y => V.cover • z.2 y))
          (W.smooth (w.1, fun y => V.cover • w.2 y)) *
          ‖V.smooth (w.1, fun y => W.cover • w.2 y)‖ := complex_dist_product _ _ _ _
      _ ≤ 1 * (((Lv * max 1 (W.cover : ℝ≥0) : ℝ≥0) : ℝ) * dist z w) +
        (((Lw * max 1 (V.cover : ℝ≥0) : ℝ≥0) : ℝ) * dist z w) * 1 := by
        exact add_le_add
          (mul_le_mul (W.smooth_bound _) (hg.dist_le_mul z w) dist_nonneg zero_le_one)
          (mul_le_mul (hf.dist_le_mul z w) (V.smooth_bound _) (norm_nonneg _)
            (by positivity))
      _ = _ := by push_cast; ring

@[simp] theorem product_eval {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (V : NormalizedPolynomialTwist X (Σ j, J j) pv cv Lv)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.product V).eval N p u = W.eval N p u * V.eval N p u := by
  have hw : (W.cover : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr W.cover_pos.ne'
  have hv : (V.cover : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr V.cover_pos.ne'
  have hfirst : (fun a => V.cover • physicalGridFactorInput (W.cover * V.cover) p
      (fun x => (u x : ℝ)) a) = physicalGridFactorInput W.cover p (fun x => (u x : ℝ)) := by
    funext a
    simp only [physicalGridFactorInput, ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul]
    congr 1
    field_simp
  have hsecond : (fun a => W.cover • physicalGridFactorInput (W.cover * V.cover) p
      (fun x => (u x : ℝ)) a) = physicalGridFactorInput V.cover p (fun x => (u x : ℝ)) := by
    funext a
    simp only [physicalGridFactorInput, ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul]
    congr 1
    field_simp
  have hmaskfirst : (fun x => ZMod.castHom (dvd_mul_right W.modulus V.modulus)
      (ZMod W.modulus) ((u x : ℤ) : ZMod (W.modulus * V.modulus))) =
      (fun x => (u x : ZMod W.modulus)) := by
    funext x
    exact map_intCast (ZMod.castHom (dvd_mul_right W.modulus V.modulus) (ZMod W.modulus)) (u x)
  have hmasksecond : (fun x => ZMod.castHom (dvd_mul_left V.modulus W.modulus)
      (ZMod V.modulus) ((u x : ℤ) : ZMod (W.modulus * V.modulus))) =
      (fun x => (u x : ZMod V.modulus)) := by
    funext x
    exact map_intCast (ZMod.castHom (dvd_mul_left V.modulus W.modulus) (ZMod V.modulus)) (u x)
  change (W.mask (fun x => ZMod.castHom (dvd_mul_right W.modulus V.modulus)
      (ZMod W.modulus) ((u x : ℤ) : ZMod (W.modulus * V.modulus))) *
    V.mask (fun x => ZMod.castHom (dvd_mul_left V.modulus W.modulus)
      (ZMod V.modulus) ((u x : ℤ) : ZMod (W.modulus * V.modulus)))) *
    (W.smooth ((fun x => (u x : ℝ) / N x), fun a => V.cover •
      physicalGridFactorInput (W.cover * V.cover) p (fun x => (u x : ℝ)) a) *
    V.smooth ((fun x => (u x : ℝ) / N x), fun a => W.cover •
      physicalGridFactorInput (W.cover * V.cover) p (fun x => (u x : ℝ)) a)) = _
  rw [hmaskfirst, hmasksecond, hfirst, hsecond]
  unfold eval
  ring

theorem product_lipschitz_le
    (W : NormalizedPolynomialTwist X Y pw cw Lw)
    (V : NormalizedPolynomialTwist X Y pv cv Lv) :
    Lw * max 1 (V.cover : ℝ≥0) + Lv * max 1 (W.cover : ℝ≥0) ≤
      Lw * max 1 (Real.toNNReal cv) + Lv * max 1 (Real.toNNReal cw) := by
  have hw : (W.cover : ℝ≥0) ≤ Real.toNNReal cw := by
    exact (NNReal.coe_le_coe).mp (W.cover_bound.trans (Real.le_coe_toNNReal cw))
  have hv : (V.cover : ℝ≥0) ≤ Real.toNNReal cv := by
    exact (NNReal.coe_le_coe).mp (V.cover_bound.trans (Real.le_coe_toNNReal cv))
  exact add_le_add (mul_le_mul_of_nonneg_left (max_le_max_left 1 hv) (show 0 ≤ Lw from zero_le))
    (mul_le_mul_of_nonneg_left (max_le_max_left 1 hw) (show 0 ≤ Lv from zero_le))

noncomputable def productUniform
    (W : NormalizedPolynomialTwist X Y pw cw Lw)
    (V : NormalizedPolynomialTwist X Y pv cv Lv) :
    NormalizedPolynomialTwist X Y (pw * pv) (cw * cv)
      (Lw * max 1 (Real.toNNReal cv) + Lv * max 1 (Real.toNNReal cw)) :=
  (W.product V).mono le_rfl le_rfl (W.product_lipschitz_le V)

@[simp] theorem productUniform_eval {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (V : NormalizedPolynomialTwist X (Σ j, J j) pv cv Lv)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.productUniform V).eval N p u = W.eval N p u * V.eval N p u := by
  exact W.product_eval V N p u

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
local notation "Input" => (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) ×
  ((Σ j, J j) → UnitAddCircle)) × ((Σ j, J j) → UnitAddCircle))

noncomputable def coefficientAmbientModelTerm (period gridPeriod : ℕ)
    (g : Finset (Fin q) → Input → ℂ)
    (z : CoefficientAmbientIndex (Fin q) J → UnitAddCircle) : ℂ :=
  ∏ s, g s (physicalFactorCoverMap period gridPeriod (coefficientAmbientVertex s z))

theorem coefficientAmbientModelTerm_bounds (period gridPeriod : ℕ)
    [NeZero period] [NeZero gridPeriod]
    (g : Finset (Fin q) → Input → ℂ) {L : ℝ≥0}
    (hg : ∀ s, LipschitzWith L (g s)) (hgb : ∀ s z, ‖g s z‖ ≤ 1) :
    (∀ z, ‖coefficientAmbientModelTerm period gridPeriod g z‖ ≤ 1) ∧
    LipschitzWith (Fintype.card (Finset (Fin q)) * (L * (period * gridPeriod) *
      ((∑ j : Fin m, ((boundedBooleanJetRows (Fin q) (j.val + 1)).card : ℝ≥0)) *
        ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0))))
      (coefficientAmbientModelTerm period gridPeriod g) := by
  have h := bounded_lipschitz_fintype_prod
    (fun s z => g s (physicalFactorCoverMap period gridPeriod (coefficientAmbientVertex s z)))
    (B := 1) le_rfl
    (fun s => ((hg s).comp (physicalFactorCoverMap_lipschitz_mul period gridPeriod)).comp
      (coefficientAmbientVertex_lipschitz s))
    (fun s z => hgb s _)
  simp only [Nat.cast_mul, one_pow, mul_one, NNReal.coe_one] at h
  unfold coefficientAmbientModelTerm
  convert h using 1

theorem coefficientAmbientModelTerm_sample {X : Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (period gridPeriod : ℕ)
    [NeZero period] [NeZero gridPeriod]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (g : Finset (Fin q) → Input → ℂ) (v : X → (Unit ⊕ Fin q) → ℤ) :
    coefficientAmbientModelTerm period gridPeriod g (coefficientAmbientTorus U
      (affineCoefficientCoverSample U p hm (period * gridPeriod)
        (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ)))) =
      ∏ s, g s (physicalMaskedFactorInput period p (fun x => (physicalCubeVertexValue v s x : ℝ)),
        physicalGridFactorInput gridPeriod p (fun x => (physicalCubeVertexValue v s x : ℝ))) := by
  unfold coefficientAmbientModelTerm
  apply Finset.prod_congr rfl
  intro s _
  rw [coefficientAmbientVertex_sample U (period * gridPeriod) p hp hm,
    physicalFactorCoverMap_input]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := Fin q) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
variable [BorelSpace (CoefficientTorus (K := Fin q) U)]
variable (μ : Measure (CoefficientTorus (K := Fin q) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})
noncomputable local instance physicalRowsFintype (j : Fin m) : Fintype (Row j) :=
  Finset.Subtype.fintype (boundedBooleanJetRows (Fin q) (j.val + 1))
local notation "rows" => (fun j => (Subtype.val : Row j → Finset (Fin q)))
local notation "jet" => euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) rows
local notation "ξ" => Measure.pi (fun j => Measure.pi (fun _ : Row j => ν j))

theorem physicalRowsCoefficient_measurePreserving (a : ℕ) (ha : 0 < a) :
    MeasurePreserving (fun z => jet (quotientIntegerCover (coefficientIntegerLattice U) a z)) μ ξ := by
  have hperiod : integerScalarLattice (Fin q) (1 : ℤ) ≤
      (1 : Matrix (Fin q) (Fin q) ℤ).mulVecLin.range := by
    intro v _
    exact ⟨v, by simp⟩
  exact (euclideanCoefficientJetMap_measurePreserving U (fun _ => 0)
    (1 : Matrix (Fin q) (Fin q) ℤ) 1 one_ne_zero hperiod rows
    (fun _ => Subtype.val_injective)
    (fun j s => (mem_boundedBooleanJetRows (j.val + 1) s.val).mp s.property) μ ν).comp
      (coefficientCover_measurePreserving U μ a ha)

theorem physicalRowsCoefficient_square_integral
    (a : ℕ) (ha : 0 < a) (f g : EuclideanJetLayers U Row → ℂ)
    (hf : Measurable f) (hg : Measurable g) :
    (∫ z, ‖f (jet (quotientIntegerCover (coefficientIntegerLattice U) a z)) -
      g (jet (quotientIntegerCover (coefficientIntegerLattice U) a z))‖ ^ 2 ∂μ) =
      ∫ y, ‖f y - g y‖ ^ 2 ∂ξ := by
  have hp := physicalRowsCoefficient_measurePreserving U μ ν a ha
  have hm : AEStronglyMeasurable (fun y => ‖f y - g y‖ ^ 2)
      (Measure.map (fun z => jet (quotientIntegerCover (coefficientIntegerLattice U) a z)) μ) := by
    rw [hp.map_eq]
    exact ((hf.sub hg).norm.pow_const 2).aestronglyMeasurable
  have he := (integral_map hp.measurable.aemeasurable hm).symm
  rw [hp.map_eq] at he
  convert he using 1
  congr! (transparency := .reducible)

theorem physicalRowsCoefficient_square_le_of_l1
    (a : ℕ) (ha : 0 < a) (f g : EuclideanJetLayers U Row → ℂ)
    (hf : Measurable f) (hg : Measurable g) (Cf Cg : ℝ≥0)
    (hfb : ∀ y, ‖f y‖ ≤ Cf) (hgb : ∀ y, ‖g y‖ ≤ Cg) {E : ℝ}
    (hE : (∫ y, ‖f y - g y‖ ∂ξ) ≤ E) :
    (∫ z, ‖f (jet (quotientIntegerCover (coefficientIntegerLattice U) a z)) -
      g (jet (quotientIntegerCover (coefficientIntegerLattice U) a z))‖ ^ 2 ∂μ) ≤
      (Cf + Cg : ℝ≥0) * E := by
  rw [physicalRowsCoefficient_square_integral U μ ν a ha f g hf hg]
  let : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Row j => ν j)) := by
    intro j
    have ht := Measure.pi.instIsProbabilityMeasure (fun _ : Row j => ν j)
    convert ht using 1
  let : IsProbabilityMeasure ξ := Measure.pi.instIsProbabilityMeasure _
  exact complex_model_l2_le_of_l1 ξ f g hf hg Cf Cg hfb hgb hE

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {X : Type*} [Fintype X] {pw cw : ℝ} {Lw : ℝ≥0}

noncomputable def nativeSingleSiteCoverObservable
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (physicalN : X → ℕ) (u : X → ℤ) (Q : ℕ)
    (y : EuclideanJetLayers U (fun _ => Unit)) : ℂ :=
  W.frozenTorus (fun i => (u i : ZMod W.modulus)) (fun i => (u i : ℝ) / physicalN i)
    (fun a => coveredJetAmbientTorus U (Q / W.cover) y ⟨a.1, (), a.2⟩)

theorem nativeSingleSiteCoverObservable_continuous
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (physicalN : X → ℕ) (u : X → ℤ) (Q : ℕ) :
    Continuous (nativeSingleSiteCoverObservable U W physicalN u Q) := by
  apply (W.frozenTorus_lipschitz _ _).continuous.comp
  apply continuous_pi
  intro a
  exact (continuous_apply (⟨a.1, (), a.2⟩ : JetAmbientIndex (fun _ => Unit) J)).comp
    (coveredJetAmbientTorus_continuous U (Q / W.cover))

theorem norm_nativeSingleSiteCoverObservable_le
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (physicalN : X → ℕ) (u : X → ℤ) (Q : ℕ)
    (y : EuclideanJetLayers U (fun _ => Unit)) :
    ‖nativeSingleSiteCoverObservable U W physicalN u Q y‖ ≤ 1 :=
  W.norm_frozenTorus_le _ _ _

theorem nativeSingleSiteCoverObservable_physical
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (physicalN : X → ℕ) (u : X → ℤ) (Q : ℕ) (hQ : 0 < Q) (hd : W.cover ∣ Q)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j) :
    nativeSingleSiteCoverObservable U W physicalN u Q
      (physicalSingleSiteValue U Q poly hm (fun i => (u i : ℝ))) = W.eval physicalN poly u :=
  (W.eval_commonCover U physicalN poly hm Q hQ hd u).symm

theorem nativeSingleSiteCoverObservable_projection
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (physicalN : X → ℕ) (u : X → ℤ) (N Q : ℕ) (hN : 0 < N) (hQ : 0 < Q)
    (hNQ : N ∣ Q) (hWN : W.cover ∣ N)
    (y : EuclideanJetLayers U (fun _ => Unit)) :
    nativeSingleSiteCoverObservable U W physicalN u N (singleSiteIntegerCover U (Q / N) y) =
      nativeSingleSiteCoverObservable U W physicalN u Q y := by
  obtain ⟨poly, hm, _, hy⟩ := exists_constantPolynomial_singleSiteValue (X := X) U Q hQ y
  rw [← hy (fun i => (u i : ℝ)), physicalSingleSiteValue_divisor_projection U poly hm Q N hQ hNQ,
    nativeSingleSiteCoverObservable_physical U W physicalN u N hN hWN,
    nativeSingleSiteCoverObservable_physical U W physicalN u Q hQ (hWN.trans hNQ)]

theorem nativeSingleSiteCoverObservable_product
    {pf cf : ℝ} {Lf : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (F : NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
    (physicalN : X → ℕ) (u : X → ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hd : (W.product F).cover ∣ Q)
    (y : EuclideanJetLayers U (fun _ => Unit)) :
    nativeSingleSiteCoverObservable U (W.product F) physicalN u Q y =
      nativeSingleSiteCoverObservable U W physicalN u Q y *
        nativeSingleSiteCoverObservable U F physicalN u Q y := by
  have hW : W.cover ∣ Q := (dvd_mul_right W.cover F.cover).trans hd
  have hF : F.cover ∣ Q := (dvd_mul_left F.cover W.cover).trans hd
  obtain ⟨poly, hm, _, hy⟩ := exists_constantPolynomial_singleSiteValue (X := X) U Q hQ y
  rw [← hy (fun i => (u i : ℝ)),
    nativeSingleSiteCoverObservable_physical U (W.product F) physicalN u Q hQ hd,
    nativeSingleSiteCoverObservable_physical U W physicalN u Q hQ hW,
    nativeSingleSiteCoverObservable_physical U F physicalN u Q hQ hF,
    NormalizedPolynomialTwist.product_eval]

variable [CompactSpace (EuclideanJetLayers U (fun _ => Unit))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))

theorem nativePhysicalHaarExpansion
    {T : Type*} [Fintype T] {pf cf : ℝ} {Lf : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (F : T → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
    (c : T → ℂ) (κ : ℂ) (δ : ℝ)
    (physicalN : X → ℕ) (u : X → ℤ) (N : ℕ) (hN : 0 < N) (hWN : W.cover ∣ N)
    (f : EuclideanJetLayers U (fun _ => Unit) → ℂ) (hf : Measurable f)
    (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j e, coefficients (poly j) e ∈ U j),
      ‖κ * f (physicalSingleSiteValue U N poly hm (fun i => (u i : ℝ))) -
        ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ) :
    ‖(∫ y, κ * f y * nativeSingleSiteCoverObservable U W physicalN u N y ∂haar) -
      ∑ i, c i * (W.product (F i)).frozenSingleSiteHaarReference U ν
        (fun j => (u j : ZMod (W.product (F i)).modulus))
        (fun j => (u j : ℝ) / physicalN j)‖ ≤ δ := by
  have : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Unit => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  have : IsProbabilityMeasure haar := Measure.pi.instIsProbabilityMeasure _
  let Q := N * ∏ i, (W.product (F i)).cover
  have hQ : 0 < Q := Nat.mul_pos hN (Finset.prod_pos fun i _ => (W.product (F i)).cover_pos)
  have hNQ : N ∣ Q := dvd_mul_right _ _
  have hprod (i : T) : (W.product (F i)).cover ∣ Q :=
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) N
  have hF (i : T) : (F i).cover ∣ Q :=
    (dvd_mul_left (F i).cover W.cover).trans (hprod i)
  let projection := singleSiteIntegerCover U (Q / N)
  let left := fun y => κ * f (projection y) * nativeSingleSiteCoverObservable U W physicalN u Q y
  let right := fun y => ∑ i, c i * nativeSingleSiteCoverObservable U (W.product (F i)) physicalN u Q y
  have herr (y) : ‖left y - right y‖ ≤ δ := by
    obtain ⟨poly, hm, _, hy⟩ := exists_constantPolynomial_singleSiteValue (X := X) U Q hQ y
    have ha := happrox poly hm
    have hw := W.norm_eval_le physicalN poly u
    have hfactor : left y - right y = W.eval physicalN poly u *
        (κ * f (physicalSingleSiteValue U N poly hm (fun i => (u i : ℝ))) -
          ∑ i, c i * (F i).eval physicalN poly u) := by
      dsimp [left, right, projection]
      rw [← hy (fun i => (u i : ℝ)),
        physicalSingleSiteValue_divisor_projection U poly hm Q N hQ hNQ,
        nativeSingleSiteCoverObservable_physical U W physicalN u Q hQ (hWN.trans hNQ)]
      simp_rw [nativeSingleSiteCoverObservable_physical U (W.product _) physicalN u Q hQ (hprod _),
        NormalizedPolynomialTwist.product_eval]
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro i _
        ring
    rw [hfactor, norm_mul]
    exact (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans (by simpa using ha)
  have hrightInt : Integrable right haar := by
    apply integrable_finsetSum
    intro i _
    apply Integrable.const_mul
    apply Integrable.of_bound
      (nativeSingleSiteCoverObservable_continuous U (W.product (F i)) physicalN u Q).aestronglyMeasurable 1
    exact ae_of_all _ fun y => norm_nativeSingleSiteCoverObservable_le U _ physicalN u Q y
  have hrightBound (y) : ‖right y‖ ≤ ∑ i, ‖c i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_nativeSingleSiteCoverObservable_le U _ physicalN u Q y)
      (norm_nonneg _)).trans_eq (mul_one _)
  have hleftMeas : Measurable left :=
    (measurable_const.mul (hf.comp (singleSiteIntegerCover_continuous U (Q / N)).measurable)).mul
      (nativeSingleSiteCoverObservable_continuous U W physicalN u Q).measurable
  have hleftInt : Integrable left haar := by
    apply Integrable.of_bound hleftMeas.aestronglyMeasurable (δ + ∑ i, ‖c i‖)
    apply ae_of_all
    intro y
    calc
      ‖left y‖ ≤ ‖left y - right y‖ + ‖right y‖ := norm_le_norm_sub_add _ _
      _ ≤ δ + ∑ i, ‖c i‖ := add_le_add (herr y) (hrightBound y)
  have hcomparison := probability_integral_approximation haar left right hleftInt hrightInt herr
  have hleft : (∫ y, left y ∂haar) =
      ∫ y, κ * f y * nativeSingleSiteCoverObservable U W physicalN u N y ∂haar := by
    have he (y) : left y =
        (fun z => κ * f z * nativeSingleSiteCoverObservable U W physicalN u N z) (projection y) := by
      dsimp [left, projection]
      rw [nativeSingleSiteCoverObservable_projection U W physicalN u N Q hN hQ hNQ hWN]
    simp_rw [he]
    exact singleSiteIntegerCover_integral U ν (Q / N) (Nat.div_pos (Nat.le_of_dvd hQ hNQ) hN) _
      ((measurable_const.mul hf).mul
        (nativeSingleSiteCoverObservable_continuous U W physicalN u N).measurable).aestronglyMeasurable
  have hright : (∫ y, right y ∂haar) =
      ∑ i, c i * (W.product (F i)).frozenSingleSiteHaarReference U ν
        (fun j => (u j : ZMod (W.product (F i)).modulus))
        (fun j => (u j : ℝ) / physicalN j) := by
    rw [show (∫ y, right y ∂haar) = ∑ i, ∫ y,
      c i * nativeSingleSiteCoverObservable U (W.product (F i)) physicalN u Q y ∂haar from
      integral_finsetSum _ (fun i _ => by
        apply Integrable.const_mul
        apply Integrable.of_bound
          (nativeSingleSiteCoverObservable_continuous U (W.product (F i)) physicalN u Q).aestronglyMeasurable 1
        exact ae_of_all _ fun y => norm_nativeSingleSiteCoverObservable_le U _ physicalN u Q y)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
    congr 1
    exact (W.product (F i)).frozenSingleSiteHaarReference_commonCover U ν _ _ Q hQ (hprod i)
  rwa [hleft, hright] at hcomparison

end Erdos3.VectorPolynomial

end

end OAI
