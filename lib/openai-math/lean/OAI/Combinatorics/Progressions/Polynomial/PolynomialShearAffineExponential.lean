/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Nilpotent.Basic
import OAI.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialDerivationDrop (w : σ → ℕ) (k : ℕ) :
    Submodule R (Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) where
  carrier := {D | ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k}
  zero_mem' := by
    intro i
    exact Submodule.zero_mem _
  add_mem' := by
    intro D E hD hE i
    exact (weightedSupportDrop w (w i) k).add_mem (hD i) (hE i)
  smul_mem' := by
    intro c D hD i
    exact (weightedSupportDrop w (w i) k).smul_mem c (hD i)

theorem polynomialDerivationDrop_antitone (w : σ → ℕ) :
    Antitone (polynomialDerivationDrop (R := R) w) := by
  intro a b hab D hD i
  exact weightedSupportDrop_antitone hab (hD i)

theorem polynomialDerivationDrop_bracket (w : σ → ℕ) (a b : ℕ)
    {D E : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)}
    (hD : D ∈ polynomialDerivationDrop w a) (hE : E ∈ polynomialDerivationDrop w b) :
    ⁅D, E⁆ ∈ polynomialDerivationDrop w (a + b) :=
  weightedDerivation_bracket w D E a b hD hE

noncomputable def polynomialLoweringLieAlgebra (w : σ → ℕ) :
    LieSubalgebra R (Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) :=
  { polynomialDerivationDrop w 1 with
    lie_mem' := fun hD hE => polynomialDerivationDrop_antitone w (by decide : 1 ≤ 1 + 1)
      (polynomialDerivationDrop_bracket w 1 1 hD hE) }

abbrev PolynomialShearLieAlgebra (w : σ → ℕ) (R : Type*) [CommRing R] :=
  ↥(polynomialLoweringLieAlgebra (R := R) w)

noncomputable def polynomialShearLayer (w : σ → ℕ) (k : ℕ) :
    Submodule R (PolynomialShearLieAlgebra w R) :=
  (polynomialDerivationDrop w k).comap (polynomialLoweringLieAlgebra w).incl.toLinearMap

theorem mem_polynomialShearLayer (w : σ → ℕ) (k : ℕ) (D : PolynomialShearLieAlgebra w R) :
    D ∈ polynomialShearLayer (R := R) w k ↔
      ∀ i, D.val (X i) ∈ weightedSupportDrop w (w i) k := Iff.rfl

theorem polynomialShearLayer_antitone (w : σ → ℕ) :
    Antitone (polynomialShearLayer (R := R) w) := by
  intro a b hab D hD
  exact polynomialDerivationDrop_antitone w hab hD

theorem polynomialShearLayer_one (w : σ → ℕ) :
    polynomialShearLayer (R := R) w 1 = ⊤ := by
  apply top_unique
  intro D _
  exact D.property

theorem polynomialShearLayer_bracket (w : σ → ℕ) (a b : ℕ)
    {D E : PolynomialShearLieAlgebra w R}
    (hD : D ∈ polynomialShearLayer (R := R) w a)
    (hE : E ∈ polynomialShearLayer (R := R) w b) :
    ⁅D, E⁆ ∈ polynomialShearLayer (R := R) w (a + b) :=
  polynomialDerivationDrop_bracket w a b hD hE

theorem polynomialShearLayer_terminal (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    polynomialShearLayer (R := R) w (s + 1) = ⊥ := by
  apply bot_unique
  intro D hD
  change D = 0
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  change D.val (X i) = 0
  exact weightedSupportDrop_eq_zero (Nat.lt_succ_of_le (hw i)) (hD i)

noncomputable def polynomialShearFiltration (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    NilpotentLieFiltration (PolynomialShearLieAlgebra w ℚ) s where
  layer := polynomialShearLayer w
  antitone := polynomialShearLayer_antitone w
  one_eq_top := polynomialShearLayer_one w
  lie_mem := polynomialShearLayer_bracket w _ _
  terminal := polynomialShearLayer_terminal w s hw

theorem polynomialShear_lowerCentralSeries_eq_bot (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    LieModule.lowerCentralSeries ℚ (PolynomialShearLieAlgebra w ℚ)
      (PolynomialShearLieAlgebra w ℚ) s = ⊥ :=
  (polynomialShearFiltration w s hw).lowerCentralSeries_eq_bot

theorem polynomialShear_group_nilpotencyClass_le (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    Group.nilpotencyClass (polynomialShearFiltration w s hw).Group ≤ s :=
  (polynomialShearFiltration w s hw).nilpotencyClass_le

end Erdos3

end

section

namespace Erdos3

open MvPolynomial Module

variable {σ R : Type*} [CommRing R]

abbrev PolynomialShearIndex (w : σ → ℕ) :=
  Σ i : σ, {a : σ →₀ ℕ // Finsupp.weight w a + 1 ≤ w i}

noncomputable def polynomialShearCoordinates (w : σ → ℕ) :
    PolynomialShearLieAlgebra w R ≃ₗ[R] (i : σ) → weightedSupportDrop (R := R) w (w i) 1 where
  toFun D i := ⟨D.val (X i), D.property i⟩
  invFun f := ⟨MvPolynomial.mkDerivation R (fun i => (f i : MvPolynomial σ R)), by
    intro i
    rw [MvPolynomial.mkDerivation_X]
    exact (f i).property⟩
  left_inv D := by
    apply Subtype.ext
    apply MvPolynomial.derivation_ext
    intro i
    exact MvPolynomial.mkDerivation_X _ _ _
  right_inv f := by
    funext i
    apply Subtype.ext
    exact MvPolynomial.mkDerivation_X _ _ _
  map_add' D E := by
    funext i
    apply Subtype.ext
    rfl
  map_smul' c D := by
    funext i
    apply Subtype.ext
    rfl

theorem polynomialShearCoordinates_apply (w : σ → ℕ) (D : PolynomialShearLieAlgebra w R) (i : σ) :
    (polynomialShearCoordinates (R := R) w D i : MvPolynomial σ R) = D.val (X i) := rfl

noncomputable def polynomialShearBasis [Fintype σ] (w : σ → ℕ) :
    Basis (PolynomialShearIndex w) R (PolynomialShearLieAlgebra w R) :=
  (Pi.basis (fun i => MvPolynomial.basisRestrictSupport R
    {a : σ →₀ ℕ | Finsupp.weight w a + 1 ≤ w i})).map (polynomialShearCoordinates w).symm

theorem polynomialShearBasis_repr [Fintype σ] (w : σ → ℕ)
    (D : PolynomialShearLieAlgebra w R) (a : PolynomialShearIndex w) :
    (polynomialShearBasis (R := R) w).repr D a = (D.val (X a.1)).coeff a.2.val := rfl

noncomputable def polynomialShearMonomial (w : σ → ℕ) (a : PolynomialShearIndex w) :
    PolynomialShearLieAlgebra w R := by
  classical
  refine ⟨MvPolynomial.mkDerivation R (Pi.single a.1 (monomial a.2.val 1)), ?_⟩
  intro i
  rw [MvPolynomial.mkDerivation_X]
  by_cases h : i = a.1
  · subst i
    rw [Pi.single_eq_same]
    exact (MvPolynomial.monomial_mem_restrictSupport R).mpr (Or.inl a.2.property)
  · rw [Pi.single_eq_of_ne h]
    exact Submodule.zero_mem _

theorem polynomialShearMonomial_X [DecidableEq σ] (w : σ → ℕ) (a : PolynomialShearIndex w) (i : σ) :
    (polynomialShearMonomial (R := R) w a).val (X i) =
      if i = a.1 then monomial a.2.val 1 else 0 := by
  classical
  rw [polynomialShearMonomial, MvPolynomial.mkDerivation_X]
  by_cases h : i = a.1
  · subst i
    simp only [Pi.single_eq_same, ite_true]
  · simp [h]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial Module

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialShearBoundedCoordinates (w : σ → ℕ) (s : ℕ)
    (hw : ∀ i, w i ≤ s) :
    PolynomialShearLieAlgebra w R →ₗ[R] (σ → weightedSupportLE (R := R) w s) where
  toFun D i := ⟨D.val (X i), weightedSupportLE_mono (hw i)
    (weightedSupportDrop_le (D.property i))⟩
  map_add' D E := by
    funext i
    apply Subtype.ext
    rfl
  map_smul' c D := by
    funext i
    apply Subtype.ext
    rfl

theorem polynomialShearBoundedCoordinates_injective (w : σ → ℕ) (s : ℕ)
    (hw : ∀ i, w i ≤ s) :
    Function.Injective (polynomialShearBoundedCoordinates (R := R) w s hw) := by
  intro D E h
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  exact congrArg (fun f : σ → weightedSupportLE (R := R) w s => (f i : MvPolynomial σ R)) h

theorem polynomialShear_moduleFinite {K : Type*} [Field K] [Fintype σ]
    (w : σ → ℕ) (hwpos : ∀ i, 0 < w i) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    Module.Finite K (PolynomialShearLieAlgebra w K) := by
  let : Module.Finite K (weightedSupportLE (R := K) w s) := weightedSupportLE_moduleFinite w hwpos s
  exact Module.Finite.of_injective (polynomialShearBoundedCoordinates w s hw)
    (polynomialShearBoundedCoordinates_injective w s hw)

theorem polynomialShear_finrank_le {K : Type*} [Field K] [Fintype σ]
    (w : σ → ℕ) (hwpos : ∀ i, 0 < w i) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    finrank K (PolynomialShearLieAlgebra w K) ≤ Fintype.card σ * (Fintype.card σ + 1) ^ s := by
  let : Module.Finite K (weightedSupportLE (R := K) w s) := weightedSupportLE_moduleFinite w hwpos s
  calc
    _ ≤ finrank K (σ → weightedSupportLE (R := K) w s) :=
      LinearMap.finrank_le_finrank_of_injective
        (polynomialShearBoundedCoordinates_injective (R := K) w s hw)
    _ = ∑ _i : σ, finrank K (weightedSupportLE (R := K) w s) := Module.finrank_pi_fintype K
    _ = Fintype.card σ * finrank K (weightedSupportLE (R := K) w s) := by simp
    _ ≤ Fintype.card σ * (Fintype.card σ + 1) ^ s :=
      Nat.mul_le_mul_left _ (weightedSupportLE_finrank_le (K := K) w hwpos s)

theorem polynomialShear_finrank_fin {K : Type*} [Field K] {d : ℕ}
    (w : Fin d → ℕ) (hwpos : ∀ i, 0 < w i) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    finrank K (PolynomialShearLieAlgebra w K) ≤ d * (d + 1) ^ s := by
  simpa only [Fintype.card_fin] using polynomialShear_finrank_le (K := K) w hwpos s hw

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*} [Fintype σ] {w : σ → ℕ}

theorem polynomialShear_X_mass_of_coordinates (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {s : ℕ} (hw : ∀ i, w i ≤ s)
    {δ : ℝ} (hδ : 0 ≤ δ) (hD : ∀ a, |(polynomialShearBasis (R := ℝ) w).repr D a| ≤ δ) (i : σ) :
    realPolynomialMass (D.val (X i)) ≤ ((s + 1) * (Fintype.card σ + 1) ^ s : ℕ) * δ := by
  classical
  have hdegree : (D.val (X i)).totalDegree ≤ s :=
    totalDegree_le_of_positive_weightedSupport w hpos
      (weightedSupportLE_mono (hw i) (weightedSupportDrop_le (D.property i)))
  calc
    _ ≤ ∑ _a ∈ (D.val (X i)).support, δ := by
      apply Finset.sum_le_sum
      intro a ha
      exact hD ⟨i, a, D.property i ha⟩
    _ = ((D.val (X i)).support.card : ℝ) * δ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast polynomial_support_card_le _ hdegree) hδ

omit [Fintype σ] in
theorem polynomialShear_pow_degree (D : PolynomialShearLieAlgebra w ℝ)
    {P : MvPolynomial σ ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) (k : ℕ) :
    (D.val.toLinearMap ^ k) P ∈ weightedSupportLE w n := by
  have h := weightedDerivation_pow w D.val 1 D.property
    (show P ∈ weightedSupportDrop w n 0 by rwa [weightedSupportDrop_zero]) k
  exact weightedSupportDrop_le h

theorem polynomialShear_pow_mass (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {M : ℝ} (hM : 0 ≤ M)
    (hD : ∀ i, realPolynomialMass (D.val (X i)) ≤ M)
    {P : MvPolynomial σ ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) (k : ℕ) :
    realPolynomialMass ((D.val.toLinearMap ^ k) P) ≤
      (Fintype.card σ * M * n) ^ k * realPolynomialMass P := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      have hdegree := totalDegree_le_of_positive_weightedSupport w hpos
        (polynomialShear_pow_degree D hP k)
      apply (realPolynomialMass_derivation D.val hM hD hdegree).trans
      calc
        _ ≤ (Fintype.card σ * M * n) *
            ((Fintype.card σ * M * n) ^ k * realPolynomialMass P) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by rw [pow_succ']; ring

theorem polynomialShear_pow_mass_of_coordinates (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {s : ℕ} (hw : ∀ i, w i ≤ s)
    {δ : ℝ} (hδ : 0 ≤ δ) (hD : ∀ a, |(polynomialShearBasis (R := ℝ) w).repr D a| ≤ δ)
    {P : MvPolynomial σ ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) (k : ℕ) :
    realPolynomialMass ((D.val.toLinearMap ^ k) P) ≤
      (Fintype.card σ * (((s + 1) * (Fintype.card σ + 1) ^ s : ℕ) * δ) * n) ^ k *
        realPolynomialMass P :=
  polynomialShear_pow_mass D hpos (by positivity)
    (polynomialShear_X_mass_of_coordinates D hpos hw hδ hD) hP k

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {σ R : Type*} [CommRing R] {w : σ → ℕ}

noncomputable def polynomialShearEnd (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    Module.End R (weightedSupportLE (R := R) w n) where
  toFun P := ⟨D.val P, weightedSupportDrop_le
    (weightedDerivation_apply_le w D.val 1 D.property P.property)⟩
  map_add' P Q := by
    apply Subtype.ext
    exact D.val.map_add P Q
  map_smul' c P := by
    apply Subtype.ext
    exact D.val.map_smul c P

theorem polynomialShearEnd_apply_coe (D : PolynomialShearLieAlgebra w R) (n : ℕ)
    (P : weightedSupportLE (R := R) w n) :
    (polynomialShearEnd D n P : MvPolynomial σ R) = D.val P := rfl

noncomputable def polynomialShearAction (w : σ → ℕ) (n : ℕ) :
    PolynomialShearLieAlgebra w R →ₗ⁅R⁆ Module.End R (weightedSupportLE (R := R) w n) where
  toLinearMap :=
    { toFun := fun D => polynomialShearEnd D n
      map_add' := by
        intro D E
        apply LinearMap.ext
        intro P
        apply Subtype.ext
        rfl
      map_smul' := by
        intro c D
        apply LinearMap.ext
        intro P
        apply Subtype.ext
        rfl }
  map_lie' := by
    intro D E
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    rfl

theorem polynomialShearEnd_pow_coe (D : PolynomialShearLieAlgebra w R) (n k : ℕ)
    (P : weightedSupportLE (R := R) w n) :
    ((polynomialShearEnd D n ^ k) P : MvPolynomial σ R) =
      (D.val.toLinearMap ^ k) (P : MvPolynomial σ R) := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      rfl

theorem polynomialShearEnd_pow_eq_zero (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    polynomialShearEnd D n ^ (n + 1) = 0 := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  change ((polynomialShearEnd D n ^ (n + 1)) P : MvPolynomial σ R) = 0
  rw [polynomialShearEnd_pow_coe]
  exact weightedDerivation_pow_eq_zero w D.val D.property P.property

theorem polynomialShearEnd_isNilpotent (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    IsNilpotent (polynomialShearEnd D n) := ⟨n + 1, polynomialShearEnd_pow_eq_zero D n⟩

theorem polynomialShearAction_injective (w : σ → ℕ) (n : ℕ) (hw : ∀ i, w i ≤ n) :
    Function.Injective (polynomialShearAction (R := R) w n) := by
  intro D E h
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  exact congrArg (fun F : Module.End R (weightedSupportLE (R := R) w n) =>
    (F ⟨X i, weightedSupportLE_mono (hw i) (weightedSupportLE_X w i)⟩ : MvPolynomial σ R)) h

end Erdos3

end

section

namespace Erdos3

open MvPolynomial Module

variable {σ R : Type*} [CommRing R] [Fintype σ]

theorem polynomialShearMonomial_repr (w : σ → ℕ) (a : PolynomialShearIndex w) :
    (polynomialShearBasis (R := R) w).repr (polynomialShearMonomial (R := R) w a) =
      Finsupp.single a 1 := by
  classical
  ext b
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  rw [polynomialShearBasis_repr, polynomialShearMonomial_X]
  by_cases hij : j = i
  · subst j
    by_cases hab : a = b
    · subst b
      simp
    · have hval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
      simp [hab, hval]
  · simp [hij]

theorem polynomialShearBasis_eq_monomial (w : σ → ℕ) (a : PolynomialShearIndex w) :
    polynomialShearBasis (R := R) w a = polynomialShearMonomial w a := by
  apply (polynomialShearBasis (R := R) w).repr.injective
  rw [Basis.repr_self, polynomialShearMonomial_repr]

noncomputable def polynomialShearDeficit (w : σ → ℕ) (a : PolynomialShearIndex w) : ℕ :=
  w a.1 - Finsupp.weight w a.2.val

omit [Fintype σ] in
theorem polynomialShearDeficit_pos (w : σ → ℕ) (a : PolynomialShearIndex w) :
    0 < polynomialShearDeficit w a := by
  have h := a.2.property
  unfold polynomialShearDeficit
  omega

theorem polynomialShearBasis_mem_layer (w : σ → ℕ) (a : PolynomialShearIndex w) (r : ℕ)
    (hr : r ≤ polynomialShearDeficit w a) :
    polynomialShearBasis (R := R) w a ∈ polynomialShearLayer (R := R) w r := by
  classical
  rw [polynomialShearBasis_eq_monomial]
  intro i
  change (polynomialShearMonomial (R := R) w a).val (X i) ∈ weightedSupportDrop w (w i) r
  rw [polynomialShearMonomial_X]
  by_cases hi : i = a.1
  · subst i
    rw [ite_eq_left rfl]
    apply (MvPolynomial.monomial_mem_restrictSupport R).mpr
    left
    change Finsupp.weight w a.2.val + r ≤ w a.1
    have h := a.2.property
    unfold polynomialShearDeficit at hr
    omega
  · rw [ite_eq_right hi]
    exact Submodule.zero_mem _

theorem polynomialShearLayer_span (w : σ → ℕ) (r : ℕ) :
    polynomialShearLayer (R := R) w r =
      Submodule.span R (polynomialShearBasis (R := R) w '' {a | r ≤ polynomialShearDeficit w a}) := by
  classical
  apply le_antisymm
  · intro D hD
    apply (polynomialShearBasis (R := R) w).mem_span_image.mpr
    intro a ha
    have hc : (D.val (X a.1)).coeff a.2.val ≠ 0 := by
      simpa only [polynomialShearBasis_repr] using Finsupp.mem_support_iff.mp ha
    have h : Finsupp.weight w a.2.val + r ≤ w a.1 :=
      hD a.1 (MvPolynomial.mem_support_iff.mpr hc)
    change r ≤ w a.1 - Finsupp.weight w a.2.val
    omega
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact polynomialShearBasis_mem_layer w a r ha

@[instance_reducible]
noncomputable def polynomialShearIndexFintype (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    Fintype (PolynomialShearIndex w) := by
  classical
  have hfinite (i : σ) : {a : σ →₀ ℕ | Finsupp.weight w a + 1 ≤ w i}.Finite :=
    (Finsupp.finite_of_nat_weight_le w (fun j => (hw j).ne') (w i)).subset
      (fun a ha => (Nat.le_add_right (Finsupp.weight w a) 1).trans ha)
  letI (i : σ) : Fintype {a : σ →₀ ℕ // Finsupp.weight w a + 1 ≤ w i} := (hfinite i).fintype
  exact inferInstance

omit [Fintype σ] in
theorem polynomialShearDeficit_le (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)
    (a : PolynomialShearIndex w) : polynomialShearDeficit w a ≤ s :=
  (Nat.sub_le _ _).trans (hw a.1)

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

noncomputable def polynomialShearExpOn (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    Module.End R (weightedSupportLE (R := R) w n) :=
  IsNilpotent.exp (polynomialShearEnd D n)

theorem polynomialShearExpOn_sum (D : PolynomialShearLieAlgebra w R) (n : ℕ)
    (P : weightedSupportLE (R := R) w n) :
    (polynomialShearExpOn D n P : MvPolynomial σ R) =
      ∑ k ∈ Finset.range (n + 1), (k.factorial : ℚ)⁻¹ •
        (D.val.toLinearMap ^ k) (P : MvPolynomial σ R) := by
  simp [polynomialShearExpOn, IsNilpotent.exp_eq_sum (a := polynomialShearEnd D n) (polynomialShearEnd_pow_eq_zero D n),
    polynomialShearEnd_pow_coe]

theorem polynomialShearExpOn_mono (D : PolynomialShearLieAlgebra w R)
    {m n : ℕ} (hmn : m ≤ n) (P : weightedSupportLE (R := R) w m) :
    (polynomialShearExpOn D n ⟨P.val, weightedSupportLE_mono hmn P.property⟩ :
      MvPolynomial σ R) = (polynomialShearExpOn D m P : MvPolynomial σ R) := by
  let inc : weightedSupportLE (R := R) w m →ₗ[R] weightedSupportLE (R := R) w n :=
    Submodule.inclusion (fun _ h => weightedSupportLE_mono hmn h)
  have hc : polynomialShearEnd D n ∘ₗ inc = inc ∘ₗ polynomialShearEnd D m := by
    ext Q
    rfl
  have h := Module.End.commute_exp_left_of_commute (polynomialShearEnd_isNilpotent D m)
    (polynomialShearEnd_isNilpotent D n) hc
  exact congrArg Subtype.val (LinearMap.congr_fun h P)

noncomputable def weightedPolynomialMul (w : σ → ℕ) (m n : ℕ) :
    weightedSupportLE (R := R) w m →ₗ[R]
      weightedSupportLE (R := R) w n →ₗ[R] weightedSupportLE (R := R) w (m + n) where
  toFun P :=
    { toFun := fun Q => ⟨P.val * Q.val, weightedSupportLE_mul P.property Q.property⟩
      map_add' := fun Q T => Subtype.ext (mul_add P.val Q.val T.val)
      map_smul' := fun c Q => Subtype.ext (mul_smul_comm c P.val Q.val) }
  map_add' P Q := by
    apply LinearMap.ext
    intro T
    exact Subtype.ext (add_mul P.val Q.val T.val)
  map_smul' c P := by
    apply LinearMap.ext
    intro Q
    exact Subtype.ext (smul_mul_assoc c P.val Q.val)

theorem polynomialShearExpOn_mul (D : PolynomialShearLieAlgebra w R) (m n : ℕ)
    (P : weightedSupportLE (R := R) w m) (Q : weightedSupportLE (R := R) w n) :
    (polynomialShearExpOn D (m + n) (weightedPolynomialMul w m n P Q) : MvPolynomial σ R) =
      (polynomialShearExpOn D m P : MvPolynomial σ R) *
        (polynomialShearExpOn D n Q : MvPolynomial σ R) := by
  have h := nilpotentExp_bilinear (weightedPolynomialMul (R := R) w m n)
    (polynomialShearEnd D m) (polynomialShearEnd D n) (polynomialShearEnd D (m + n))
    (polynomialShearEnd_isNilpotent D m) (polynomialShearEnd_isNilpotent D n)
    (polynomialShearEnd_isNilpotent D (m + n))
    (fun x y => Subtype.ext (by
      change D.val (x.val * y.val) = D.val x.val * y.val + x.val * D.val y.val
      rw [D.val.leibniz, smul_eq_mul, smul_eq_mul]
      ring)) P Q
  exact congrArg Subtype.val h

end Erdos3

end

section

namespace Erdos3

open MvPolynomial Module
open scoped BigOperators Classical

variable {σ R : Type*} [CommRing R] [Fintype σ]

theorem polynomialShearBasis_coordinate_eval (w : σ → ℕ)
    [Fintype (PolynomialShearIndex w)] (D : PolynomialShearLieAlgebra w R) (i : σ) :
    D.val (X i) = ∑ a : PolynomialShearIndex w,
      if a.1 = i then C ((polynomialShearBasis (R := R) w).repr D a) * monomial a.2.val 1
      else 0 := by
  classical
  let ev : PolynomialShearLieAlgebra w R →ₗ[R] MvPolynomial σ R :=
    { toFun := fun E => E.val (X i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  calc
    D.val (X i) = ev (∑ a, (polynomialShearBasis (R := R) w).repr D a •
        polynomialShearBasis (R := R) w a) :=
      congrArg ev ((polynomialShearBasis (R := R) w).sum_repr D).symm
    _ = ∑ a, (polynomialShearBasis (R := R) w).repr D a •
        (polynomialShearBasis (R := R) w a).val (X i) := by
      rw [map_sum]
      simp only [map_smul]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [polynomialShearBasis_eq_monomial, polynomialShearMonomial_X]
      by_cases h : a.1 = i
      · simp [h, smul_eq_C_mul]
      · simp [h, Ne.symm h]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

noncomputable def polynomialShearExp (D : PolynomialShearLieAlgebra w R)
    (P : MvPolynomial σ R) : MvPolynomial σ R :=
  polynomialShearExpOn D (P.weightedTotalDegree w)
    ⟨P, (mem_weightedSupportLE_iff w _ P).mpr le_rfl⟩

theorem polynomialShearExp_eq_on (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearExp D P = (polynomialShearExpOn D n ⟨P, hP⟩ : MvPolynomial σ R) :=
  (polynomialShearExpOn_mono D ((mem_weightedSupportLE_iff w n P).mp hP)
    ⟨P, (mem_weightedSupportLE_iff w _ P).mpr le_rfl⟩).symm

theorem polynomialShearExp_eq_sum (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearExp D P = ∑ k ∈ Finset.range (n + 1),
      (k.factorial : ℚ)⁻¹ • (D.val.toLinearMap ^ k) P := by
  rw [polynomialShearExp_eq_on D hP]
  exact polynomialShearExpOn_sum D n ⟨P, hP⟩

theorem polynomialShearExp_degree (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearExp D P ∈ weightedSupportLE w n := by
  rw [polynomialShearExp_eq_on D hP]
  exact (polynomialShearExpOn D n ⟨P, hP⟩).property

theorem polynomialShearExp_add (D : PolynomialShearLieAlgebra w R)
    (P Q : MvPolynomial σ R) :
    polynomialShearExp D (P + Q) = polynomialShearExp D P + polynomialShearExp D Q := by
  let n := P.weightedTotalDegree w + Q.weightedTotalDegree w
  have hp : P ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n P).mpr (Nat.le_add_right _ _)
  have hq : Q ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n Q).mpr (Nat.le_add_left _ _)
  rw [polynomialShearExp_eq_on D ((weightedSupportLE w n).add_mem hp hq),
    polynomialShearExp_eq_on D hp, polynomialShearExp_eq_on D hq]
  exact congrArg Subtype.val ((polynomialShearExpOn D n).map_add ⟨P, hp⟩ ⟨Q, hq⟩)

theorem polynomialShearExp_smul (D : PolynomialShearLieAlgebra w R)
    (c : R) (P : MvPolynomial σ R) :
    polynomialShearExp D (c • P) = c • polynomialShearExp D P := by
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  rw [polynomialShearExp_eq_on D ((weightedSupportLE w _).smul_mem c hp),
    polynomialShearExp_eq_on D hp]
  exact congrArg Subtype.val ((polynomialShearExpOn D _).map_smul c ⟨P, hp⟩)

theorem polynomialShearExp_mul (D : PolynomialShearLieAlgebra w R)
    (P Q : MvPolynomial σ R) :
    polynomialShearExp D (P * Q) = polynomialShearExp D P * polynomialShearExp D Q := by
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  have hq : Q ∈ weightedSupportLE w (Q.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ Q).mpr le_rfl
  rw [polynomialShearExp_eq_on D (weightedSupportLE_mul hp hq),
    polynomialShearExp_eq_on D hp, polynomialShearExp_eq_on D hq]
  exact polynomialShearExpOn_mul D _ _ ⟨P, hp⟩ ⟨Q, hq⟩

theorem polynomialShearExp_C (D : PolynomialShearLieAlgebra w R) (c : R) :
    polynomialShearExp D (C c) = C c := by
  rw [polynomialShearExp_eq_sum D (weightedSupportLE_C w 0 c)]
  simp

noncomputable def polynomialShearExpHom (D : PolynomialShearLieAlgebra w R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R where
  toFun := polynomialShearExp D
  map_one' := by simpa using polynomialShearExp_C D 1
  map_zero' := by simpa using polynomialShearExp_C D 0
  map_add' := polynomialShearExp_add D
  map_mul' := polynomialShearExp_mul D
  commutes' := polynomialShearExp_C D

theorem polynomialShearExp_sub_lower (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearExp D P - P ∈ weightedSupportLT w n := by
  rw [polynomialShearExp_eq_sum D hP, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply,
    one_smul, add_sub_cancel_right]
  apply (weightedSupportLT w n).sum_mem
  intro k hk
  have h := weightedDerivation_pow w D.val 1 D.property
    (show P ∈ weightedSupportDrop w n 0 by rwa [weightedSupportDrop_zero]) (k + 1)
  simp only [Nat.mul_one, Nat.zero_add] at h
  have hlow : (D.val.toLinearMap ^ (k + 1)) P ∈ weightedSupportLT w n := by
    rw [← weightedSupportDrop_one]
    exact weightedSupportDrop_antitone (Nat.le_add_left 1 k) h
  exact (weightedSupportLT (R := R) w n).restrictScalars ℚ |>.smul_mem _ hlow

noncomputable def polynomialShearExpAut (D : PolynomialShearLieAlgebra w R) :
    WeightedLoweringAut w R :=
  WeightedLoweringAut.ofHom w (polynomialShearExpHom D)
    (fun i => polynomialShearExp_sub_lower D (weightedSupportLE_X w i))

theorem polynomialShearExpAut_apply (D : PolynomialShearLieAlgebra w R)
    (P : MvPolynomial σ R) : (polynomialShearExpAut D).val P = polynomialShearExp D P := rfl

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

theorem polynomialShearExp_eq_add_of_sq_eq_zero (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} (hP : (D.val.toLinearMap ^ 2) P = 0) :
    polynomialShearExp D P = P + D.val P := by
  let n := max (P.weightedTotalDegree w) 1
  have hdeg : P ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n P).mpr (le_max_left _ _)
  have htwo : 2 ≤ n + 1 := Nat.succ_le_succ (le_max_right _ _)
  rw [polynomialShearExp_eq_sum D hdeg]
  have hsum :
      (∑ k ∈ Finset.range 2, (k.factorial : ℚ)⁻¹ • (D.val.toLinearMap ^ k) P) =
      ∑ k ∈ Finset.range (n + 1), (k.factorial : ℚ)⁻¹ • (D.val.toLinearMap ^ k) P := by
    apply Finset.sum_subset (Finset.range_mono htwo)
    intro k _ hk
    have hk2 : 2 ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
    rw [Module.End.pow_map_zero_of_le hk2 hP, smul_zero]
  rw [← hsum]
  simp [Finset.sum_range_succ]

theorem polynomialShearExp_X_of_derivation_eq_C (D : PolynomialShearLieAlgebra w R)
    (i : σ) (b : R) (hD : D.val (X i) = C b) :
    polynomialShearExp D (X i) = X i + C b := by
  have hsq : (D.val.toLinearMap ^ 2) (X i) = 0 := by
    change D.val (D.val (X i)) = 0
    rw [hD, MvPolynomial.derivation_C]
  rw [polynomialShearExp_eq_add_of_sq_eq_zero D hsq, hD]

end Erdos3

end

end OAI
