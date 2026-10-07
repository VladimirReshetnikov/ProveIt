import OAI.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
import OAI.Combinatorics.Progressions.Geometry.AllocatedJetChartSupport
import OAI.Combinatorics.Progressions.Geometry.AllocatedPhysicalChartBounds
import OAI.Combinatorics.Progressions.Geometry.AllocatedSupportedSiteApproximation
import OAI.Combinatorics.Progressions.Lattices.IntegerMatrixPMFSupport
import OAI.Combinatorics.Progressions.Linear.ContainedSupportedProgressionKernels
import OAI.Combinatorics.Progressions.Probability.AllocatedFrozenJetDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

universe uα

theorem exists_bounded_grid_site_expansion
    {α : Type uα} [Fintype α] [DecidableEq α]
    (rows : Finset (Finset α)) (p : PMF (rows → ℤ)) {K Kmax : ℕ}
    (hK : 0 < K) (hKmax : K ≤ Kmax) {H ε P : ℝ} (hH : 0 ≤ H)
    (hsupport : ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
      p (fun t => booleanCoefficient y t) ≠ 0 → ∀ u, |(y u : ℝ) / K| ≤ H)
    (hε : 0 < ε) (hP : 0 ≤ P) (hHP : H + 1 / 4 ≤ Real.exp P)
    (hcap : (Kmax : ℝ) ^ rows.card ≤ Real.exp P)
    (hLip : ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp (Fintype.card (Finset α) * (4 * P + 8))) 1
        (Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P))
        (⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ + 4) (H + 1 / 4) ∧
      ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((K : ℝ) ^ rows.card * (p (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
          e.integerEval K y‖ ≤ ε := by
  let F (x : Finset α → Unit → ℝ) : ℂ :=
    integerRowMassInterpolation K p (selectedBooleanSiteRows () rows x)
  have hKreal : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hKnn : (1 : ℝ≥0) ≤ K := by exact_mod_cast hK
  have hmax : (K : ℝ≥0) ≤ Kmax := by exact_mod_cast hKmax
  have hF (x) : ‖F x‖ ≤ (Kmax : ℝ≥0) ^ rows.card := by
    dsimp only [F]
    rw [Complex.norm_real, Real.norm_of_nonneg (integerRowMassInterpolation_range hKreal.le p _).1]
    apply (integerRowMassInterpolation_range hKreal.le p _).2.trans
    simpa only [Fintype.card_coe, NNReal.coe_pow, NNReal.coe_natCast] using
      pow_le_pow_left₀ hKreal.le (show (K : ℝ) ≤ Kmax by exact_mod_cast hKmax) rows.card
  have hLF : LipschitzWith
      ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
        (2 : ℝ≥0) ^ Fintype.card α) F := by
    have h := (integerRowMassInterpolation_lipschitz (K : ℝ≥0) hKnn p).comp
      (selectedBooleanSiteRows_lipschitz () rows)
    have hc : LipschitzWith
        ((rows.card * (2 * (K : ℝ≥0) ^ 2) * (K : ℝ≥0) ^ rows.card) *
          (2 : ℝ≥0) ^ Fintype.card α) F := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [F, Function.comp_def, Fintype.card_coe, dist_eq_norm,
        ← Complex.ofReal_sub, Complex.norm_real, NNReal.coe_natCast] using h.dist_le_mul x y
    apply hc.weaken
    gcongr
  obtain ⟨N, hN, c, f, hc, hf, hLf, he⟩ := exists_grouped_site_approximation F
    ((Kmax : ℝ≥0) ^ rows.card) _ hF hLF
    (show 0 < H + 1 / 4 by linarith only [hH]) hε hP hHP
    (by simpa only [NNReal.coe_pow, NNReal.coe_natCast] using hcap) hLip hεP
  let e : ScalarSiteExpansion.{uα,uα} (Finset α) :=
    { Term := Finset α × Unit → Fin N
      period := fun _ => 1
      coefficient := c
      factor := fun k u _ x => scalarSupportPlateau H x * f k u (fun _ => x) }
  refine ⟨e, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · change (Fintype.card (Finset α × Unit → Fin N) : ℝ) ≤ _
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_unit,
      mul_one, Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hN _).trans_eq (Real.exp_nat_mul _ _).symm
  · exact fun _ => zero_lt_one
  · intro k
    norm_num only [e, Nat.cast_one]
  · simpa only [Fintype.card_unit, mul_one] using hc
  · intro k u r x
    change ‖scalarSupportPlateau H x * f k u (fun _ => x)‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (scalarSupportPlateau_norm _ _) (hf k u _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro k u r
    apply scalarSupportPlateau_mul_lipschitz H (fun x => f k u (fun _ => x)) _ (fun x => hf k u _)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Fintype.card_unit, Nat.cast_one, dist_pi_const] using
      (hLf k u).dist_le_mul (fun _ => x) (fun _ => y)
  · intro k u r x hx
    change scalarSupportPlateau H x * f k u (fun _ => x) = 0
    rw [scalarSupportPlateau_zero hx, zero_mul]
  · intro y hy
    let target : ℂ := (((K : ℝ) ^ rows.card * (p (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ)
    have hkeep : target ≠ 0 → ∀ u, scalarSupportPlateau H ((y u : ℝ) / K) = 1 := by
      intro ht u
      have hp : p (fun t => booleanCoefficient y t) ≠ 0 := by
        intro hz
        apply ht
        simp only [target, hz, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
      exact scalarSupportPlateau_one hH (hsupport y hy hp u)
    apply finite_site_cutoff_error target c (fun k u => f k u (fun _ => (y u : ℝ) / K))
      (fun u => scalarSupportPlateau H ((y u : ℝ) / K)) hε.le
      (fun u => scalarSupportPlateau_norm _ _) hkeep
    intro hcut
    have herr := he (fun u _ => (y u : ℝ) / K)
      (fun u _ => (scalarSupportPlateau_support _ _ (hcut u)).le)
    have heq : F (fun u _ => (y u : ℝ) / K) = target := by
      dsimp only [F, target]
      rw [show selectedBooleanSiteRows () rows (fun u _ => (y u : ℝ) / K) =
        (fun t : rows => ((booleanCoefficient y t : ℤ) : ℝ) / K) by
          simpa only using selectedBooleanSiteRows_integer () rows (fun _ => K) (fun u _ => y u)]
      rw [integerRowMassInterpolation_grid hKreal, Fintype.card_coe]
    rwa [heq] at herr

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedLayerIntegerCoefficient_scaled_bound (j : Fin m) (hσ1 : σ j ≤ 1)
    (i : Fin (n j)) (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    (z : ℤ) (hz : z ∈ (allocatedLayerIntegerPMFs B U b hR hσ S j i e).support) :
    |(z : ℝ) / basisAxisScale (b j) i| * monomialScale (layerSamplerBox B U b S) e.val ≤ R j := by
  have hT : ∀ k, 0 < layerSamplerBox B U b S k :=
    fun k => zero_lt_one.trans_le (layerSamplerBox_one_le B U b S k)
  exact (allocatedIntegerCoefficient_bound (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (j.val + 1) (basisAxisScale (b j) i) S.value (layerTailDegree m) (Nat.zero_lt_succ _) (basisAxisScale_pos (b j) i)
    S.positive (layerSamplerBox B U b S) hT (layerSamplerBox_le B U b S) Subtype.val
    (fun d => d.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) hσ1 (S.gap j i) (S.width j)
    (layerIntegerPrincipalSlots_not_constant B j i) rfl
    (layerSamplerSides_integer_principal B U b R S.value j i) e hz).trans (by linarith [hR j])

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

theorem allocatedIntegerJet_scaled_support_bound (j : Fin m) (hσ1 : σ j ≤ 1)
    (i : Fin (n j)) (z : O j → ℤ)
    (hz : (integerMatrixImagePMF (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j))
      (allocatedLayerIntegerPMFs B U b hR hσ S j i) z).toReal ≠ 0) (r : O j) :
    |(z r : ℝ) / basisAxisScale (b j) i| ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) * R j := by
  have hT : ∀ k, 0 < layerSamplerBox B U b S k :=
    fun k => zero_lt_one.trans_le (layerSamplerBox_one_le B U b S k)
  have hroot (k) : |(root k : ℝ) / layerSamplerBox B U b S k| ≤ 1 := by
    simpa only [allocatedPhysicalRootAllowance_zero] using
      allocatedPhysicalCube_root_normalized B U b S x (principalAxisJoin grid u v) (fun _ => 0) k
  exact integerMatrixImagePMF_scaled_support_bound _ _
    (fun e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) =>
      monomialScale (layerSamplerBox B U b S) e.val)
    (fun e => monomialScale_pos _ hT e.val) (by positivity)
    (boundedCoefficientJetMatrix_scaled_entry_bound root dirs _ hT hroot
      (allocatedPhysicalCube_directions_normalized B U b S x (principalAxisJoin grid u v)) _ (rows j))
    (fun e z hz => allocatedLayerIntegerCoefficient_scaled_bound B U b hR hσ S j hσ1 i e z hz) z hz r

theorem allocatedGridJetDensity_scaled_support_bound
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (hz : allocatedGridJetDensity B U b hR hσ S x u v rows
      (fun a => coefficientJetAxisEquiv O I n z a.val) ≠ 0)
    (j : Fin m) (hσ1 : σ j ≤ 1) (i : Fin (n j)) (hgrid : grid ⟨j, Sum.inr i⟩) (r : O j) :
    |((z j).2 i r : ℝ) / basisAxisScale (b j) i| ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) * R j := by
  apply allocatedIntegerJet_scaled_support_bound B U b hR hσ S x u v rows j hσ1 i ((z j).2 i) ?_ r
  intro hzero
  apply hz
  unfold allocatedGridJetDensity
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨⟨j, Sum.inr i⟩, hgrid⟩ : {a // grid a})) hzero

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "tuples" => principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

noncomputable def allocatedWholeGridJetPMF
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)) :
    ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val)
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => integerMatrixImagePMF
      (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) (j.val + 1) (rows j))
      (allocatedLayerIntegerPMFs B U b hR hσ S j i)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
  [Fintype α] [∀ j, Fintype (O j)] in
theorem allocatedWholeGridJetPMF_toReal
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (a : {a // grid a}) (z : CoefficientJetAxisRow O a.val) :
    (allocatedWholeGridJetPMF B U b hR hσ S x rows y a z).toReal =
      allocatedGridJetFactor B U b hR hσ S x (principalAxisRestrict grid y)
        (principalAxisRestrict (fun a => ¬grid a) y) rows a z := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · simp only [allocatedWholeGridJetPMF, allocatedGridJetFactor, principalAxisJoin_restrict]
    rfl

variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

instance allocatedGridJetRow_countable
    (a : {a // allocatedGridAxis (I := I) U b S.value a}) :
    Countable (CoefficientJetAxisRow O a.val) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact inferInstanceAs (Countable (O j → ℤ))

instance allocatedGridJetRow_measurableSingleton
    (a : {a // allocatedGridAxis (I := I) U b S.value a}) :
    MeasurableSingletonClass (CoefficientJetAxisRow O a.val) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact inferInstanceAs (MeasurableSingletonClass (O j → ℤ))

noncomputable def allocatedSupportedGridJetPMF
    (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (a : {a // allocatedGridAxis (I := I) U b S.value a}) :
    PMF (CoefficientJetAxisRow O a.val) := by
  exact ((principalTupleWeights (α := α) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).condition
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).toPMF.bind
        (fun y => allocatedWholeGridJetPMF B U b hR hσ S x rows y a)

noncomputable def allocatedSupportedGridJetDensity
    (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (z : AllocatedFrozenJetRows B U b S O) : ℝ :=
  ∏ a, (allocatedSupportedGridJetPMF B U b hR hσ S x rows q r hcell a (z a)).toReal

theorem allocatedWholeGridJetPMF_joint_law :
    (FiniteProbabilityWeights.condition
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).toPMF.bind (fun y => dependentProductPMF
      (allocatedWholeGridJetPMF B U b hR hσ S x rows y)) =
      dependentProductPMF (allocatedSupportedGridJetPMF B U b hR hσ S x rows q r hcell) := by
  let k : ∀ a : {a // grid a},
      (∀ c : B a.val, ∀ v : Fin (layerSamplerDegree I n a.val),
        IntegerScalarCubeBox α (allocatedPrincipalSides B U b S ⟨a.val, c, v⟩)) →
      PMF (CoefficientJetAxisRow O a.val)
    | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
    | ⟨⟨j, .inr i⟩, _⟩ => fun y =>
        (independentProductPMF (fun c : Option (B ⟨j, Sum.inr i⟩) =>
          allocatedLayerIntegerPMFs B U b hR hσ S j i
            (principalCoefficientChoice (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ c))).map
          (fun c t => booleanCoefficient (fun _ : Finset α => c none) (rows j t) +
            ∑ b, c (some b) * integerBooleanBlockJet (fun v i => (y b v i : ℤ)) (rows j t))
  have hp (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
      (a : {a // grid a}) :
      allocatedWholeGridJetPMF B U b hR hσ S x rows y a = k a (fun c v => y ⟨a.val, c, v⟩) := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · exact allocatedPhysicalGridJetPMF_principal B U b hR hσ S j i ha x y (rows j)
  have hfun y : allocatedWholeGridJetPMF B U b hR hσ S x rows y =
      (fun a => k a (fun c v => y ⟨a.val, c, v⟩)) := funext (hp y)
  unfold allocatedSupportedGridJetPMF
  simp_rw [hfun]
  exact principalSupportedResidue_selected_kernels B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S) q r hcell
    Subtype.val Subtype.val_injective k

theorem allocatedGridJetDensity_conditional_mean (z : AllocatedFrozenJetRows B U b S O) :
    (FiniteProbabilityWeights.condition
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).mean (fun y => allocatedGridJetDensity B U b hR hσ S x
      (principalAxisRestrict grid y) (principalAxisRestrict (fun a => ¬grid a) y) rows z) =
        allocatedSupportedGridJetDensity B U b hR hσ S x rows q r hcell z := by
  have h := FiniteProbabilityWeights.mean_prod_point_mass (FiniteProbabilityWeights.condition
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell)
    (allocatedWholeGridJetPMF B U b hR hσ S x rows)
    (allocatedWholeGridJetPMF_joint_law B U b hR hσ S x rows q r hcell) (fun _ => 1) z
  simpa only [one_mul, allocatedWholeGridJetPMF_toReal, allocatedGridJetDensity,
    allocatedSupportedGridJetDensity, allocatedSupportedGridJetPMF] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j

theorem allocatedPhysicalGridPMF_base_independent
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (x x' : G → IntegerScalarCubeBox α S.value) :
    allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x =
      allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x' := by
  unfold allocatedSupportedPhysicalGridPMF
  rw [allocatedSupportedResidueJetPMF_constant_mixture B U b hR hσ S q r hcell j i hgrid rows x,
    allocatedSupportedResidueJetPMF_constant_mixture B U b hR hσ S q r hcell j i hgrid rows x']

theorem allocatedPhysicalGridPMF_scaled_support
    (hσ1 : σ j ≤ 1) (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)
    (z : rows → ℤ)
    (hmass : allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x z ≠ 0)
    (t : rows) : |(z t : ℝ) / height| ≤ radius := by
  by_contra hbad
  apply hmass
  unfold allocatedSupportedPhysicalGridPMF
  apply pmf_bind_zero_of_support
  intro y _
  by_contra hmass'
  have hreal := (ENNReal.toReal_pos hmass' (PMF.apply_ne_top _ _)).ne'
  have hT : ∀ k, 0 < layerSamplerBox B U b S k :=
    fun k => zero_lt_one.trans_le (layerSamplerBox_one_le B U b S k)
  have hroot (k) : |(allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y k : ℝ) /
      layerSamplerBox B U b S k| ≤ 1 := by
    simpa only [allocatedPhysicalRootAllowance_zero] using
      allocatedPhysicalCube_root_normalized B U b S x y (fun _ => 0) k
  apply hbad
  exact integerMatrixImagePMF_scaled_support_bound _ _
    (fun e : Slots => monomialScale (layerSamplerBox B U b S) e.val)
    (fun e => monomialScale_pos _ hT e.val) (by positivity)
    (boundedCoefficientJetMatrix_scaled_entry_bound _ _ _ hT hroot
      (allocatedPhysicalCube_directions_normalized B U b S x y) _ (fun t : rows => (t : Finset α)))
    (fun e z hz => allocatedLayerIntegerCoefficient_scaled_bound B U b hR hσ S j hσ1 i e z hz)
    z hreal t

theorem exists_allocated_bounded_grid_site_expansion
    (hσ1 : σ j ≤ 1) (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) {Kmax : ℕ} (hKmax : height ≤ Kmax)
    {ε P : ℝ} (hε : 0 < ε) (hP : 0 ≤ P)
    (hHP : rows.card * radius + 1 / 4 ≤ Real.exp P)
    (hcap : (Kmax : ℝ) ^ rows.card ≤ Real.exp P)
    (hLip : ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp (Fintype.card (Finset α) * (4 * P + 8))) 1
        (Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P))
        (⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ + 4) (rows.card * radius + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε := by
  let x₀ : G → IntegerScalarCubeBox α S.value := fun _ _ =>
    ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast S.positive⟩⟩
  let p := allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x₀
  have hrad : 0 ≤ radius := by
    have := (hR j).le
    positivity
  have hk : (0 : ℝ) < height := Nat.cast_pos.mpr (basisAxisScale_pos (b j) i)
  have hs : ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
      p (fun t => booleanCoefficient y t) ≠ 0 → ∀ u, |(y u : ℝ) / height| ≤ rows.card * radius := by
    intro y hy hm u
    apply integer_boolean_sites_bound y rows hy hrad hk _ u
    intro t ht
    have hb := allocatedPhysicalGridPMF_scaled_support B U b hR hσ S q r hcell j i hσ1 rows x₀
      (fun t => booleanCoefficient y t) hm ⟨t, ht⟩
    rw [abs_div, abs_of_pos hk] at hb
    exact (div_le_iff₀ hk).mp hb
  obtain ⟨e, he, herr⟩ := exists_bounded_grid_site_expansion rows p
    (basisAxisScale_pos (b j) i) hKmax (mul_nonneg (Nat.cast_nonneg _) hrad)
    hs hε hP hHP hcap hLip hεP
  refine ⟨e, he, ?_⟩
  intro x y hy
  rw [allocatedPhysicalGridPMF_base_independent B U b hR hσ S q r hcell j i hgrid rows x x₀]
  exact herr y hy

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [DecidableEq α] in
theorem allocatedGridSide_normalizable_or_bounded (hq : 0 < q)
    (hsize : (Fintype.card α + 1) * q ≤ S.value) :
    let γ := principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card
    (2 * inactiveDenominator γ ≤ height ∧
      ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin degree),
        (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩) ∨
    height ≤ max (2 * inactiveDenominator γ) (integerAxisShortBound degree ((Fintype.card α + 1) * q) γ) := by
  dsimp only
  let γ := principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card
  rcases integerAxisSideLength_long_or_bounded (K := height) (γ := γ)
    (Nat.zero_lt_succ _) (Nat.mul_pos (Nat.succ_pos _) hq) hsize with hs | hb
  · by_cases hl : 2 * inactiveDenominator γ ≤ height
    · refine Or.inl ⟨hl, ?_⟩
      intro a v
      change (Fintype.card α + 1) * q ≤ integerAxisSideLength degree height S.value
        (principalProfileSize (R j) (Fintype.card (B ⟨j, Sum.inr i⟩)))
      simpa only [γ, layerIntegerPrincipalSlots_card] using hs
    · exact Or.inr ((Nat.le_of_not_ge hl).trans (le_max_left _ _))
  · exact Or.inr (hb.trans (le_max_right _ _))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

theorem allocatedSupportedGridJetPMF_scaled_support_bound
    (j : Fin m) (hσ1 : σ j ≤ 1) (i : Fin (n j))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (z : O j → ℤ)
    (hz : (allocatedSupportedGridJetPMF B U b hR hσ S x rows q r hcell
      ⟨⟨j, Sum.inr i⟩, hgrid⟩ z).toReal ≠ 0) (t : O j) :
    |(z t : ℝ) / basisAxisScale (b j) i| ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) * R j := by
  by_contra hlarge
  apply hz
  have hzero : allocatedSupportedGridJetPMF B U b hR hσ S x rows q r hcell
      ⟨⟨j, Sum.inr i⟩, hgrid⟩ z = 0 := by
    unfold allocatedSupportedGridJetPMF
    apply pmf_bind_zero_of_support
    intro y _
    have hreal : (allocatedWholeGridJetPMF B U b hR hσ S x rows y
        ⟨⟨j, Sum.inr i⟩, hgrid⟩ z).toReal = 0 := by
      by_contra hn
      apply hlarge
      have h := allocatedIntegerJet_scaled_support_bound B U b hR hσ S x
        (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y)
        (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y)
        rows j hσ1 i z
      simp only [principalAxisJoin_restrict] at h
      exact h hn t
    exact ((ENNReal.toReal_eq_zero_iff _).mp hreal).resolve_right (PMF.apply_ne_top _ _)
  rw [hzero, ENNReal.toReal_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) *
    (8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1))
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedPhysicalGridPMF_natural_support
    (hσ1 : σ j ≤ 1) (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)
    (z : rows → ℤ)
    (hmass : allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x z ≠ 0)
    (t : rows) : |(z t : ℝ) / scale| ≤ radius := by
  have hk : (0 : ℝ) < height := Nat.cast_pos.mpr (basisAxisScale_pos (b j) i)
  have hn : (0 : ℝ) < scale := Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)
  have ho := allocatedPhysicalGridPMF_scaled_support B U b hR hσ S q r hcell j i hσ1 rows x z hmass t
  rw [abs_div, abs_of_pos hk] at ho
  rw [abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ((Fintype.card Slots : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j) * height :=
      (div_le_iff₀ hk).mp ho
    _ = radius * (gamma * height) := by
      unfold principalProfileSize
      have hp : (0 : ℝ) < (layerIntegerPrincipalSlots (G := G) B j i).card + 1 := by positivity
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by positivity)

theorem exists_allocated_natural_bounded_grid_site_expansion
    (hσ1 : σ j ≤ 1) (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) {Kmax : ℕ} (hKmax : scale ≤ Kmax)
    {ε P : ℝ} (hε : 0 < ε) (hP : 0 ≤ P)
    (hHP : rows.card * radius + 1 / 4 ≤ Real.exp P)
    (hcap : (Kmax : ℝ) ^ rows.card ≤ Real.exp P)
    (hLip : ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp (Fintype.card (Finset α) * (4 * P + 8))) 1
        (Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P))
        (⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ + 4) (rows.card * radius + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((scale : ℝ) ^ rows.card *
          (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval scale y‖ ≤ ε := by
  let x₀ : G → IntegerScalarCubeBox α S.value := fun _ _ =>
    ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast S.positive⟩⟩
  let p := allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x₀
  have hrad : 0 ≤ radius := by
    have := (hR j).le
    positivity
  have hk : (0 : ℝ) < scale := Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)
  have hs : ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
      p (fun t => booleanCoefficient y t) ≠ 0 → ∀ u, |(y u : ℝ) / scale| ≤ rows.card * radius := by
    intro y hy hm u
    apply integer_boolean_sites_bound y rows hy hrad hk _ u
    intro t ht
    have hb := allocatedPhysicalGridPMF_natural_support B U b hR hσ S q r hcell j i hσ1 rows x₀
      (fun t => booleanCoefficient y t) hm ⟨t, ht⟩
    rw [abs_div, abs_of_pos hk] at hb
    exact (div_le_iff₀ hk).mp hb
  obtain ⟨e, he, herr⟩ := exists_bounded_grid_site_expansion rows p
    (allocatedPrincipalGridScale_pos_of_radius B U b hR j i) hKmax (mul_nonneg (Nat.cast_nonneg _) hrad)
    hs hε hP hHP hcap hLip hεP
  refine ⟨e, he, ?_⟩
  intro x y hy
  rw [allocatedPhysicalGridPMF_base_independent B U b hR hσ S q r hcell j i hgrid rows x x₀]
  exact herr y hy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => j.val + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) *
    (8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1))
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "constantLaw" => allocatedLayerIntegerPMFs B U b hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

theorem forecastInactive_fixed_mem_physical_support
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)
    (c : ℤ) (hc : constantLaw c ≠ 0) (z : rows → ℤ)
    (hz : allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows
      (fun t => booleanCoefficient (fun _ : Finset α => c) t) z ≠ 0) :
    allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x z ≠ 0 := by
  unfold allocatedSupportedPhysicalGridPMF
  rw [allocatedSupportedResidueJetPMF_constant_mixture B U b hR hσ S q r hcell j i hgrid rows x]
  apply (PMF.mem_support_iff _ _).mp
  apply (PMF.mem_support_bind_iff _ _ z).mpr
  exact ⟨c, (PMF.mem_support_iff _ _).mpr hc, (PMF.mem_support_iff _ _).mpr hz⟩

theorem forecastInactive_fixed_natural_support
    (hσ1 : σ j ≤ 1) (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (c : ℤ) (hc : constantLaw c ≠ 0) (z : rows → ℤ)
    (hz : allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows
      (fun t => booleanCoefficient (fun _ : Finset α => c) t) z ≠ 0)
    (t : rows) : |(z t : ℝ) / scale| ≤ radius := by
  let x₀ : G → IntegerScalarCubeBox α S.value := fun _ _ =>
    ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast S.positive⟩⟩
  exact allocatedPhysicalGridPMF_natural_support B U b hR hσ S q r hcell j i hσ1 rows x₀ z
    (forecastInactive_fixed_mem_physical_support B U b hR hσ S q r hcell j i
      hgrid rows x₀ c hc z hz) t

theorem exists_forecastInactive_fixed_bounded_site_expansion
    (hσ1 : σ j ≤ 1) (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (c : ℤ) (hc : constantLaw c ≠ 0)
    (rows : Finset (Finset α)) {Kmax : ℕ} (hKmax : scale ≤ Kmax)
    {ε P : ℝ} (hε : 0 < ε) (hP : 0 ≤ P)
    (hHP : rows.card * radius + 1 / 4 ≤ Real.exp P)
    (hcap : (Kmax : ℝ) ^ rows.card ≤ Real.exp P)
    (hLip : ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp (Fintype.card (Finset α) * (4 * P + 8))) 1
        (Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P))
        (⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ + 4) (rows.card * radius + 1 / 4) ∧
      ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((scale : ℝ) ^ rows.card *
          (allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows
            (fun t => booleanCoefficient (fun _ : Finset α => c) t)
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval scale y‖ ≤ ε := by
  let p := allocatedSupportedResidueJetPMF B U b hR hσ S q r hcell j i rows
    (fun t => booleanCoefficient (fun _ : Finset α => c) t)
  have hrad : 0 ≤ radius := by positivity
  have hk : (0 : ℝ) < scale :=
    Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)
  have hs : ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
      p (fun t => booleanCoefficient y t) ≠ 0 → ∀ u, |(y u : ℝ) / scale| ≤ rows.card * radius := by
    intro y hy hm u
    apply integer_boolean_sites_bound y rows hy hrad hk _ u
    intro t ht
    have hb := forecastInactive_fixed_natural_support B U b hR hσ S q r hcell j i hσ1 hgrid
      rows c hc (fun t => booleanCoefficient y t) hm ⟨t, ht⟩
    rw [abs_div, abs_of_pos hk] at hb
    exact (div_le_iff₀ hk).mp hb
  exact exists_bounded_grid_site_expansion rows p
    (allocatedPrincipalGridScale_pos_of_radius B U b hR j i) hKmax (mul_nonneg (Nat.cast_nonneg _) hrad)
    hs hε hP hHP hcap hLip hεP

end Erdos3.VectorPolynomial

end

end OAI
