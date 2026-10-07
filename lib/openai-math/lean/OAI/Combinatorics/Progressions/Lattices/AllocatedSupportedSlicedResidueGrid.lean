import OAI.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidueJet
import OAI.Combinatorics.Progressions.Probability.ContainedProgressionJetSourceLaw
import OAI.Combinatorics.Progressions.Sampling.DenseSliceGridScale

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem positiveAffineModerate_grid_approximation_on_cover
    {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (hs : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hv : ∀ b j i, 0 < v b j i)
    (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ b z, (c b).source.weight z ≠ 0 → ((c b).length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlen : ∀ b j, L ≤ (s b j).length)
    (K M t : ℕ) [NeZero M]
    (hscale : ∀ b, (M : ℝ) / (((c b).length : ℝ) * ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t) :
    let F := positiveModerateSpectrumCover J M n U V L
      (positiveModerateRetainedBias n J.card t U V W ε);
      (F.card : ℝ) ≤ positiveModerateSpectrumCardBudget n J.card t U V W ε ∧
      ∀ shift z : J → ℤ,
        ‖(integerGridDensity (weightedModerateIntegerProductSource c s)
            (weightedAffineModerateIntegerJetSum c s u v J (fun _ => 0) shift) K M z : ℂ) -
          weightedAffineModerateGridApproximation c s u v K M J (fun _ => 0) shift z F‖ ≤
            ((K : ℝ) / M) ^ J.card * ε := by
  intro F
  obtain ⟨hζ, hζ1, hacc⟩ := positiveModerateRetainedBias_spec n J.card t (V := V) hU hW hε hε1
  have htail := weightedPositiveAffineModerate_uniform_spectrum_tail c s A hA hU hc hs
    (fun b j i => (u b j i : ℝ)) v hv hstride hpositive hV hW hL hζ hζ1 hε.le hlen
    (Nat.pos_of_ne_zero (NeZero.ne M)) hscale J hJ hB hsize hacc
  refine ⟨?_, fun shift z => ?_⟩
  · simpa only [Fintype.card_coe] using
      positiveModerateSpectrumCover_card_budget J M n t hU hV hW hL hε hε1
        (by simpa only [Fintype.card_coe] using hsize)
  · exact weightedAffineModerateGridDensity_error_of_tail c s u v K M J (fun _ => 0) F
      (by simpa only [Int.cast_zero] using htail) shift z

theorem positiveAffineModerate_grid_approximation
    {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (hs : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hv : ∀ b j i, 0 < v b j i)
    (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ b z, (c b).source.weight z ≠ 0 → ((c b).length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlen : ∀ b j, L ≤ (s b j).length)
    (K M t : ℕ) [NeZero M]
    (hscale : ∀ b, (M : ℝ) / (((c b).length : ℝ) * ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t) :
    ∃ F : Finset (J → Fin M),
      (F.card : ℝ) ≤ positiveModerateSpectrumCardBudget n J.card t U V W ε ∧
      ∀ shift z : J → ℤ,
        ‖(integerGridDensity (weightedModerateIntegerProductSource c s)
            (weightedAffineModerateIntegerJetSum c s u v J (fun _ => 0) shift) K M z : ℂ) -
          weightedAffineModerateGridApproximation c s u v K M J (fun _ => 0) shift z F‖ ≤
            ((K : ℝ) / M) ^ J.card * ε := by
  let ζ := positiveModerateRetainedBias n J.card t U V W ε
  let F := positiveModerateSpectrumCover J M n U V L ζ
  obtain ⟨hζ, hζ1, hacc⟩ := positiveModerateRetainedBias_spec n J.card t (V := V) hU hW hε hε1
  have htail := weightedPositiveAffineModerate_uniform_spectrum_tail c s A hA hU hc hs
    (fun b j i => (u b j i : ℝ)) v hv hstride hpositive hV hW hL hζ hζ1 hε.le hlen
    (Nat.pos_of_ne_zero (NeZero.ne M)) hscale J hJ hB hsize hacc
  refine ⟨F, ?_, fun shift z => ?_⟩
  · simpa only [Fintype.card_coe] using
      positiveModerateSpectrumCover_card_budget J M n t hU hV hW hL hε hε1
        (by simpa only [Fintype.card_coe] using hsize)
  · exact weightedAffineModerateGridDensity_error_of_tail c s u v K M J (fun _ => 0) F
      (by simpa only [Int.cast_zero] using htail) shift z

end Erdos3

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
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ H t)
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedProgressionResidueLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q hq r hsize

noncomputable def allocatedSlicedResidueJetPMF
    (rows : Finset (Finset α)) (shift : rows → ℤ) : PMF (rows → ℤ) :=
  (dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
    allocatedLayerIntegerPMFs B U basis hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))).bind
    (fun coeff => (conditioned).toPMF.map (fun y =>
      shift + ∑ b, fun t : rows => coeff b *
        integerBooleanBlockJet (fun v k => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ k : ℤ)) t))

theorem allocatedSlicedResidueJetPMF_source
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    let sources := principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
      ⟨j, Sum.inr i⟩ (fun b v => hsize ⟨⟨j,Sum.inr i⟩,b,v⟩)
    let coeff := fun _ : B ⟨j,Sum.inr i⟩ => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
    let lower := fun (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (a : Option α) =>
      if a = none then c ⟨⟨j,Sum.inr i⟩,b,v⟩ else 0
    let strides := fun (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (_ : Option α) =>
      step ⟨⟨j,Sum.inr i⟩,b,v⟩
    (weightedModerateIntegerProductSource coeff sources).toPMF.map
      (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift) =
      allocatedSlicedResidueJetPMF B U basis hR hσ S q hq r H step c hH hsubset hsize j i rows shift := by
  intro sources coeff lower strides
  have hp := containedProgressionResidueLaw_jet_sum_law B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S)
    hH hsubset q hq r hsize ⟨j,Sum.inr i⟩ coeff rows (fun _ => 0) shift
  dsimp only at hp
  have hc := congrArg (fun p : B ⟨j,Sum.inr i⟩ → PMF ℤ => dependentProductPMF p)
    (funext (fun b => allocatedPrincipalNormalizedSource_law B U basis hR hσ S j i hactive b))
  rw [hc] at hp
  simp only [zero_add] at hp
  convert hp using 1 <;> rfl

theorem allocatedSlicedResidueJetPMF_constant_mixture
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value) :
    (conditioned).toPMF.bind (fun y =>
      integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
        (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)) =
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientChoice (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ none)).bind
        (fun z => allocatedSlicedResidueJetPMF B U basis hR hσ S q hq r H step c hH hsubset hsize j i rows
          (fun t => booleanCoefficient (fun _ : Finset α => z) t)) := by
  let p := (conditioned).toPMF
  let a := dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
    allocatedLayerIntegerPMFs B U basis hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))
  let constLaw := allocatedLayerIntegerPMFs B U basis hR hσ S j i
    (principalCoefficientChoice (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ none)
  let f (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
      (z : ℤ) (coeff : B ⟨j, Sum.inr i⟩ → ℤ) : rows → ℤ :=
    (fun t : rows => booleanCoefficient (fun _ : Finset α => z) t) +
      ∑ b, fun t : rows => coeff b * integerBooleanBlockJet
        (fun v k => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ k : ℤ)) t
  have hpoint y : integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
        (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
      constLaw.bind (fun z => a.map (f y z)) := by
    rw [allocatedPhysicalGridJetPMF_principal B U basis hR hσ S j i hgrid,
      independentProductPMF_option, PMF.map_bind]
    simp only [PMF.map_comp]
    apply congrArg (fun k : ℤ → PMF (rows → ℤ) => constLaw.bind k)
    funext z
    apply congrArg (fun g : (B ⟨j, Sum.inr i⟩ → ℤ) → rows → ℤ => a.map g)
    funext coeff t
    simp only [Function.comp_apply, f, Pi.add_apply, Finset.sum_apply,
      Option.elim_none, Option.elim_some]
  simp_rw [hpoint]
  change p.bind (fun y => constLaw.bind (fun z => a.map (f y z))) =
    constLaw.bind (fun z => a.bind (fun coeff => p.map (fun y => f y z coeff)))
  refine (PMF.bind_comm p constLaw (fun y z => a.map (f y z))).trans ?_
  apply congrArg (fun k : ℤ → PMF (rows → ℤ) => constLaw.bind k)
  funext z
  exact PMF.bind_comm p a (fun y coeff => PMF.pure (f y z coeff))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ H t)
variable (j : Fin m) (i : Fin (n j))

noncomputable def allocatedSlicedGridDensity (M : ℕ) (rows : Finset (Finset α))
    (shift z : rows → ℤ) : ℝ :=
  (basisAxisScale (basis j) i : ℝ) ^ rows.card *
    (((allocatedSlicedResidueJetPMF B U basis hR hσ S q hq r H step c hH hsubset hsize j i rows shift).map
      (integerGridResidue M)) (integerGridResidue M z)).toReal

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "coeff" => (fun _ : B (Sigma.mk j (Sum.inr i)) =>
  allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) (fun b v => hsize (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedSlicedGridDensity_approximation
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {C ε : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := (C / (2 * gamma)) / δ ^ (j.val + 1)
    let t := (layerTailDegree m + 1) * rows.card
    let W := C ^ rows.card / δ ^ t
    ∃ F : Finset (rows → Fin M),
      (F.card : ℝ) ≤ positiveModerateSpectrumCardBudget j.val rows.card t P V W ε ∧
      ∀ shift z : rows → ℤ,
        ‖(allocatedSlicedGridDensity B U basis hR hσ S q hq r H step c hH hsubset hsize j i M rows shift z : ℂ) -
          weightedAffineModerateGridApproximation coeff sources lower strides
            (basisAxisScale (basis j) i) M rows (fun _ => 0) shift z F‖ ≤
          ((basisAxisScale (basis j) i : ℝ) / M) ^ rows.card * ε := by
  intro V t W
  have hc := (allocatedPrincipalNormalizedSource_primitive B U basis hR S j i hactive A).mono hcP
  have hs (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) :=
    (principalSupportedAxisSources_primitive B (layerSamplerDegree I n) H hH q hq r
      ⟨j,Sum.inr i⟩ (fun b v => hsize ⟨⟨j,Sum.inr i⟩,b,v⟩) b v A).mono hsP
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hscale (b : B ⟨j,Sum.inr i⟩) :
      (M : ℝ) / (((coeff b).length : ℝ) * ∏ v, (((sources) b v).length : ℝ)) ≤ V := by
    exact dense_slice_product_ratio (fun v => (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) hδ
      (Nat.cast_pos.mpr S.positive) (Nat.cast_pos.mpr (coeff b).length_pos) (Nat.cast_nonneg M)
      (hlength b) (allocatedPrincipalNormalizedSource_grid_ratio B U basis hR S j i hactive hC hMK)
  have hcard : (M : ℝ) ^ rows.card ≤ W * (δ * S.value) ^ t :=
    dense_slice_grid_cardinality rows.card t hδ
      (allocatedGrid_modulus_cardinality B U basis S j i hgrid hC hMK rows.card)
  obtain ⟨F, hF, he⟩ := positiveAffineModerate_grid_approximation coeff sources lower strides A hA
    hc.one_le (fun _ => hc) hs (fun b v _ => hstep b v) (fun b v _ => hstride b v)
    (fun _ z hz => allocatedPrincipalNormalizedSource_positive_support B U basis hR S j i hactive z hz)
    hV hW (mul_pos hδ (Nat.cast_pos.mpr S.positive)).le hε hε1 hlength
    (basisAxisScale (basis j) i) M t hscale rows hrows hB hcard
  refine ⟨F,hF,fun shift z => ?_⟩
  have hlaw := allocatedSlicedResidueJetPMF_source B U basis hR hσ S q hq r H step c hH hsubset hsize
    j i hactive rows shift
  have hd := integerGridDensity_eq_of_pmf_image (weightedModerateIntegerProductSource coeff sources)
    (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift)
    _ hlaw (basisAxisScale (basis j) i) M z
  have hd' : integerGridDensity (weightedModerateIntegerProductSource coeff sources)
      (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift)
      (basisAxisScale (basis j) i) M z =
        allocatedSlicedGridDensity B U basis hR hσ S q hq r H step c hH hsubset hsize j i M rows shift z := by
    simpa only [allocatedSlicedGridDensity, Fintype.card_coe] using hd
  rw [← hd']
  exact he shift z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

noncomputable def allocatedSupportedSlicedGridDensity (M : ℕ) (rows : Finset (Finset α))
    (shift z : rows → ℤ) : ℝ :=
  (basisAxisScale (basis j) i : ℝ) ^ rows.card *
    (((allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift).map
      (integerGridResidue M)) (integerGridResidue M z)).toReal

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "coeff" => (fun _ : B (Sigma.mk j (Sum.inr i)) =>
  allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedSupportedSlicedGridDensity_approximation_on_cover
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {C ε : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := (C / (2 * gamma)) / δ ^ (j.val + 1)
    let t := (layerTailDegree m + 1) * rows.card
    let W := C ^ rows.card / δ ^ t
    let F := positiveModerateSpectrumCover rows M j.val P V (δ * S.value)
      (positiveModerateRetainedBias j.val rows.card t P V W ε);
      (F.card : ℝ) ≤ positiveModerateSpectrumCardBudget j.val rows.card t P V W ε ∧
      ∀ shift z : rows → ℤ,
        ‖(allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z : ℂ) -
          weightedAffineModerateGridApproximation coeff sources lower strides
            (basisAxisScale (basis j) i) M rows (fun _ => 0) shift z F‖ ≤
          ((basisAxisScale (basis j) i : ℝ) / M) ^ rows.card * ε := by
  intro V t W F
  have hc := (allocatedPrincipalNormalizedSource_primitive B U basis hR S j i hactive A).mono hcP
  have hs (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) :=
    (principalSupportedAxisSources_primitive B (layerSamplerDegree I n) H hH q hq r
      ⟨j,Sum.inr i⟩ hsize b v A).mono hsP
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hscale (b : B ⟨j,Sum.inr i⟩) :
      (M : ℝ) / (((coeff b).length : ℝ) * ∏ v, (((sources) b v).length : ℝ)) ≤ V := by
    exact dense_slice_product_ratio (fun v => (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) hδ
      (Nat.cast_pos.mpr S.positive) (Nat.cast_pos.mpr (coeff b).length_pos) (Nat.cast_nonneg M)
      (hlength b) (allocatedPrincipalNormalizedSource_grid_ratio B U basis hR S j i hactive hC hMK)
  have hcard : (M : ℝ) ^ rows.card ≤ W * (δ * S.value) ^ t :=
    dense_slice_grid_cardinality rows.card t hδ
      (allocatedGrid_modulus_cardinality B U basis S j i hgrid hC hMK rows.card)
  obtain ⟨hF, he⟩ := positiveAffineModerate_grid_approximation_on_cover coeff sources lower strides A hA
    hc.one_le (fun _ => hc) hs (fun b v _ => hstep b v) (fun b v _ => hstride b v)
    (fun _ z hz => allocatedPrincipalNormalizedSource_positive_support B U basis hR S j i hactive z hz)
    hV hW (mul_pos hδ (Nat.cast_pos.mpr S.positive)).le hε hε1 hlength
    (basisAxisScale (basis j) i) M t hscale rows hrows hB hcard
  refine ⟨hF,fun shift z => ?_⟩
  have hlaw := allocatedSupportedSlicedResidueJetPMF_source B U basis hR hσ S q hq r H step c hH hsubset hcell
    j i hactive hsize rows shift
  have hd := integerGridDensity_eq_of_pmf_image (weightedModerateIntegerProductSource coeff sources)
    (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift)
    _ hlaw (basisAxisScale (basis j) i) M z
  have hd' : integerGridDensity (weightedModerateIntegerProductSource coeff sources)
      (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift)
      (basisAxisScale (basis j) i) M z =
        allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z := by
    simpa only [allocatedSupportedSlicedGridDensity, Fintype.card_coe] using hd
  rw [← hd']
  exact he shift z

theorem allocatedSupportedSlicedGridDensity_approximation
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {C ε : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := (C / (2 * gamma)) / δ ^ (j.val + 1)
    let t := (layerTailDegree m + 1) * rows.card
    let W := C ^ rows.card / δ ^ t
    ∃ F : Finset (rows → Fin M),
      (F.card : ℝ) ≤ positiveModerateSpectrumCardBudget j.val rows.card t P V W ε ∧
      ∀ shift z : rows → ℤ,
        ‖(allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z : ℂ) -
          weightedAffineModerateGridApproximation coeff sources lower strides
            (basisAxisScale (basis j) i) M rows (fun _ => 0) shift z F‖ ≤
          ((basisAxisScale (basis j) i : ℝ) / M) ^ rows.card * ε := by
  intro V t W
  have hc := (allocatedPrincipalNormalizedSource_primitive B U basis hR S j i hactive A).mono hcP
  have hs (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) :=
    (principalSupportedAxisSources_primitive B (layerSamplerDegree I n) H hH q hq r
      ⟨j,Sum.inr i⟩ hsize b v A).mono hsP
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hscale (b : B ⟨j,Sum.inr i⟩) :
      (M : ℝ) / (((coeff b).length : ℝ) * ∏ v, (((sources) b v).length : ℝ)) ≤ V := by
    exact dense_slice_product_ratio (fun v => (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) hδ
      (Nat.cast_pos.mpr S.positive) (Nat.cast_pos.mpr (coeff b).length_pos) (Nat.cast_nonneg M)
      (hlength b) (allocatedPrincipalNormalizedSource_grid_ratio B U basis hR S j i hactive hC hMK)
  have hcard : (M : ℝ) ^ rows.card ≤ W * (δ * S.value) ^ t :=
    dense_slice_grid_cardinality rows.card t hδ
      (allocatedGrid_modulus_cardinality B U basis S j i hgrid hC hMK rows.card)
  obtain ⟨F, hF, he⟩ := positiveAffineModerate_grid_approximation coeff sources lower strides A hA
    hc.one_le (fun _ => hc) hs (fun b v _ => hstep b v) (fun b v _ => hstride b v)
    (fun _ z hz => allocatedPrincipalNormalizedSource_positive_support B U basis hR S j i hactive z hz)
    hV hW (mul_pos hδ (Nat.cast_pos.mpr S.positive)).le hε hε1 hlength
    (basisAxisScale (basis j) i) M t hscale rows hrows hB hcard
  refine ⟨F,hF,fun shift z => ?_⟩
  have hlaw := allocatedSupportedSlicedResidueJetPMF_source B U basis hR hσ S q hq r H step c hH hsubset hcell
    j i hactive hsize rows shift
  have hd := integerGridDensity_eq_of_pmf_image (weightedModerateIntegerProductSource coeff sources)
    (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift)
    _ hlaw (basisAxisScale (basis j) i) M z
  have hd' : integerGridDensity (weightedModerateIntegerProductSource coeff sources)
      (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift)
      (basisAxisScale (basis j) i) M z =
        allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z := by
    simpa only [allocatedSupportedSlicedGridDensity, Fintype.card_coe] using hd
  rw [← hd']
  exact he shift z

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedSupportedSlicedGridDensity_absolute_cap
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {C : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    :
    let V := (C / (2 * gamma)) / δ ^ (j.val + 1)
    let t := (layerTailDegree m + 1) * rows.card
    let W := C ^ rows.card / δ ^ t
    (∑ k, ‖∏ b, weightedAffineModerateGridCoefficient (coeff b) (sources b)
      (fun v a => (lower b v a : ℝ)) (strides b) 0 M rows k‖) ≤
        positiveModerateSpectrumCardBudget j.val rows.card t P V W 1 + 1 := by
  intro V t W
  have hc := (allocatedPrincipalNormalizedSource_primitive B U basis hR S j i hactive A).mono hcP
  have hs (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) :=
    (principalSupportedAxisSources_primitive B (layerSamplerDegree I n) H hH q hq r
      ⟨j,Sum.inr i⟩ hsize b v A).mono hsP
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hscale (b : B ⟨j,Sum.inr i⟩) :
      (M : ℝ) / (((coeff b).length : ℝ) * ∏ v, (((sources) b v).length : ℝ)) ≤ V := by
    exact dense_slice_product_ratio (fun v => (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) hδ
      (Nat.cast_pos.mpr S.positive) (Nat.cast_pos.mpr (coeff b).length_pos) (Nat.cast_nonneg M)
      (hlength b) (allocatedPrincipalNormalizedSource_grid_ratio B U basis hR S j i hactive hC hMK)
  have hcard : (M : ℝ) ^ rows.card ≤ W * (δ * S.value) ^ t :=
    dense_slice_grid_cardinality rows.card t hδ
      (allocatedGrid_modulus_cardinality B U basis S j i hgrid hC hMK rows.card)
  exact weightedPositiveAffineModerateSpectrum_absolute_cap coeff sources A hA hc.one_le
    (fun _ => hc) hs (fun b v a => (lower b v a : ℝ)) strides
    (fun b v _ => hstep b v) (fun b v _ => hstride b v)
    (fun _ z hz => allocatedPrincipalNormalizedSource_positive_support B U basis hR S j i hactive z hz)
    hV hW (mul_pos hδ (Nat.cast_pos.mpr S.positive)).le hlength
    (Nat.pos_of_ne_zero (NeZero.ne M)) hscale rows hrows hB hcard

end Erdos3.VectorPolynomial

end

end OAI
