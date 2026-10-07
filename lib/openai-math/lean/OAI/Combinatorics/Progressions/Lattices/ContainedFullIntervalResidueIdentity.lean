import OAI.Combinatorics.Progressions.Probability.ContainedSupportedProgressionJetLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (modulus : ℕ) (hm : 0 < modulus)
variable (r : PrincipalTupleIndex B h → Option α → ZMod modulus)
variable (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)

local notation "weights" => principalResidueWeights B h H hH modulus hm r hsize
local notation "tupleMap" => containedProgressionTupleMap B h L H step c hL hsubset

theorem principalResidueWeights_cube_support
    (v : PrincipalIntegerTuples B h α H) (hv : (weights).weight v ≠ 0)
    (j : PrincipalTupleIndex B h) : IntegerScalarCube (H j) (fun i => (v j i : ℤ)) := by
  apply scalarCubeResidueWeights_cube_support α (H j) modulus (hH j)
    (fun _ => modulus) (r j) (fun _ => hm) (fun _ => le_rfl) (hsize j)
  exact FiniteProbabilityWeights.pi_weight_pos_component _ v
    (lt_of_le_of_ne ((weights).nonneg v) (Ne.symm hv)) j

noncomputable def containedProgressionResidueLaw :
    FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) := (weights).fiberLaw tupleMap

theorem containedProgressionResidueLaw_mean (f : (JointBlockParameter B h α → ℝ) → ℝ) :
    (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).mean
        (fun v => f (principalTupleNormalized L v)) =
      (weights).mean (fun v => f (principalTupleFlatten B h α
        (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j))) := by
  exact containedProgressionTupleLaw_mean B h L H step c hL hsubset weights
    (principalResidueWeights_cube_support B h H hH modulus hm r hsize) f

theorem containedProgressionResidueLaw_support
    (v : PrincipalIntegerTuples B h α L)
    (hv : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v ≠ 0) :
    ∀ j i, ((v j i : ℤ) : ZMod modulus) =
      (if i = none then (c j : ZMod modulus) else 0) + (step j : ZMod modulus) * r j i := by
  apply (weights).fiberLaw_support tupleMap
    (fun v => ∀ j i, ((v j i : ℤ) : ZMod modulus) =
      (if i = none then (c j : ZMod modulus) else 0) + (step j : ZMod modulus) * r j i) _ v hv
  intro z hz j i
  have hc := principalResidueWeights_cube_support B h H hH modulus hm r hsize z hz j
  have hr := scalarCubeResiduePi_support H (fun _ => modulus) hH
    (fun _ _ => modulus) r (fun _ _ => hm) (fun _ _ => le_rfl) hsize z hz j i
  change ((containedProgressionCubeMap α (L j) (H j) (step j) (c j) (hL j) (hsubset j) (z j) i : ℤ) : ZMod modulus) = _
  rw [containedProgressionCubeMap_value _ _ _ _ _ _ _ _ hc]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, apply_ite, Int.cast_zero, hr]

theorem containedProgressionResidueLaw_matrix {Z K I N : Type*}
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (z : Z → ℤ) (rows : I → Finset α)
    (v v₀ : PrincipalIntegerTuples B h α L)
    (hv : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v ≠ 0)
    (hv₀ : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v₀ ≠ 0) :
    integerResidueMatrix (integerMappedJetMatrix e input z rows (principalTupleIntegers v)) modulus =
      integerResidueMatrix (integerMappedJetMatrix e input z rows (principalTupleIntegers v₀)) modulus := by
  apply integerMappedJetMatrix_residue
  funext a
  change ((v ⟨a.1,a.2.1,a.2.2.1⟩ a.2.2.2 : ℤ) : ZMod modulus) =
    ((v₀ ⟨a.1,a.2.1,a.2.2.1⟩ a.2.2.2 : ℤ) : ZMod modulus)
  rw [containedProgressionResidueLaw_support B h L H step c hL hH hsubset modulus hm r hsize v hv,
    containedProgressionResidueLaw_support B h L H step c hL hH hsubset modulus hm r hsize v₀ hv₀]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem containedProgressionResidueLaw_label_eq
    {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
    (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (modulus : ℕ) (hm : 0 < modulus)
    (r : PrincipalTupleIndex B h → Option α → ZMod modulus)
    (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
    (v v₀ : PrincipalIntegerTuples B h α L)
    (hv : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v ≠ 0)
    (hv₀ : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v₀ ≠ 0) :
    principalResidueLabel modulus v = principalResidueLabel modulus v₀ := by
  funext j i
  exact (containedProgressionResidueLaw_support B h L H step c hL hH hsubset modulus hm r hsize v hv j i).trans
    (containedProgressionResidueLaw_support B h L H step c hL hH hsubset modulus hm r hsize v₀ hv₀ j i).symm

end Erdos3

end

section

namespace Erdos3

open scoped Classical NNReal

theorem FiniteProbabilityWeights.toPMF_injective {X : Type*} [Fintype X] :
    Function.Injective (fun p : FiniteProbabilityWeights X => p.toPMF) := by
  intro p q hpq
  change p.toPMF = q.toPMF at hpq
  have hw : p.weight = q.weight := by
    funext x
    exact (FiniteProbabilityWeights.toPMF_toReal p x).symm.trans
      ((congrArg (fun μ : PMF X => (μ x).toReal) hpq).trans
        (FiniteProbabilityWeights.toPMF_toReal q x))
  cases p
  cases q
  cases hw
  rfl

variable {D α : Type*} [Fintype α] [DecidableEq α]
variable (B : D → Type*) (h : D → ℕ)
variable (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ L t)

noncomputable def principalResidueNormalizedSource (t : PrincipalTupleIndex B h) :
    NormalizedScalarCubeSource α :=
  normalizedUniformCubeSource α (L t) q (hL t) (fun _ => q) (r t)
    (fun _ => hq) (fun _ => le_rfl) (hsize t)

local notation "sources" => principalResidueNormalizedSource B h L hL q hq r hsize

theorem principalResidueNormalizedSource_toPMF (t : PrincipalTupleIndex B h) :
    ((sources) t).source.toPMF =
      (scalarCubeResidueWeights α (L t) q (hL t) (fun _ => q) (r t)
        (fun _ => hq) (fun _ => le_rfl) (hsize t)).toPMF :=
  normalizedUniformCubeSource_toPMF α (L t) q (hL t) (fun _ => q) (r t)
    (fun _ => hq) (fun _ => le_rfl) (hsize t)

theorem principalResidueNormalizedSource_source (t : PrincipalTupleIndex B h) :
    ((sources) t).source =
      scalarCubeResidueWeights α (L t) q (hL t) (fun _ => q) (r t)
        (fun _ => hq) (fun _ => le_rfl) (hsize t) :=
  FiniteProbabilityWeights.toPMF_injective
    (principalResidueNormalizedSource_toPMF B h L hL q hq r hsize t)

theorem principalResidueNormalizedSource_primitive (t : PrincipalTupleIndex B h) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget ((sources) t) A (scalarCubePrimitiveEnvelope α A 1 0 q) :=
  normalizedUniformCubeSource_primitive α (L t) q (hL t) (fun _ => q) (r t)
    (fun _ => hq) (fun _ => le_rfl) (hsize t) A

variable [Fintype D] [DecidableEq D] [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]

theorem principalResidueWeights_normalized_law :
    (principalResidueWeights B h L hL q hq r hsize).toPMF =
      dependentProductPMF (fun t => ((sources) t).source.toPMF) := by
  have hp : (principalResidueWeights B h L hL q hq r hsize).toPMF =
      dependentProductPMF (fun t => (scalarCubeResidueWeights α (L t) q (hL t)
        (fun _ => q) (r t) (fun _ => hq) (fun _ => le_rfl) (hsize t)).toPMF) :=
    FiniteProbabilityWeights.toPMF_pi (fun t => scalarCubeResidueWeights α (L t) q (hL t)
      (fun _ => q) (r t) (fun _ => hq) (fun _ => le_rfl) (hsize t))
  exact hp.trans (congrArg
    (fun p : ∀ t, PMF (IntegerScalarCubeBox α (L t)) => dependentProductPMF p)
    (funext (fun t => (principalResidueNormalizedSource_toPMF B h L hL q hq r hsize t).symm)))

theorem principalResidueWeights_eq_normalized_pi :
    principalResidueWeights B h L hL q hq r hsize =
      FiniteProbabilityWeights.pi (fun t => ((sources) t).source) := by
  apply FiniteProbabilityWeights.toPMF_injective
  exact (principalResidueWeights_normalized_law B h L hL q hq r hsize).trans
    (FiniteProbabilityWeights.toPMF_pi (fun t => ((sources) t).source)).symm

theorem principalResidueWeights_normalized_blocks :
    (principalResidueWeights B h L hL q hq r hsize).toPMF.map
      (fun y a b v => y ⟨a, b, v⟩) =
      dependentProductPMF (fun a => dependentProductPMF (fun b =>
        dependentProductPMF (fun v => ((sources) ⟨a, b, v⟩).source.toPMF))) := by
  have hp := congrArg (fun p : PMF (PrincipalIntegerTuples B h α L) =>
    p.map (fun y a b v => y ⟨a, b, v⟩))
    (principalResidueWeights_normalized_law B h L hL q hq r hsize)
  exact hp.trans (dependentProductPMF_sigma_curry
    (fun a b v => ((sources) ⟨a, b, v⟩).source.toPMF))

theorem principalTuple_complex_disintegrate_normalized [NeZero q]
    (f : (PrincipalTupleIndex B h → Option α → ZMod q) → PrincipalIntegerTuples B h α L → ℂ) :
    (principalTupleWeights (α := α) B h L hL).complexMean
        (fun y => f (principalResidueLabel q y) y) =
      ((principalTupleWeights (α := α) B h L hL).fiberLaw (principalResidueLabel q)).complexMean
        (fun residue => (FiniteProbabilityWeights.pi (fun t =>
          (principalResidueNormalizedSource B h L hL q hq residue hsize t).source)).complexMean
            (f residue)) := by
  refine (principalTuple_complex_disintegrate B h L hL q hq hsize f).trans ?_
  apply congrArg (fun g : (PrincipalTupleIndex B h → Option α → ZMod q) → ℂ =>
    ((principalTupleWeights (α := α) B h L hL).fiberLaw (principalResidueLabel q)).complexMean g)
  funext residue
  exact congrArg (fun p : FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) =>
    p.complexMean (f residue))
    (principalResidueWeights_eq_normalized_pi B h L hL q hq residue hsize)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ L t) (a : D)

local notation "sources" => principalResidueNormalizedSource B h L hL q hq r hsize
local notation "law" => FiniteProbabilityWeights.toPMF (principalResidueWeights B h L hL q hq r hsize)

theorem principalResidueWeights_axis_pair_law :
    (law).map (fun y (bv : B a × Fin (h a)) => y ⟨a, bv⟩) =
      dependentProductPMF (fun bv : B a × Fin (h a) => ((sources) ⟨a, bv⟩).source.toPMF) := by
  have hp := congrArg (fun p : PMF (PrincipalIntegerTuples B h α L) =>
    p.map (fun y (bv : B a × Fin (h a)) => y ⟨a, bv⟩))
    (principalResidueWeights_normalized_law B h L hL q hq r hsize)
  exact hp.trans (dependentProductPMF_marginal (fun t => ((sources) t).source.toPMF)
    (fun bv : B a × Fin (h a) => ⟨a, bv⟩) (by intro v w h; simpa using h))

theorem principalResidueWeights_axis_block_law :
    (law).map (fun y (b : B a) (v : Fin (h a)) => y ⟨a, b, v⟩) =
      dependentProductPMF (fun b : B a => dependentProductPMF
        (fun v : Fin (h a) => ((sources) ⟨a, b, v⟩).source.toPMF)) := by
  have hp := congrArg
    (fun p : PMF (∀ bv : B a × Fin (h a), IntegerScalarCubeBox α (L ⟨a, bv⟩)) =>
      p.map (fun y b v => y (b, v)))
    (principalResidueWeights_axis_pair_law B h L hL q hq r hsize a)
  have hc := PMF.map_comp (fun (y : PrincipalIntegerTuples B h α L) (bv : B a × Fin (h a)) => y ⟨a, bv⟩)
    (law) (fun y b v => y (b, v))
  exact hc.symm.trans (hp.trans (dependentProductPMF_curry
    (fun (b : B a) (v : Fin (h a)) => ((sources) ⟨a, b, v⟩).source.toPMF)))

theorem principalResidueWeights_axis_integer_law :
    (law).map (fun y (b : B a) (v : Fin (h a)) i => (y ⟨a, b, v⟩ i : ℤ)) =
      dependentProductPMF (fun b : B a =>
        (dependentProductPMF (fun v : Fin (h a) => ((sources) ⟨a, b, v⟩).source.toPMF)).map
          (fun y v i => (y v i : ℤ))) := by
  have hp := congrArg
    (fun p : PMF (∀ b : B a, ∀ v : Fin (h a), IntegerScalarCubeBox α (L ⟨a, b, v⟩)) =>
      p.map (fun y b v i => (y b v i : ℤ)))
    (principalResidueWeights_axis_block_law B h L hL q hq r hsize a)
  have hc := PMF.map_comp (fun (y : PrincipalIntegerTuples B h α L) (b : B a) (v : Fin (h a)) => y ⟨a, b, v⟩)
    (law) (fun y b v i => (y b v i : ℤ))
  refine hc.symm.trans (hp.trans ?_)
  exact dependentProductPMF_map
    (fun b : B a => dependentProductPMF
      (fun v : Fin (h a) => ((sources) ⟨a, b, v⟩).source.toPMF))
    (fun _ y v i => (y v i : ℤ))

noncomputable def principalResidueAxisJetPMF
    (c : B a → NormalizedScalarCubeSource Empty) (rows : Finset (Finset α))
    (offset : B a → ℤ) (shift : rows → ℤ) : PMF (rows → ℤ) :=
  (dependentProductPMF (fun b => (c b).source.toPMF.map (fun x => (x none : ℤ)))).bind
    (fun z => (law).map (fun y => shift + ∑ b : B a, fun row : rows =>
      (offset b + z b) * integerBooleanBlockJet
        (fun v : Fin (h a) => fun i => (y ⟨a, b, v⟩ i : ℤ)) row))

theorem principalResidueWeightedAxis_jet_sum_law
    (c : B a → NormalizedScalarCubeSource Empty) (rows : Finset (Finset α))
    (offset : B a → ℤ) (shift : rows → ℤ) :
    ((weightedModerateIntegerProductSource c (fun b v => (sources) ⟨a, b, v⟩)).toPMF).map
      (weightedModerateIntegerJetSum c (fun b v => (sources) ⟨a, b, v⟩) rows offset shift) =
      principalResidueAxisJetPMF B h L hL q hq r hsize a c rows offset shift := by
  unfold principalResidueAxisJetPMF
  have hp := weightedModerateProductSource_jet_sum_law c
    (fun b v => (sources) ⟨a, b, v⟩) rows offset shift
  refine hp.trans ?_
  have ht := congrArg (fun p : PMF (B a → Fin (h a) → Option α → ℤ) =>
    (dependentProductPMF (fun b => (c b).source.toPMF.map (fun x => (x none : ℤ)))).bind
      (fun z => p.map (fun y => shift + ∑ b : B a, fun row : rows =>
        (offset b + z b) * integerBooleanBlockJet (y b) row)))
    (principalResidueWeights_axis_integer_law B h L hL q hq r hsize a).symm
  simpa only [PMF.map_comp, Function.comp_def] using ht

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ L t) (a : D)
variable (c : B a → NormalizedScalarCubeSource Empty) (rows : Finset (Finset α))
variable (offset : B a → ℤ) (shift : rows → ℤ)

local notation "sources" => principalResidueNormalizedSource B h L hL q hq r hsize

noncomputable def principalResidueAxisGridDensity (K M : ℕ) (z : rows → ℤ) : ℝ :=
  (K : ℝ) ^ rows.card *
    (((principalResidueAxisJetPMF B h L hL q hq r hsize a c rows offset shift).map
      (integerGridResidue M)) (integerGridResidue M z)).toReal

theorem principalResidueAxisGridDensity_eq_normalized (K M : ℕ) (z : rows → ℤ) :
    principalResidueAxisGridDensity B h L hL q hq r hsize a c rows offset shift K M z =
      integerGridDensity (weightedModerateIntegerProductSource c
        (fun b v => (sources) ⟨a, b, v⟩))
        (weightedModerateIntegerJetSum c (fun b v => (sources) ⟨a, b, v⟩) rows offset shift)
        K M z := by
  symm
  have hp := integerGridDensity_eq_of_pmf_image
    (weightedModerateIntegerProductSource c (fun b v => (sources) ⟨a, b, v⟩))
    (weightedModerateIntegerJetSum c (fun b v => (sources) ⟨a, b, v⟩) rows offset shift)
    (principalResidueAxisJetPMF B h L hL q hq r hsize a c rows offset shift)
    (principalResidueWeightedAxis_jet_sum_law B h L hL q hq r hsize a c rows offset shift)
    K M z
  simpa only [principalResidueAxisGridDensity, Fintype.card_coe] using hp

theorem principalResidueAxisGridDensity_error_of_tail
    (K M : ℕ) [NeZero M] (S : Finset (rows → Fin M)) {ε : ℝ}
    (htail : spectrumTail S (fun k =>
      ‖∏ b : B a, weightedModerateGridCoefficient (c b)
        (fun v => (sources) ⟨a, b, v⟩) (offset b : ℝ) M rows k‖) ≤ ε)
    (z : rows → ℤ) :
    ‖(principalResidueAxisGridDensity B h L hL q hq r hsize a c rows offset shift K M z : ℂ) -
      weightedModerateGridApproximation c (fun b v => (sources) ⟨a, b, v⟩)
        K M rows offset shift z S‖ ≤ ((K : ℝ) / M) ^ rows.card * ε := by
  have he := congrArg (fun t : ℝ => ‖(t : ℂ) -
    weightedModerateGridApproximation c (fun b v => (sources) ⟨a, b, v⟩)
      K M rows offset shift z S‖)
    (principalResidueAxisGridDensity_eq_normalized B h L hL q hq r hsize a c rows offset shift K M z)
  exact he.trans_le (weightedModerateGridDensity_error_of_tail c
    (fun b v => (sources) ⟨a, b, v⟩) K M rows offset S htail shift z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem fullIntervalProgression_eq (H : ℕ) :
    integerProgressionSupport 0 (1 : ℤ) H = Finset.Ico (0 : ℤ) (H : ℤ) := by
  simp [integerProgressionSupport, translateSupport, integerStrideHom]

theorem fullIntervalProgression_subset (H : ℕ) :
    integerProgressionSupport 0 (1 : ℤ) H ⊆ Finset.Ico (0 : ℤ) (H : ℤ) :=
  (fullIntervalProgression_eq H).subset

theorem fullIntervalProgression_card (H : ℕ) :
    (integerProgressionSupport 0 (1 : ℤ) H).card = H := by
  rw [fullIntervalProgression_eq]
  simp

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (H : PrincipalTupleIndex B h → ℕ) (hH : ∀ j, 0 < H j)

omit [Fintype D] [DecidableEq D] [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] in
theorem containedProgressionTupleMap_fullInterval_of_cube
    (y : PrincipalIntegerTuples B h α H)
    (hy : ∀ j, IntegerScalarCube (H j) (fun i => (y j i : ℤ))) :
    containedProgressionTupleMap B h H H (fun _ => 1) (fun _ => 0) hH
      (fun j => fullIntervalProgression_subset (H j)) y = y := by
  funext j i
  apply Subtype.ext
  change (containedProgressionCubeMap α (H j) (H j) 1 0 (hH j)
    (fullIntervalProgression_subset (H j)) (y j) i : ℤ) = (y j i : ℤ)
  rw [containedProgressionCubeMap_value _ _ _ _ _ _ _ _ (hy j)]
  simp

theorem principalCubeWeights_fullInterval_fiberLaw
    (p : FiniteProbabilityWeights (PrincipalIntegerTuples B h α H))
    (hp : ∀ y, p.weight y ≠ 0 → ∀ j, IntegerScalarCube (H j) (fun i => (y j i : ℤ))) :
    p.fiberLaw (containedProgressionTupleMap B h H H (fun _ => 1) (fun _ => 0) hH
      (fun j => fullIntervalProgression_subset (H j))) = p := by
  apply FiniteProbabilityWeights.toPMF_injective
  exact (p.toPMF_fiberLaw _).trans ((p.toPMF_map_congr_on_support _ id (fun y hy =>
    containedProgressionTupleMap_fullInterval_of_cube B h H hH y (hp y hy))).trans
      (PMF.map_id p.toPMF))

theorem containedProgressionResidueLaw_fullInterval
    (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
    (hsize : ∀ j, (Fintype.card α + 1) * q ≤ H j) :
    containedProgressionResidueLaw B h H H (fun _ => 1) (fun _ => 0) hH hH
      (fun j => fullIntervalProgression_subset (H j)) q hq r hsize =
      principalResidueWeights B h H hH q hq r hsize := by
  exact principalCubeWeights_fullInterval_fiberLaw B h H hH _
    (principalResidueWeights_cube_support B h H hH q hq r hsize)

theorem containedSupportedProgressionLaw_fullInterval
    (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
    (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = r))) :
    containedSupportedProgressionLaw B h H H (fun _ => 1) (fun _ => 0) hH hH
      (fun j => fullIntervalProgression_subset (H j)) q r hcell =
      (principalTupleWeights (α := α) B h H hH).condition
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell := by
  exact principalCubeWeights_fullInterval_fiberLaw B h H hH _
    (principalSupportedResidue_cube_support B h H hH q r hcell)

theorem containedProgressionResidueLaw_fullInterval_eq_condition
    (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
    (hsize : ∀ j, (Fintype.card α + 1) * q ≤ H j)
    (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = r))) :
    containedProgressionResidueLaw B h H H (fun _ => 1) (fun _ => 0) hH hH
      (fun j => fullIntervalProgression_subset (H j)) q hq r hsize =
      (principalTupleWeights (α := α) B h H hH).condition
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell := by
  rw [containedProgressionResidueLaw_fullInterval B h H hH q hq r hsize]
  exact principalResidueWeights_eq_condition B h H hH q hq r hsize

theorem containedProgressionResidueLaw_fullInterval_integer_law
    (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
    (hsize : ∀ j, (Fintype.card α + 1) * q ≤ H j) :
    (containedProgressionResidueLaw B h H H (fun _ => 1) (fun _ => 0) hH hH
      (fun j => fullIntervalProgression_subset (H j)) q hq r hsize).toPMF.map
        principalTupleIntegers =
      (principalResidueWeights B h H hH q hq r hsize).toPMF.map principalTupleIntegers := by
  rw [containedProgressionResidueLaw_fullInterval B h H hH q hq r hsize]

end Erdos3

end

end OAI
