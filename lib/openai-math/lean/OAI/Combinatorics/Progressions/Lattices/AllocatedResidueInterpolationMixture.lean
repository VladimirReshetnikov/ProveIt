import OAI.Combinatorics.Progressions.Estimates.PositiveFiberMarginal
import OAI.Combinatorics.Progressions.Geometry.PrincipalCoordinatePartition
import OAI.Combinatorics.Progressions.Probability.AllocatedActiveAxisSourceLaw
import OAI.Combinatorics.Progressions.Sampling.AllocatedWeightedGridMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

noncomputable def principalSupportedCoordinateWeights (t : PrincipalTupleIndex B h) :
    FiniteProbabilityWeights (IntegerScalarCubeBox α (L t)) :=
  (integerScalarCubeWeights α (L t) (hL t)).condition
    (Finset.univ.filter (fun z => (fun i => ((z i : ℤ) : ZMod q)) = r t))
    (FiniteProbabilityWeights.coordinate_fiber_mass_pos
      (fun t => integerScalarCubeWeights α (L t) (hL t))
      (fun t (z : IntegerScalarCubeBox α (L t)) i => ((z i : ℤ) : ZMod q)) r hcell t)

local notation "coord" => principalSupportedCoordinateWeights B h L hL q r hcell
local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B h L hL)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

theorem principalSupportedResidueWeights_eq_pi :
    (conditioned) = FiniteProbabilityWeights.pi (coord) :=
  FiniteProbabilityWeights.pi_condition_positive_fiber
    (fun t => integerScalarCubeWeights α (L t) (hL t))
    (fun t (z : IntegerScalarCubeBox α (L t)) i => ((z i : ℤ) : ZMod q)) r hcell

theorem principalSupportedResiduePMF_eq_product :
    (conditioned).toPMF = dependentProductPMF (fun t => ((coord) t).toPMF) := by
  exact (congrArg (fun p : FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) => p.toPMF)
    (principalSupportedResidueWeights_eq_pi B h L hL q r hcell)).trans
      (FiniteProbabilityWeights.toPMF_pi (coord))

noncomputable def principalSupportedAxisTuplePMF (a : D) :
    PMF (∀ b : B a, ∀ v : Fin (h a), IntegerScalarCubeBox α (L ⟨a, b, v⟩)) :=
  dependentProductPMF (fun b => dependentProductPMF (fun v => ((coord) ⟨a, b, v⟩).toPMF))

theorem principalSupportedResidue_full_axis_law :
    (conditioned).toPMF.map (fun y (a : D) (b : B a) (v : Fin (h a)) => y ⟨a, b, v⟩) =
      dependentProductPMF (principalSupportedAxisTuplePMF B h L hL q r hcell) := by
  have hp := congrArg (fun p : PMF (PrincipalIntegerTuples B h α L) =>
    p.map (fun y (a : D) (b : B a) (v : Fin (h a)) => y ⟨a, b, v⟩))
    (principalSupportedResiduePMF_eq_product B h L hL q r hcell)
  exact hp.trans (dependentProductPMF_sigma_curry
    (fun a b v => ((coord) ⟨a, b, v⟩).toPMF))

theorem principalSupportedResidue_selected_axis_law {A : Type*} [Fintype A]
    (e : A → D) (he : Function.Injective e) :
    (conditioned).toPMF.map (fun y (a : A) (b : B (e a)) (v : Fin (h (e a))) => y ⟨e a, b, v⟩) =
      dependentProductPMF (fun a => principalSupportedAxisTuplePMF B h L hL q r hcell (e a)) := by
  have hp := congrArg (fun p : PMF (∀ a : D, ∀ b : B a, ∀ v : Fin (h a),
      IntegerScalarCubeBox α (L ⟨a, b, v⟩)) => p.map (fun y a => y (e a)))
    (principalSupportedResidue_full_axis_law B h L hL q r hcell)
  rw [PMF.map_comp] at hp
  exact hp.trans (dependentProductPMF_marginal
    (principalSupportedAxisTuplePMF B h L hL q r hcell) e he)

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem scalarCubeResidue_fiber_eq {α : Type*} [Fintype α] [DecidableEq α]
    (L q : ℕ) (r : Option α → ZMod q) :
    Finset.univ.filter (fun x : IntegerScalarCubeBox α L =>
      (fun i => ((x i : ℤ) : ZMod q)) = r) =
        scalarCubeResidueSet α L (fun _ => q) r := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    mem_scalarCubeResidueSet, funext_iff]

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

theorem principalSupportedResidue_marginal {V : Type*} [Fintype V]
    (e : V → PrincipalTupleIndex B h) (he : Function.Injective e)
    (hsize : ∀ v, (Fintype.card α + 1) * q ≤ L (e v)) :
    ((principalTupleWeights (α := α) B h L hL).condition
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).toPMF.map
        (fun y v => y (e v)) =
      dependentProductPMF (fun v =>
        (normalizedUniformCubeSource α (L (e v)) q (hL (e v)) (fun _ => q) (r (e v))
          (fun _ => hq) (fun _ => le_rfl) (hsize v)).source.toPMF) := by
  have hpositive : 0 < (FiniteProbabilityWeights.pi
      (fun t => integerScalarCubeWeights α (L t) (hL t))).mass
        (Finset.univ.filter (fun y => (fun t i => ((y t i : ℤ) : ZMod q)) = r)) := hcell
  have hp := FiniteProbabilityWeights.pi_condition_positive_fiber_marginal
    (fun t => integerScalarCubeWeights α (L t) (hL t))
    (fun t (x : IntegerScalarCubeBox α (L t)) i => ((x i : ℤ) : ZMod q)) r hpositive e he
  refine hp.trans ?_
  apply congrArg (fun p : ∀ v, PMF (IntegerScalarCubeBox α (L (e v))) => dependentProductPMF p)
  funext v
  rw [normalizedUniformCubeSource_toPMF]
  simp only [scalarCubeResidueWeights]
  congr 2
  exact scalarCubeResidue_fiber_eq (L (e v)) q (r (e v))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (a : D) (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ L ⟨a, b, v⟩)

noncomputable def principalSupportedAxisSources (b : B a) (v : Fin (h a)) :
    NormalizedScalarCubeSource α :=
  normalizedUniformCubeSource α (L ⟨a, b, v⟩) q (hL ⟨a, b, v⟩) (fun _ => q) (r ⟨a, b, v⟩)
    (fun _ => hq) (fun _ => le_rfl) (hsize b v)

local notation "sources" => principalSupportedAxisSources B h L hL q hq r a hsize

omit [Fintype D] [DecidableEq D] [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] in
theorem principalSupportedAxisSources_primitive (b : B a) (v : Fin (h a)) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget ((sources) b v) A (scalarCubePrimitiveEnvelope α A 1 0 q) :=
  normalizedUniformCubeSource_primitive α (L ⟨a, b, v⟩) q (hL ⟨a, b, v⟩) (fun _ => q)
    (r ⟨a, b, v⟩) (fun _ => hq) (fun _ => le_rfl) (hsize b v) A

variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

theorem principalSupportedResidue_axis_marginal :
    ((principalTupleWeights (α := α) B h L hL).condition
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).toPMF.map
        (fun y (b : B a) (v : Fin (h a)) => y ⟨a, b, v⟩) =
      dependentProductPMF (fun b => dependentProductPMF (fun v => ((sources) b v).source.toPMF)) := by
  have hp := principalSupportedResidue_marginal B h L hL q hq r hcell
    (fun t : B a × Fin (h a) => ⟨a, t⟩)
    (by intro x y hxy; simpa using hxy) (fun t => hsize t.1 t.2)
  have ht := congrArg (fun p => p.map (fun x b v => x (b, v))) hp
  rw [PMF.map_comp] at ht
  exact ht.trans (dependentProductPMF_curry
    (fun b v => ((sources) b v).source.toPMF))

theorem principalSupportedResidue_axis_integer_law :
    ((principalTupleWeights (α := α) B h L hL).condition
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).toPMF.map
        (fun y (b : B a) (v : Fin (h a)) i => (y ⟨a, b, v⟩ i : ℤ)) =
      dependentProductPMF (fun b => (dependentProductPMF
        (fun v => ((sources) b v).source.toPMF)).map (fun y v i => (y v i : ℤ))) := by
  have hp := congrArg (fun p => p.map (fun x b v i => (x b v i : ℤ)))
    (principalSupportedResidue_axis_marginal B h L hL q hq r a hsize hcell)
  rw [PMF.map_comp] at hp
  exact hp.trans (dependentProductPMF_map
    (fun b => dependentProductPMF (fun v => ((sources) b v).source.toPMF))
    (fun _ y v i => (y v i : ℤ)))

theorem principalSupportedResidue_axis_jet_sum_law
    (c : B a → NormalizedScalarCubeSource Empty)
    (rows : Finset (Finset α)) (offset : B a → ℤ) (shift : rows → ℤ) :
    (weightedModerateIntegerProductSource c (sources)).toPMF.map
      (weightedModerateIntegerJetSum c (sources) rows offset shift) =
      (dependentProductPMF (fun b => (c b).source.toPMF.map (fun z => (z none : ℤ)))).bind
        (fun coeff => ((principalTupleWeights (α := α) B h L hL).condition
          (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).toPMF.map
            (fun y => shift + ∑ b, fun t : rows => (offset b + coeff b) *
              integerBooleanBlockJet (fun v i => (y ⟨a, b, v⟩ i : ℤ)) t)) := by
  refine (weightedModerateProductSource_jet_sum_law c (sources) rows offset shift).trans ?_
  have hp := congrArg (fun p : PMF (B a → Fin (h a) → Option α → ℤ) =>
    (dependentProductPMF (fun b => (c b).source.toPMF.map (fun z => (z none : ℤ)))).bind
      (fun coeff => p.map (fun y => shift + ∑ b, fun t : rows =>
        (offset b + coeff b) * integerBooleanBlockJet (y b) t)))
    (principalSupportedResidue_axis_integer_law B h L hL q hq r a hsize hcell).symm
  simpa only [PMF.map_comp, Function.comp_def] using hp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

noncomputable def principalSupportedAxisWeights (P : D → Prop) [DecidablePred P] :
    FiniteProbabilityWeights (PrincipalAxisTuples (α := α) P L) :=
  FiniteProbabilityWeights.pi
    (fun j : PrincipalTupleIndex (fun d : {d // P d} => B d.val) (fun d => h d.val) =>
      principalSupportedCoordinateWeights B h L hL q r hcell ⟨j.1.val, j.2⟩)

local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights (α := α) B h L hL)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell
local notation "axisWeights" => principalSupportedAxisWeights B h L hL q r hcell

theorem principalSupportedResidueWeights_partition_weight
    (P : D → Prop) [DecidablePred P] (y : PrincipalIntegerTuples B h α L) :
    (conditioned).weight y =
      (axisWeights P).weight (principalAxisRestrict P y) *
      (axisWeights (fun d => ¬P d)).weight (principalAxisRestrict (fun d => ¬P d) y) := by
  rw [principalSupportedResidueWeights_eq_pi B h L hL q r hcell]
  exact principalCoordinateWeights_partition_weight P L
    (principalSupportedCoordinateWeights B h L hL q r hcell) y

theorem principalSupportedResidueWeights_partition
    (P : D → Prop) [DecidablePred P] (f : PrincipalIntegerTuples B h α L → ℂ) :
    (conditioned).complexMean f =
      (axisWeights P).complexMean (fun u =>
        (axisWeights (fun d => ¬P d)).complexMean (fun v => f (principalAxisJoin P u v))) := by
  rw [principalSupportedResidueWeights_eq_pi B h L hL q r hcell]
  exact principalCoordinateWeights_partition P L
    (principalSupportedCoordinateWeights B h L hL q r hcell) f

theorem principalSupportedResidueWeights_partition_mul
    (P : D → Prop) [DecidablePred P]
    (φ : PrincipalAxisTuples (α := α) P L → ℂ)
    (ψ : PrincipalAxisTuples (α := α) (fun d => ¬P d) L → ℂ) :
    (conditioned).complexMean (fun y =>
      φ (principalAxisRestrict P y) * ψ (principalAxisRestrict (fun d => ¬P d) y)) =
      (axisWeights P).complexMean φ * (axisWeights (fun d => ¬P d)).complexMean ψ := by
  rw [principalSupportedResidueWeights_partition B h L hL q r hcell P]
  simp only [principalAxisRestrict_join_left, principalAxisRestrict_join_right,
    FiniteProbabilityWeights.complexMean_mul_left]
  simp only [FiniteProbabilityWeights.complexMean, Finset.sum_mul, mul_assoc]

theorem principalSupportedAxisWeights_eq_residueWeights
    (P : D → Prop) [DecidablePred P] (hq : 0 < q)
    (hsize : ∀ j : PrincipalTupleIndex (fun d : {d // P d} => B d.val) (fun d => h d.val),
      (Fintype.card α + 1) * q ≤ principalAxisLength P L j) :
    axisWeights P =
      principalResidueWeights (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (fun j => hL ⟨j.1.val, j.2⟩) q hq
        (fun j => r ⟨j.1.val, j.2⟩) hsize := by
  unfold principalSupportedAxisWeights principalResidueWeights
  congr 1
  funext j
  simp only [principalSupportedCoordinateWeights, scalarCubeResidueWeights,
    principalAxisLength]
  congr 1
  exact scalarCubeResidue_fiber_eq (L ⟨j.1.val, j.2⟩) q (r ⟨j.1.val, j.2⟩)

end Erdos3

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
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "sides_pos" => allocatedPrincipalSides_pos B U basis S

noncomputable def allocatedActiveResidueSources
    (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) : NormalizedScalarCubeSource α :=
  principalSupportedAxisSources B (layerSamplerDegree I n) (sides) (sides_pos)
    q hq r ⟨j, Sum.inr i⟩
    (fun b v => by
      simpa only [allocatedPrincipalSides_active B U basis S j i hactive b v] using hsize) b v

local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedActiveResidueSources_length (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
    ((sources) b v).length = S.value :=
  allocatedPrincipalSides_active B U basis S j i hactive b v

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedActiveResidueSources_primitive
    (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget ((sources) b v) A (scalarCubePrimitiveEnvelope α A 1 0 q) :=
  principalSupportedAxisSources_primitive B (layerSamplerDegree I n) (sides) (sides_pos)
    q hq r ⟨j, Sum.inr i⟩ _ b v A

variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

theorem allocatedActiveResidueSources_jet_sum_law
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    (weightedModerateIntegerProductSource
      (fun _ : B ⟨j, Sum.inr i⟩ => allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
      (sources)).toPMF.map
        (weightedModerateIntegerJetSum
          (fun _ => allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
          (sources) rows (fun _ => 0) shift) =
      (dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
        allocatedLayerIntegerPMFs B U basis hR hσ S j i
          (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))).bind
        (fun coeff => ((principalTupleWeights (α := α) B (layerSamplerDegree I n)
          (sides) (sides_pos)).condition
            (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).toPMF.map
              (fun y => shift + ∑ b, fun t : rows => coeff b *
                integerBooleanBlockJet (fun v k => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ k : ℤ)) t)) := by
  have hp := principalSupportedResidue_axis_jet_sum_law B (layerSamplerDegree I n)
    (sides) (sides_pos) q hq r ⟨j, Sum.inr i⟩
    (fun b v => by
      simpa only [allocatedPrincipalSides_active B U basis S j i hactive b v] using hsize)
    hcell (fun _ => allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
    rows (fun _ => 0) shift
  have hc : (dependentProductPMF (fun _ : B ⟨j, Sum.inr i⟩ =>
      (allocatedPrincipalNormalizedSource B U basis hR S j i hactive).source.toPMF.map
        (fun z => (z none : ℤ)))) =
      dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
        allocatedLayerIntegerPMFs B U basis hR hσ S j i
          (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b)) :=
    congrArg (fun p : B ⟨j, Sum.inr i⟩ → PMF ℤ => dependentProductPMF p)
      (funext (fun b => allocatedPrincipalNormalizedSource_law B U basis hR hσ S j i hactive b))
  rw [hc] at hp
  simp only [zero_add] at hp
  convert hp using 6 <;> rfl

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
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "sources" => allocatedActiveResidueSources B U basis S j i hactive q hq r hsize

theorem allocatedActiveResidueSources_coeff_jet_law
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    (weightedModerateIntegerProductSource
      (fun _ : B ⟨j, Sum.inr i⟩ => allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
      sources).toPMF.map
        (fun x => (fun b => ((x b).1 none : ℤ),
          weightedModerateIntegerJetSum
            (fun _ => allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
            sources rows (fun _ => 0) shift x)) =
      (dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
        allocatedLayerIntegerPMFs B U basis hR hσ S j i
          (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))).bind
        (fun coeff => ((principalTupleWeights (α := α) B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).condition
            (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).toPMF.map
              (fun y => (coeff, shift + ∑ b, fun t : rows => coeff b *
                integerBooleanBlockJet (fun v k => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ k : ℤ)) t))) := by
  let c := fun _ : B ⟨j, Sum.inr i⟩ => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
  have hp := congrArg
    (fun p : PMF (B ⟨j, Sum.inr i⟩ → ℤ × (Fin (j.val + 1) → Option α → ℤ)) =>
      p.map (fun z => (fun b => (z b).1,
        shift + ∑ b, fun t : rows => (z b).1 * integerBooleanBlockJet (z b).2 t)))
    (weightedModerateProductSource_pair_law c sources)
  rw [PMF.map_comp, PMF.map_bind] at hp
  have hc : (dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
      (c b).source.toPMF.map (fun z => (z none : ℤ)))) =
      dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
        allocatedLayerIntegerPMFs B U basis hR hσ S j i
          (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b)) :=
    congrArg (fun p : B ⟨j, Sum.inr i⟩ → PMF ℤ => dependentProductPMF p)
      (funext (fun b => allocatedPrincipalNormalizedSource_law B U basis hR hσ S j i hactive b))
  rw [hc] at hp
  have ht := principalSupportedResidue_axis_integer_law B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
    q hq r ⟨j, Sum.inr i⟩
    (fun b v => by simpa only [allocatedPrincipalSides_active B U basis S j i hactive b v] using hsize)
    hcell
  have htarget := congrArg
    (fun p : PMF (B ⟨j, Sum.inr i⟩ → Fin (j.val + 1) → Option α → ℤ) =>
      (dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
        allocatedLayerIntegerPMFs B U basis hR hσ S j i
          (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))).bind
        (fun coeff => p.map (fun y => (coeff,
          shift + ∑ b, fun t : rows => coeff b * integerBooleanBlockJet (y b) t)))) ht.symm
  simp only [PMF.map_comp, Function.comp_def] at hp
  dsimp only [layerSamplerDegree] at hp htarget ⊢
  have hfinal := hp.trans htarget
  simp only [PMF.map_comp, Function.comp_def] at hfinal
  convert hfinal using 2
  · funext x
    congr 1
    funext t
    simp only [weightedModerateIntegerJetSum, Pi.add_apply, Finset.sum_apply,
      weightedModerateIntegerBlock, zero_add]
  · rfl

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
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S))
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

noncomputable def allocatedSupportedResidueJetPMF
    (rows : Finset (Finset α)) (shift : rows → ℤ) : PMF (rows → ℤ) :=
  (dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
    allocatedLayerIntegerPMFs B U basis hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))).bind
    (fun coeff => (conditioned).toPMF.map (fun y =>
      shift + ∑ b, fun t : rows => coeff b *
        integerBooleanBlockJet (fun v k => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ k : ℤ)) t))

theorem allocatedSupportedResidueJetPMF_source
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    (weightedModerateIntegerProductSource
      (fun _ : B ⟨j, Sum.inr i⟩ => allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
      (allocatedActiveResidueSources B U basis S j i hactive q hq r hsize)).toPMF.map
        (weightedModerateIntegerJetSum
          (fun _ => allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
          (allocatedActiveResidueSources B U basis S j i hactive q hq r hsize)
          rows (fun _ => 0) shift) =
      allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows shift :=
  allocatedActiveResidueSources_jet_sum_law B U basis S j i hactive q hq r hsize hcell
    hR hσ rows shift

theorem allocatedSupportedResidueJetPMF_constant_mixture
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value) :
    (conditioned).toPMF.bind (fun y =>
      integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
        (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)) =
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientChoice (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ none)).bind
        (fun c => allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows
          (fun t => booleanCoefficient (fun _ : Finset α => c) t)) := by
  let p := (conditioned).toPMF
  let a := dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
    allocatedLayerIntegerPMFs B U basis hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))
  let c := allocatedLayerIntegerPMFs B U basis hR hσ S j i
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
      c.bind (fun z => a.map (f y z)) := by
    rw [allocatedPhysicalGridJetPMF_principal B U basis hR hσ S j i hgrid,
      independentProductPMF_option, PMF.map_bind]
    simp only [PMF.map_comp]
    apply congrArg (fun k : ℤ → PMF (rows → ℤ) => c.bind k)
    funext z
    apply congrArg (fun g : (B ⟨j, Sum.inr i⟩ → ℤ) → rows → ℤ => a.map g)
    funext coeff t
    simp only [Function.comp_apply, f, Pi.add_apply, Finset.sum_apply,
      Option.elim_none, Option.elim_some]
  simp_rw [hpoint]
  change p.bind (fun y => c.bind (fun z => a.map (f y z))) =
    c.bind (fun z => a.bind (fun coeff => p.map (fun y => f y z coeff)))
  refine (PMF.bind_comm p c (fun y z => a.map (f y z))).trans ?_
  apply congrArg (fun k : ℤ → PMF (rows → ℤ) => c.bind k)
  funext z
  exact PMF.bind_comm p a (fun y coeff => PMF.pure (f y z coeff))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

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
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S))
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

theorem allocatedResidueInterpolation_constant_mixture
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℝ) :
    (conditioned).mean (fun y => integerRowMassInterpolation (basisAxisScale (basis j) i)
      (integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
        (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)) z) =
      ∫ c, integerRowMassInterpolation (basisAxisScale (basis j) i)
        (allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows
          (fun t => booleanCoefficient (fun _ : Finset α => c) t)) z ∂(constantLaw).toMeasure := by
  have hm := allocatedSupportedResidueJetPMF_constant_mixture B U basis hR hσ S q r hcell
    j i hgrid rows x
  have he := congrArg (fun μ : PMF (rows → ℤ) =>
    integerRowMassInterpolation (basisAxisScale (basis j) i) μ z) hm
  rw [integerRowMassInterpolation_finite_bind _ (Nat.cast_nonneg _),
    integerRowMassInterpolation_bind _ (Nat.cast_nonneg _)] at he
  exact he

theorem allocatedNormalizedResidueInterpolation_constant_mixture
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℝ) :
    (conditioned).mean (fun y => normalizedIntegerRowInterpolation (basisAxisScale (basis j) i)
      (integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
        (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)) z) =
      ∫ c, normalizedIntegerRowInterpolation (basisAxisScale (basis j) i)
        (allocatedSupportedResidueJetPMF B U basis hR hσ S q r hcell j i rows
          (fun t => booleanCoefficient (fun _ : Finset α => c) t)) z ∂(constantLaw).toMeasure := by
  have hm := allocatedSupportedResidueJetPMF_constant_mixture B U basis hR hσ S q r hcell
    j i hgrid rows x
  have he := congrArg (fun μ : PMF (rows → ℤ) =>
    normalizedIntegerRowInterpolation (basisAxisScale (basis j) i) μ z) hm
  rw [normalizedIntegerRowInterpolation_finite_bind _ (Nat.cast_nonneg _),
    normalizedIntegerRowInterpolation_bind _ (Nat.cast_nonneg _)] at he
  exact he

end Erdos3.VectorPolynomial

end

end OAI
