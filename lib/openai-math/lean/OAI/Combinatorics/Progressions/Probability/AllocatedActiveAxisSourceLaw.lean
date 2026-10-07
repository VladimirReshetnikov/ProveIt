import OAI.Combinatorics.Progressions.Estimates.AllocatedFrozenTupleGrouping

namespace OAI

section

namespace Erdos3

open scoped Classical

theorem normalizedUniformCubeSource_toPMF (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    (normalizedUniformCubeSource I L M hL m r hm hmM hsize).source.toPMF =
      (scalarCubeResidueWeights I L M hL m r hm hmM hsize).toPMF := by
  ext x
  change ENNReal.ofReal ((scalarCubeResidueWeights I L M hL m r hm hmM hsize).weight x * 1) =
    ENNReal.ofReal ((scalarCubeResidueWeights I L M hL m r hm hmM hsize).weight x)
  rw [mul_one]

theorem integerScalarCubeWeights_normalized_source (I : Type*) [Fintype I] [DecidableEq I]
    (L : ℕ) (hL : 0 < L) (hsize : Fintype.card I + 1 ≤ L) :
    (normalizedUniformCubeSource I L 1 hL (fun _ => 1) (fun _ => 0)
      (fun _ => by norm_num) (fun _ => le_rfl) (by simpa using hsize)).source.toPMF =
      (integerScalarCubeWeights I L hL).toPMF := by
  rw [normalizedUniformCubeSource_toPMF]
  have hr : scalarCubeResidueSet I L (fun _ => 1) (fun _ => 0) = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    apply (mem_scalarCubeResidueSet L (fun _ => 1) (fun _ => 0) x).mpr
    intro i
    exact Subsingleton.elim _ _
  have hm : (integerScalarCubeWeights I L hL).mass Finset.univ = 1 :=
    (integerScalarCubeWeights I L hL).total
  ext x
  change ENNReal.ofReal ((if x ∈ scalarCubeResidueSet I L (fun _ => 1) (fun _ => 0)
    then (integerScalarCubeWeights I L hL).weight x else 0) /
      (integerScalarCubeWeights I L hL).mass (scalarCubeResidueSet I L (fun _ => 1) (fun _ => 0))) =
    ENNReal.ofReal ((integerScalarCubeWeights I L hL).weight x)
  rw [hr, hm]
  simp

end Erdos3

end

section

namespace Erdos3

open scoped Classical

universe uX uY uZ uW

theorem pmf_pair_law_map {X : Type uX} {Y : Type uY} {Z : Type uZ} {W : Type uW}
    (p : PMF X) (c : PMF Y) (q : PMF Z) (f : X → Y × Z) (g : Y × Z → W)
    (h : p.map f = c.bind (fun y => q.map (fun z => (y, z)))) :
    p.map (g ∘ f) = c.bind (fun y => q.map (fun z => g (y, z))) := by
  rw [← PMF.map_comp, h, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

local notation "csource" => principalNormalizedSource hK hT hγ hlarge
local notation "pcoeff" => principalIntegerPMF K T γ hK hT hγ hlarge

theorem principalModerateSource_pair_law (s : Fin n → NormalizedScalarCubeSource I) :
    ((weightedModerateIntegerSource csource s).toPMF).map
      (fun x => ((x.1 none : ℤ), x.2)) =
      (pcoeff).bind (fun a =>
        (dependentProductPMF (fun j => (s j).source.toPMF)).map (fun y => (a, y))) := by
  rw [weightedModerateIntegerSource, FiniteProbabilityWeights.toPMF_prod, PMF.map_bind]
  simp_rw [PMF.map_comp]
  rw [← principalNormalizedSource_law hK hT hγ hlarge, PMF.bind_map]
  simp only [Function.comp_def]
  exact congrArg (fun q : PMF (∀ j, IntegerScalarCubeBox I (s j).length) =>
    (csource).source.toPMF.bind (fun x => q.map (fun y => ((x none : ℤ), y))))
    (FiniteProbabilityWeights.toPMF_pi (fun j => (s j).source))

theorem principalModerateSource_jet_law (s : Fin n → NormalizedScalarCubeSource I)
    (J : Finset (Finset I)) :
    ((weightedModerateIntegerSource csource s).toPMF).map
      (weightedModerateIntegerBlock csource s J 0) =
      (pcoeff).bind (fun a =>
        (dependentProductPMF (fun j => (s j).source.toPMF)).map
          (fun y r => a * integerBooleanBlockJet (fun j q => (y j q : ℤ)) (r : J))) := by
  have hp := congrArg (fun p : PMF (ℤ × (∀ j, IntegerScalarCubeBox I (s j).length)) =>
    p.map (fun ay (r : J) => ay.1 *
      integerBooleanBlockJet (fun j q => (ay.2 j q : ℤ)) r))
    (principalModerateSource_pair_law hK hT hγ hlarge s)
  rw [PMF.map_comp, PMF.map_bind] at hp
  simp only [PMF.map_comp] at hp
  change ((weightedModerateIntegerSource csource s).toPMF).map
    (fun x (r : J) => (0 + (x.1 none : ℤ)) *
      integerBooleanBlockJet (fun j q => (x.2 j q : ℤ)) r) = _
  simpa only [Function.comp_def, zero_add] using hp

section UniformTuples

variable (L : Fin n → ℕ) (hL : ∀ j, 0 < L j) (hsize : ∀ j, Fintype.card I + 1 ≤ L j)

noncomputable def normalizedUniformTupleSources : Fin n → NormalizedScalarCubeSource I :=
  fun j => normalizedUniformCubeSource I (L j) 1 (hL j)
    (fun _ => 1) (fun _ => 0) (fun _ => by norm_num) (fun _ => le_rfl) (by simpa using hsize j)

local notation "usources" => normalizedUniformTupleSources L hL hsize

theorem normalizedUniformTupleSources_law :
    dependentProductPMF (fun j => ((usources) j).source.toPMF) =
      dependentProductPMF (fun j => (integerScalarCubeWeights I (L j) (hL j)).toPMF) :=
  congrArg (fun p : ∀ j, PMF (IntegerScalarCubeBox I (L j)) => dependentProductPMF p)
    (funext (fun j => integerScalarCubeWeights_normalized_source I (L j) (hL j) (hsize j)))

theorem principalModerateSource_uniform_pair_law :
    ((weightedModerateIntegerSource csource usources).toPMF).map
      (fun x => ((x.1 none : ℤ), x.2)) =
      (pcoeff).bind (fun a =>
        (dependentProductPMF (fun j => (integerScalarCubeWeights I (L j) (hL j)).toPMF)).map
          (fun y => (a, y))) := by
  rw [principalModerateSource_pair_law]
  exact congrArg (fun q : PMF (∀ j, IntegerScalarCubeBox I (L j)) =>
    (pcoeff).bind (fun a => q.map (fun y => (a, y))))
    (normalizedUniformTupleSources_law L hL hsize)

theorem principalModerateSource_uniform_jet_law (J : Finset (Finset I)) :
    ((weightedModerateIntegerSource csource usources).toPMF).map
      (weightedModerateIntegerBlock csource usources J 0) =
      (pcoeff).bind (fun a =>
        (dependentProductPMF (fun j => (integerScalarCubeWeights I (L j) (hL j)).toPMF)).map
          (fun y r => a * integerBooleanBlockJet (fun j q => (y j q : ℤ)) (r : J))) := by
  have hp := pmf_pair_law_map
    ((weightedModerateIntegerSource csource usources).toPMF) (pcoeff)
    (dependentProductPMF (fun j => (integerScalarCubeWeights I (L j) (hL j)).toPMF))
    (fun x => ((x.1 none : ℤ), x.2))
    (fun ay : ℤ × (∀ j, IntegerScalarCubeBox I (L j)) => fun r : J => ay.1 *
      integerBooleanBlockJet (fun j q => (ay.2 j q : ℤ)) r)
    (principalModerateSource_uniform_pair_law hK hT hγ hlarge L hL hsize)
  change ((weightedModerateIntegerSource csource usources).toPMF).map
    (fun x (r : J) => (0 + (x.1 none : ℤ)) *
      integerBooleanBlockJet (fun j q => (x.2 j q : ℤ)) r) = _
  simpa only [Function.comp_def, zero_add] using hp

end UniformTuples

end Erdos3

end

section

namespace Erdos3

theorem weightedModerateSource_pair_law {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I) :
    ((weightedModerateIntegerSource c s).toPMF).map (fun x => ((x.1 none : ℤ), x.2)) =
      (c.source.toPMF.map (fun x => (x none : ℤ))).bind (fun a =>
        (dependentProductPMF (fun j => (s j).source.toPMF)).map (fun y => (a, y))) := by
  rw [weightedModerateIntegerSource, FiniteProbabilityWeights.toPMF_prod, PMF.map_bind, PMF.bind_map]
  simp_rw [PMF.map_comp]
  simp only [Function.comp_def]
  exact congrArg (fun q : PMF (∀ j, IntegerScalarCubeBox I (s j).length) =>
    c.source.toPMF.bind (fun x => q.map (fun y => ((x none : ℤ), y))))
    (FiniteProbabilityWeights.toPMF_pi (fun j => (s j).source))

theorem weightedModerateSource_integer_pair_law {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I) :
    ((weightedModerateIntegerSource c s).toPMF).map
      (fun x => ((x.1 none : ℤ), fun j q => (x.2 j q : ℤ))) =
      (c.source.toPMF.map (fun x => (x none : ℤ))).bind (fun a =>
        (dependentProductPMF (fun j => (s j).source.toPMF)).map
          (fun y => (a, fun j q => (y j q : ℤ)))) := by
  have hp := congrArg (fun p : PMF (ℤ × (∀ j, IntegerScalarCubeBox I (s j).length)) =>
    p.map (fun ay => (ay.1, fun j q => (ay.2 j q : ℤ))))
    (weightedModerateSource_pair_law c s)
  rw [PMF.map_comp, PMF.map_bind] at hp
  simpa only [PMF.map_comp, Function.comp_def] using hp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

universe uB uX uY uZ

theorem dependentProductPMF_pair_transport
    {B : Type uB} [Fintype B] {X : B → Type uX} {Y : B → Type uY} {Z : B → Type uZ}
    [∀ b, Countable (X b)] [∀ b, Countable (Y b)] [∀ b, Countable (Z b)]
    [∀ b, MeasurableSpace (X b)] [∀ b, MeasurableSpace (Y b)] [∀ b, MeasurableSpace (Z b)]
    [∀ b, MeasurableSingletonClass (X b)] [∀ b, MeasurableSingletonClass (Y b)]
    [∀ b, MeasurableSingletonClass (Z b)]
    (p : ∀ b, PMF (X b)) (c : ∀ b, PMF (Y b)) (q : ∀ b, PMF (Z b))
    (f : ∀ b, X b → Y b × Z b)
    (h : ∀ b, (p b).map (f b) = (c b).bind (fun y => (q b).map (fun z => (y, z)))) :
    (dependentProductPMF p).map (fun x b => f b (x b)) =
      (dependentProductPMF c).bind (fun y => (dependentProductPMF q).map
        (fun z b => (y b, z b))) := by
  exact (dependentProductPMF_map p f).trans
    ((congrArg (fun r : ∀ b, PMF (Y b × Z b) => dependentProductPMF r) (funext h)).trans
      (dependentProductPMF_pair c q).symm)

theorem finiteWeights_pi_pair_transport
    {B : Type uB} [Fintype B] [DecidableEq B]
    {X : B → Type uX} {Y : B → Type uY} {Z : B → Type uZ}
    [∀ b, Fintype (X b)] [∀ b, Countable (Y b)] [∀ b, Countable (Z b)]
    [∀ b, MeasurableSpace (X b)] [∀ b, MeasurableSpace (Y b)] [∀ b, MeasurableSpace (Z b)]
    [∀ b, MeasurableSingletonClass (X b)] [∀ b, MeasurableSingletonClass (Y b)]
    [∀ b, MeasurableSingletonClass (Z b)]
    (p : ∀ b, FiniteProbabilityWeights (X b)) (c : ∀ b, PMF (Y b)) (q : ∀ b, PMF (Z b))
    (f : ∀ b, X b → Y b × Z b)
    (h : ∀ b, (p b).toPMF.map (f b) = (c b).bind (fun y => (q b).map (fun z => (y, z)))) :
    (FiniteProbabilityWeights.pi p).toPMF.map (fun x b => f b (x b)) =
      (dependentProductPMF c).bind (fun y => (dependentProductPMF q).map
        (fun z b => (y b, z b))) := by
  have hp : (FiniteProbabilityWeights.pi p).toPMF =
      dependentProductPMF (fun b => (p b).toPMF) := FiniteProbabilityWeights.toPMF_pi p
  have hm := congrArg (fun r : PMF (∀ b, X b) => r.map (fun x b => f b (x b))) hp
  exact hm.trans (dependentProductPMF_pair_transport (fun b => (p b).toPMF) c q f h)

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
variable (c : B → NormalizedScalarCubeSource Empty)
variable (s : B → Fin n → NormalizedScalarCubeSource I)

theorem weightedModerateProductSource_pair_law :
    ((weightedModerateIntegerProductSource c s).toPMF).map
      (fun x b => (((x b).1 none : ℤ), fun j q => ((x b).2 j q : ℤ))) =
      (dependentProductPMF (fun b => (c b).source.toPMF.map (fun x => (x none : ℤ)))).bind
        (fun a => (dependentProductPMF (fun b =>
          (dependentProductPMF (fun j => (s b j).source.toPMF)).map
            (fun y j q => (y j q : ℤ)))).map (fun y b => (a b, y b))) := by
  apply finiteWeights_pi_pair_transport
    (X := fun b => IntegerScalarCubeBox Empty (c b).length ×
      (∀ j, IntegerScalarCubeBox I (s b j).length))
    (Y := fun _ => ℤ) (Z := fun _ => Fin n → Option I → ℤ)
    (fun b => weightedModerateIntegerSource (c b) (s b))
    (fun b => (c b).source.toPMF.map (fun x => (x none : ℤ)))
    (fun b => (dependentProductPMF (fun j => (s b j).source.toPMF)).map
      (fun y j q => (y j q : ℤ)))
    (fun b (x : IntegerScalarCubeBox Empty (c b).length ×
      (∀ j, IntegerScalarCubeBox I (s b j).length)) =>
        ((x.1 none : ℤ), fun j q => (x.2 j q : ℤ)))
  intro b
  simpa only [PMF.map_comp, Function.comp_def] using
    (weightedModerateSource_integer_pair_law (c b) (s b))

theorem weightedModerateProductSource_jet_sum_law
    (J : Finset (Finset I)) (offset : B → ℤ) (shift : J → ℤ) :
    ((weightedModerateIntegerProductSource c s).toPMF).map
      (weightedModerateIntegerJetSum c s J offset shift) =
      (dependentProductPMF (fun b => (c b).source.toPMF.map (fun x => (x none : ℤ)))).bind
        (fun a => (dependentProductPMF (fun b =>
          (dependentProductPMF (fun j => (s b j).source.toPMF)).map
            (fun y j q => (y j q : ℤ)))).map
              (fun y => shift + ∑ b, fun r : J => (offset b + a b) * integerBooleanBlockJet (y b) r)) := by
  have hp := congrArg (fun p : PMF (B → ℤ × (Fin n → Option I → ℤ)) =>
    p.map (fun z => shift + ∑ b, fun r : J =>
      (offset b + (z b).1) * integerBooleanBlockJet (z b).2 r))
    (weightedModerateProductSource_pair_law c s)
  rw [PMF.map_comp, PMF.map_bind] at hp
  change ((weightedModerateIntegerProductSource c s).toPMF).map
    (fun x => shift + ∑ b, fun r : J => (offset b + ((x b).1 none : ℤ)) *
      integerBooleanBlockJet (fun j q => ((x b).2 j q : ℤ)) r) = _
  simpa only [PMF.map_comp, Function.comp_def] using hp

end Erdos3

end

section

namespace Erdos3

open scoped Classical

universe uP uQ uV

theorem pmf_map_law_transport {X : Type uP} {Y : Type uQ} {Z : Type uV}
    (p : PMF X) (q : PMF Y) (f : X → Y) (g : Y → Z) (h : p.map f = q) :
    p.map (g ∘ f) = q.map g :=
  (PMF.map_comp f p g).symm.trans (congrArg (fun r : PMF Y => r.map g) h)

theorem integerScalarTuplePMF_congr {V α : Type*} [Fintype V] [Fintype α] [DecidableEq α]
    (L₁ L₂ : V → ℕ) (h₁ : ∀ v, 0 < L₁ v) (h₂ : ∀ v, 0 < L₂ v)
    (hL : L₁ = L₂) :
    (dependentProductPMF (fun v => (integerScalarCubeWeights α (L₁ v) (h₁ v)).toPMF)).map
      (fun x v q => (x v q : ℤ)) =
    (dependentProductPMF (fun v => (integerScalarCubeWeights α (L₂ v) (h₂ v)).toPMF)).map
      (fun x v q => (x v q : ℤ)) := by
  subst L₂
  rfl

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedFrozenTuple_single_block_marginal
    (a : {a : LayerSamplerAxis I n // grid a}) (b : B a.val) :
    ((allocatedFrozenTupleWeights (α := α) B U basis S).toPMF).map
      (fun u (v : Fin (layerSamplerDegree I n a.val)) => u ⟨a, b, v⟩) =
      dependentProductPMF (fun v : Fin (layerSamplerDegree I n a.val) =>
        (integerScalarCubeWeights α (sides ⟨a.val, b, v⟩)
          (allocatedPrincipalSides_pos B U basis S ⟨a.val, b, v⟩)).toPMF) := by
  let w := fun k : PrincipalTupleIndex
    (fun d : {d // grid d} => B d.val) (fun d => layerSamplerDegree I n d.val) =>
      integerScalarCubeWeights α (sides ⟨k.1.val, k.2⟩)
        (allocatedPrincipalSides_pos B U basis S ⟨k.1.val, k.2⟩)
  have hp : (allocatedFrozenTupleWeights (α := α) B U basis S).toPMF =
      dependentProductPMF (fun k => (w k).toPMF) :=
    FiniteProbabilityWeights.toPMF_pi w
  exact (congrArg (fun p : PMF (PrincipalAxisTuples (α := α) grid sides) =>
    p.map (fun u (v : Fin (layerSamplerDegree I n a.val)) => u ⟨a, b, v⟩)) hp).trans
      (dependentProductPMF_marginal (fun k => (w k).toPMF) (fun v => ⟨a, b, v⟩)
        (by intro v z h; simpa using h))

theorem allocatedFrozenTuple_single_block_integer_law
    (a : {a : LayerSamplerAxis I n // grid a}) (b : B a.val) :
    ((allocatedFrozenTupleWeights (α := α) B U basis S).toPMF).map
      (fun u (v : Fin (layerSamplerDegree I n a.val)) q => (u ⟨a, b, v⟩ q : ℤ)) =
      (dependentProductPMF (fun v : Fin (layerSamplerDegree I n a.val) =>
        (integerScalarCubeWeights α (sides ⟨a.val, b, v⟩)
          (allocatedPrincipalSides_pos B U basis S ⟨a.val, b, v⟩)).toPMF)).map
            (fun x v q => (x v q : ℤ)) := by
  exact pmf_map_law_transport
    (allocatedFrozenTupleWeights (α := α) B U basis S).toPMF
    (dependentProductPMF (fun v : Fin (layerSamplerDegree I n a.val) =>
      (integerScalarCubeWeights α (sides ⟨a.val, b, v⟩)
        (allocatedPrincipalSides_pos B U basis S ⟨a.val, b, v⟩)).toPMF))
    (fun u (v : Fin (layerSamplerDegree I n a.val)) => u ⟨a, b, v⟩)
    (fun x v q => (x v q : ℤ))
    (allocatedFrozenTuple_single_block_marginal (α := α) B U basis S a b)

theorem allocatedFrozenTuple_active_block_law (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (hgrid : grid ⟨j, Sum.inr i⟩) (b : B ⟨j, Sum.inr i⟩) :
    ((allocatedFrozenTupleWeights (α := α) B U basis S).toPMF).map
      (fun u (v : Fin (j.val + 1)) q => (u ⟨⟨⟨j, Sum.inr i⟩, hgrid⟩, b, v⟩ q : ℤ)) =
      (dependentProductPMF (fun _ : Fin (j.val + 1) =>
        (integerScalarCubeWeights α S.value S.positive).toPMF)).map
          (fun x v q => (x v q : ℤ)) := by
  exact (allocatedFrozenTuple_single_block_integer_law (α := α) B U basis S
    ⟨⟨j, Sum.inr i⟩, hgrid⟩ b).trans
      (integerScalarTuplePMF_congr
        (fun v => sides ⟨⟨j, Sum.inr i⟩, b, v⟩) (fun _ => S.value)
        (fun v => allocatedPrincipalSides_pos B U basis S ⟨⟨j, Sum.inr i⟩, b, v⟩)
        (fun _ => S.positive)
        (funext (fun v => allocatedPrincipalSides_active B U basis S j i hactive b v)))

theorem allocatedFrozenTuple_active_normalized_block_law (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (hgrid : grid ⟨j, Sum.inr i⟩) (b : B ⟨j, Sum.inr i⟩)
    (hsize : Fintype.card α + 1 ≤ S.value) :
    ((allocatedFrozenTupleWeights (α := α) B U basis S).toPMF).map
      (fun u (v : Fin (j.val + 1)) q => (u ⟨⟨⟨j, Sum.inr i⟩, hgrid⟩, b, v⟩ q : ℤ)) =
      (dependentProductPMF (fun v => ((normalizedUniformTupleSources
        (fun _ : Fin (j.val + 1) => S.value) (fun _ => S.positive) (fun _ => hsize)) v).source.toPMF)).map
          (fun x v q => (x v q : ℤ)) := by
  rw [allocatedFrozenTuple_active_block_law B U basis S j i hactive hgrid b]
  exact congrArg (fun p : PMF (∀ _ : Fin (j.val + 1), IntegerScalarCubeBox α S.value) =>
    p.map (fun x v q => (x v q : ℤ)))
      (normalizedUniformTupleSources_law
        (fun _ : Fin (j.val + 1) => S.value) (fun _ => S.positive) (fun _ => hsize)).symm

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedFrozenTuple_active_axis_normalized_law (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hsize : Fintype.card α + 1 ≤ S.value) :
    ((allocatedFrozenTupleWeights (α := α) B U basis S).toPMF).map
      (fun u (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) q =>
        (u ⟨⟨⟨j, Sum.inr i⟩, hgrid⟩, b, v⟩ q : ℤ)) =
      dependentProductPMF (fun _ : B ⟨j, Sum.inr i⟩ =>
        (dependentProductPMF (fun v => ((normalizedUniformTupleSources
          (fun _ : Fin (j.val + 1) => S.value) (fun _ => S.positive) (fun _ => hsize)) v).source.toPMF)).map
            (fun x v q => (x v q : ℤ))) := by
  have hs : ((allocatedFrozenTupleWeights (α := α) B U basis S).toPMF).map
      (fun u (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) q =>
        (u ⟨⟨⟨j, Sum.inr i⟩, hgrid⟩, b, v⟩ q : ℤ)) =
      (dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
        dependentProductPMF (fun v : Fin (j.val + 1) =>
          (integerScalarCubeWeights α (sides ⟨⟨j, Sum.inr i⟩, b, v⟩)
            (allocatedPrincipalSides_pos B U basis S ⟨⟨j, Sum.inr i⟩, b, v⟩)).toPMF))).map
              (fun x b v q => (x b v q : ℤ)) :=
    pmf_map_law_transport
      (allocatedFrozenTupleWeights (α := α) B U basis S).toPMF
      (dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
        dependentProductPMF (fun v : Fin (j.val + 1) =>
          (integerScalarCubeWeights α (sides ⟨⟨j, Sum.inr i⟩, b, v⟩)
            (allocatedPrincipalSides_pos B U basis S ⟨⟨j, Sum.inr i⟩, b, v⟩)).toPMF)))
      (fun u (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) =>
        u ⟨⟨⟨j, Sum.inr i⟩, hgrid⟩, b, v⟩)
      (fun x b v q => (x b v q : ℤ))
      (allocatedFrozenTuple_block_marginal (α := α) B U basis S
        ⟨⟨j, Sum.inr i⟩, hgrid⟩)
  refine hs.trans ((dependentProductPMF_map
    (fun b : B ⟨j, Sum.inr i⟩ => dependentProductPMF (fun v : Fin (j.val + 1) =>
      (integerScalarCubeWeights α (sides ⟨⟨j, Sum.inr i⟩, b, v⟩)
        (allocatedPrincipalSides_pos B U basis S ⟨⟨j, Sum.inr i⟩, b, v⟩)).toPMF))
    (fun _ x v q => (x v q : ℤ))).trans ?_)
  apply congrArg (fun p : B ⟨j, Sum.inr i⟩ → PMF (Fin (j.val + 1) → Option α → ℤ) =>
    dependentProductPMF p)
  funext b
  exact (integerScalarTuplePMF_congr
    (fun v => sides ⟨⟨j, Sum.inr i⟩, b, v⟩) (fun _ => S.value)
    (fun v => allocatedPrincipalSides_pos B U basis S ⟨⟨j, Sum.inr i⟩, b, v⟩)
    (fun _ => S.positive)
    (funext (fun v => allocatedPrincipalSides_active B U basis S j i hactive b v))).trans
      (congrArg (fun p : PMF (∀ _ : Fin (j.val + 1), IntegerScalarCubeBox α S.value) =>
        p.map (fun x v q => (x v q : ℤ)))
        (normalizedUniformTupleSources_law
          (fun _ : Fin (j.val + 1) => S.value) (fun _ => S.positive) (fun _ => hsize)).symm)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
variable (b : B ⟨j, Sum.inr i⟩)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (hsize : Fintype.card α + 1 ≤ S.value)

local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "usources" => normalizedUniformTupleSources
  (fun _ : Fin (j.val + 1) => S.value) (fun _ => S.positive) (fun _ => hsize)
local notation "pcoeff" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientSlot (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) b)

theorem allocatedActiveBlockSource_pair_law :
    ((weightedModerateIntegerSource csource usources).toPMF).map
      (fun x => ((x.1 none : ℤ), fun v q => (x.2 v q : ℤ))) =
      (pcoeff).bind (fun a => ((allocatedFrozenTupleWeights (α := α) B U basis S).toPMF).map
        (fun u => (a, fun v : Fin (j.val + 1) => fun q =>
          (u ⟨⟨⟨j, Sum.inr i⟩, hgrid⟩, b, v⟩ q : ℤ)))) := by
  rw [weightedModerateSource_integer_pair_law,
    allocatedPrincipalNormalizedSource_law B U basis hR hσ S j i hactive b]
  have hp := congrArg (fun p : PMF (Fin (j.val + 1) → Option α → ℤ) =>
    (pcoeff).bind (fun a => p.map (fun y => (a, y))))
    (allocatedFrozenTuple_active_normalized_block_law B U basis S j i hactive hgrid b hsize).symm
  simpa only [PMF.map_comp, Function.comp_def] using hp

theorem allocatedActiveBlockSource_jet_law (rows : Finset (Finset α)) :
    ((weightedModerateIntegerSource csource usources).toPMF).map
      (weightedModerateIntegerBlock csource usources rows 0) =
      (pcoeff).bind (fun a => ((allocatedFrozenTupleWeights (α := α) B U basis S).toPMF).map
        (fun u (r : rows) => a * integerBooleanBlockJet
          (fun v : Fin (j.val + 1) => fun q =>
            (u ⟨⟨⟨j, Sum.inr i⟩, hgrid⟩, b, v⟩ q : ℤ)) r)) := by
  have hp := congrArg (fun p : PMF (ℤ × (Fin (j.val + 1) → Option α → ℤ)) =>
    p.map (fun ay (r : rows) => ay.1 * integerBooleanBlockJet ay.2 r))
    (allocatedActiveBlockSource_pair_law B U basis hR hσ S j i hactive hgrid b hsize)
  rw [PMF.map_comp, PMF.map_bind] at hp
  change ((weightedModerateIntegerSource csource usources).toPMF).map
    (fun x (r : rows) => (0 + (x.1 none : ℤ)) *
      integerBooleanBlockJet (fun v q => (x.2 v q : ℤ)) r) = _
  simpa only [PMF.map_comp, Function.comp_def, zero_add] using hp

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
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (hsize : Fintype.card α + 1 ≤ S.value)

local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "usources" => normalizedUniformTupleSources
  (fun _ : Fin (j.val + 1) => S.value) (fun _ => S.positive) (fun _ => hsize)

theorem allocatedActiveAxisSource_jet_sum_law (rows : Finset (Finset α)) (shift : rows → ℤ) :
    ((weightedModerateIntegerProductSource
      (fun _ : B ⟨j, Sum.inr i⟩ => csource) (fun _ => usources)).toPMF).map
        (weightedModerateIntegerJetSum (fun _ => csource) (fun _ => usources)
          rows (fun _ => 0) shift) =
      (dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
        allocatedLayerIntegerPMFs B U basis hR hσ S j i
          (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))).bind
            (fun a => ((allocatedFrozenTupleWeights (α := α) B U basis S).toPMF).map
              (fun u => shift + ∑ b, fun r : rows => a b * integerBooleanBlockJet
                (fun v : Fin (j.val + 1) => fun q =>
                  (u ⟨⟨⟨j, Sum.inr i⟩, hgrid⟩, b, v⟩ q : ℤ)) r)) := by
  have hp := weightedModerateProductSource_jet_sum_law
    (fun _ : B ⟨j, Sum.inr i⟩ => csource) (fun _ => usources) rows (fun _ => 0) shift
  have hc :
      (dependentProductPMF (fun _ : B ⟨j, Sum.inr i⟩ =>
        (csource).source.toPMF.map (fun x => (x none : ℤ)))) =
      dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
        allocatedLayerIntegerPMFs B U basis hR hσ S j i
          (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b)) :=
    congrArg (fun p : B ⟨j, Sum.inr i⟩ → PMF ℤ => dependentProductPMF p)
      (funext (fun b => allocatedPrincipalNormalizedSource_law B U basis hR hσ S j i hactive b))
  rw [hc] at hp
  refine hp.trans ?_
  have ht := congrArg
    (fun p : PMF (B ⟨j, Sum.inr i⟩ → Fin (j.val + 1) → Option α → ℤ) =>
      (dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
        allocatedLayerIntegerPMFs B U basis hR hσ S j i
          (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))).bind
        (fun a => p.map (fun y => shift + ∑ b, fun r : rows =>
          a b * integerBooleanBlockJet (y b) r)))
    (allocatedFrozenTuple_active_axis_normalized_law B U basis S j i hactive hgrid hsize).symm
  simpa only [PMF.map_comp, Function.comp_def, zero_add] using ht

end Erdos3.VectorPolynomial

end

end OAI
