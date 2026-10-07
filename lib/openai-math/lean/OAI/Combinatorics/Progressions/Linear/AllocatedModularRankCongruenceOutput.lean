import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fintype.EquivFin
import OAI.Combinatorics.Progressions.Estimates.ModularMultilinearAmbientSublevel
import OAI.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

def canonicalRankBlockEmbedding (h : D → ℕ) (d : D) (b : B d) :
    Fin (h d) ↪ SamplerTupleIndex G B h where
  toFun v := .inr ⟨d, b, v⟩
  inj' := by intro v w he; simpa only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq,
    Prod.mk.injEq, true_and] using he

def canonicalRankBlock (h : D → ℕ) (d : D) (b : B d) :
    Finset (SamplerTupleIndex G B h) :=
  Finset.univ.map (canonicalRankBlockEmbedding h d b)

theorem canonicalRankBlock_card (h : D → ℕ) (d : D) (b : B d) :
    (canonicalRankBlock (G := G) h d b).card = h d := by
  simp only [canonicalRankBlock, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem mem_canonicalRankBlock (h : D → ℕ) (d : D) (b : B d)
    (k : SamplerTupleIndex G B h) :
    k ∈ canonicalRankBlock h d b ↔ ∃ v : Fin (h d), k = .inr ⟨d, b, v⟩ := by
  simp only [canonicalRankBlock, Finset.mem_map, Finset.mem_univ, true_and,
    canonicalRankBlockEmbedding, eq_comm]
  rfl

theorem canonicalRankBlock_pairwise_disjoint (h : D → ℕ) :
    Pairwise (fun a b : (Σ d, B d) =>
      Disjoint (canonicalRankBlock (G := G) h a.1 a.2)
        (canonicalRankBlock h b.1 b.2)) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro k hka hkb
  obtain ⟨v, hv⟩ := (mem_canonicalRankBlock h a.1 a.2 k).mp hka
  obtain ⟨w, hw⟩ := (mem_canonicalRankBlock h b.1 b.2 k).mp hkb
  have he : (Sum.inr ⟨a.1, a.2, v⟩ : SamplerTupleIndex G B h) = .inr ⟨b.1, b.2, w⟩ :=
    hv.symm.trans hw
  have hp := congrArg (fun t : SamplerTupleIndex G B h =>
    match t with
    | .inl _ => none
    | .inr t => some (⟨t.1, t.2.1⟩ : Σ d, B d)) he
  exact hab (Option.some.inj hp)

theorem canonicalRankBlock_disjoint (h : D → ℕ) (d : D) :
    Pairwise (fun b c : B d => Disjoint (canonicalRankBlock (G := G) h d b)
      (canonicalRankBlock h d c)) := by
  intro b c hbc
  apply canonicalRankBlock_pairwise_disjoint (G := G) h (i := ⟨d, b⟩) (j := ⟨d, c⟩)
  intro he
  apply hbc
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using he

theorem principalCoefficientSlot_eq_block_sum (h : D → ℕ) (d : D) (b : B d) :
    (principalCoefficientSlot (G := G) h d b).val =
      ∑ k ∈ canonicalRankBlock h d b, Finsupp.single k 1 := by
  simp only [principalCoefficientSlot, canonicalPrincipalExponent, productBlockExponent,
    canonicalRankBlock, Finset.sum_map, canonicalRankBlockEmbedding]
  rfl

theorem principalCoefficientSlot_monomial {R : Type*} [CommSemiring R]
    (h : D → ℕ) (d : D) (b : B d) (c : R) :
    MvPolynomial.monomial (principalCoefficientSlot (G := G) h d b).val c =
      MvPolynomial.C c * ∏ k ∈ canonicalRankBlock h d b, MvPolynomial.X k := by
  rw [principalCoefficientSlot_eq_block_sum, MvPolynomial.monomial_sum_index]
  rfl

theorem principalCoefficientSlot_squarefree (h : D → ℕ) (d : D) (b : B d) :
    SquarefreeExponent (principalCoefficientSlot (G := G) h d b).val := by
  intro k
  rw [principalCoefficientSlot_eq_block_sum, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  by_cases hk : k ∈ canonicalRankBlock (G := G) h d b
  · simp only [Finset.sum_ite_eq', hk, ite_true, le_refl]
  · simp only [Finset.sum_ite_eq', hk, ite_false, zero_le]

theorem principalCoefficientSlot_eq_squarefree [Fintype G] [Fintype D]
    [∀ d, Fintype (B d)] (h : D → ℕ) (d : D) (b : B d) :
    (principalCoefficientSlot (G := G) h d b).val =
      (SquarefreeIndex.ofFinset (canonicalRankBlock h d b)).val := by
  ext k
  rw [principalCoefficientSlot_eq_block_sum, Finsupp.finsetSum_apply,
    SquarefreeIndex.ofFinset_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq']

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
  {B : LayerSamplerAxis I n → Type*}

def allocatedRankBlockEmbedding (a : LayerSamplerAxis I n) (b : B a) :
    Fin (a.1.val + 1) ↪ LayerSamplerVariables G I n B :=
  canonicalRankBlockEmbedding (layerSamplerDegree I n) a b

def allocatedRankBlock (a : LayerSamplerAxis I n) (b : B a) :
    Finset (LayerSamplerVariables G I n B) :=
  canonicalRankBlock (layerSamplerDegree I n) a b

def allocatedRankSelected (a : LayerSamplerAxis I n) (b : B a) :
    LayerSamplerVariables G I n B :=
  allocatedRankBlockEmbedding a b 0

theorem allocatedRankSelected_mem (a : LayerSamplerAxis I n) (b : B a) :
    allocatedRankSelected (G := G) a b ∈ allocatedRankBlock a b := by
  exact Finset.mem_map.mpr ⟨⟨0, Nat.zero_lt_succ _⟩, Finset.mem_univ _, rfl⟩

theorem allocatedRankBlock_pairwise_disjoint :
    Pairwise (fun a b : (Σ a : LayerSamplerAxis I n, B a) =>
      Disjoint (allocatedRankBlock (G := G) a.1 a.2)
        (allocatedRankBlock b.1 b.2)) :=
  canonicalRankBlock_pairwise_disjoint _

theorem allocatedRankBlock_card (a : LayerSamplerAxis I n) (b : B a) :
    (allocatedRankBlock (G := G) a b).card = a.1.val + 1 :=
  canonicalRankBlock_card _ _ _

theorem allocatedRankBlock_disjoint (a : LayerSamplerAxis I n) :
    Pairwise (fun b c : B a => Disjoint (allocatedRankBlock (G := G) a b)
      (allocatedRankBlock a c)) :=
  canonicalRankBlock_disjoint _ _

theorem allocatedRankBlock_monomial {R : Type*} [CommSemiring R]
    (a : LayerSamplerAxis I n) (b : B a) (c : R) :
    MvPolynomial.monomial
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) a b).val c =
      MvPolynomial.C c * ∏ k ∈ allocatedRankBlock a b, MvPolynomial.X k :=
  principalCoefficientSlot_monomial _ _ _ _

theorem allocatedRankBlock_monomial_smul {R : Type*} [CommSemiring R]
    (a : LayerSamplerAxis I n) (b : B a) (c : R) :
    MvPolynomial.monomial
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) a b).val c =
      c • ∏ k ∈ allocatedRankBlock a b, MvPolynomial.X k := by
  rw [allocatedRankBlock_monomial, MvPolynomial.smul_eq_C_mul]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators Classical

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

def kernelRankBlockEmbedding (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A) :
    Fin h ↪ SamplerTupleIndex G B degree where
  toFun v := .inl (e (a, v))
  inj' := by
    intro v w he
    exact congrArg Prod.snd (e.injective (Sum.inl.inj he))

@[simp] theorem kernelRankBlockEmbedding_apply (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) (v : Fin h) :
    kernelRankBlockEmbedding (B := B) degree e a v = .inl (e (a, v)) := rfl

def kernelRankBlock (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A) :
    Finset (SamplerTupleIndex G B degree) :=
  Finset.univ.map (kernelRankBlockEmbedding degree e a)

theorem kernelRankBlock_eq_image (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A) :
    kernelRankBlock (B := B) degree e a =
      Finset.univ.image (fun v : Fin h => (Sum.inl (e (a, v)) : SamplerTupleIndex G B degree)) := by
  rw [kernelRankBlock, Finset.map_eq_image]
  rfl

theorem kernelRankBlock_card (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A) :
    (kernelRankBlock (B := B) degree e a).card = h := by
  simp only [kernelRankBlock, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem mem_kernelRankBlock (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A)
    (k : SamplerTupleIndex G B degree) :
    k ∈ kernelRankBlock degree e a ↔ ∃ v : Fin h, k = .inl (e (a, v)) := by
  simp only [kernelRankBlock, Finset.mem_map, Finset.mem_univ, true_and,
    kernelRankBlockEmbedding, eq_comm]
  rfl

theorem kernelRankBlock_pairwise_disjoint (degree : D → ℕ) (e : A × Fin h ↪ G) :
    Pairwise (fun a b : A => Disjoint (kernelRankBlock (B := B) degree e a)
      (kernelRankBlock degree e b)) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro k hka hkb
  obtain ⟨v, hv⟩ := (mem_kernelRankBlock degree e a k).mp hka
  obtain ⟨w, hw⟩ := (mem_kernelRankBlock degree e b k).mp hkb
  exact hab (congrArg Prod.fst (e.injective (Sum.inl.inj (hv.symm.trans hw))))

theorem kernelRankBlock_disjoint_canonicalRankBlock (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) (d : D) (b : B d) :
    Disjoint (kernelRankBlock degree e a) (canonicalRankBlock degree d b) := by
  apply Finset.disjoint_left.mpr
  intro k hk hp
  obtain ⟨v, hv⟩ := (mem_kernelRankBlock degree e a k).mp hk
  obtain ⟨w, hw⟩ := (mem_canonicalRankBlock degree d b k).mp hp
  exact Sum.inl_ne_inr (hv.symm.trans hw)

noncomputable def kernelRankCoefficientSlot (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) :
    BoundedCoefficientExponent (SamplerTupleIndex G B degree) h :=
  ⟨productBlockExponent (kernelRankBlockEmbedding degree e a),
    (productBlockExponent_degree _).le⟩

theorem kernelRankCoefficientSlot_degree (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) :
    (kernelRankCoefficientSlot (B := B) degree e a).val.degree = h :=
  productBlockExponent_degree _

theorem kernelRankCoefficientSlot_eq_block_sum (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) :
    (kernelRankCoefficientSlot (B := B) degree e a).val =
      ∑ k ∈ kernelRankBlock degree e a, Finsupp.single k 1 := by
  simp only [kernelRankCoefficientSlot, productBlockExponent, kernelRankBlock,
    Finset.sum_map]

theorem kernelRankCoefficientSlot_apply (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a b : A) (v : Fin h) :
    (kernelRankCoefficientSlot (B := B) degree e a).val (.inl (e (b, v))) =
      if a = b then 1 else 0 := by
  by_cases hab : a = b <;>
    simp [kernelRankCoefficientSlot, productBlockExponent,
      Finsupp.single_apply, e.injective.eq_iff, hab]

theorem kernelRankCoefficientSlot_injective (degree : D → ℕ)
    (e : A × Fin h ↪ G) (hh : 0 < h) :
    Function.Injective (kernelRankCoefficientSlot (B := B) degree e) := by
  intro a b he
  have hv := congrArg (fun q : BoundedCoefficientExponent (SamplerTupleIndex G B degree) h =>
    q.val (.inl (e (b, ⟨0, hh⟩)))) he
  rw [kernelRankCoefficientSlot_apply, kernelRankCoefficientSlot_apply] at hv
  by_contra hab
  simp [hab] at hv

theorem kernelRankCoefficientSlot_monomial {R : Type*} [CommSemiring R]
    (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A) (c : R) :
    MvPolynomial.monomial (kernelRankCoefficientSlot (B := B) degree e a).val c =
      c • ∏ k ∈ kernelRankBlock degree e a, MvPolynomial.X k := by
  rw [kernelRankCoefficientSlot_eq_block_sum, MvPolynomial.monomial_sum_index,
    MvPolynomial.smul_eq_C_mul]
  rfl

theorem kernelRankCoefficientSlot_squarefree (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) :
    SquarefreeExponent (kernelRankCoefficientSlot (B := B) degree e a).val := by
  intro k
  rw [kernelRankCoefficientSlot_eq_block_sum, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq']
  split_ifs <;> omega

theorem kernelRankCoefficientSlot_eq_squarefree [Fintype G] [Fintype D]
    [∀ d, Fintype (B d)] (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A) :
    (kernelRankCoefficientSlot (B := B) degree e a).val =
      (SquarefreeIndex.ofFinset (kernelRankBlock degree e a)).val := by
  ext k
  rw [kernelRankCoefficientSlot_eq_block_sum, Finsupp.finsetSum_apply,
    SquarefreeIndex.ofFinset_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq']

theorem exists_kernelRankEmbedding [Fintype A] [Fintype G]
    (hcap : Fintype.card A * h ≤ Fintype.card G) : Nonempty (A × Fin h ↪ G) := by
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_prod, Fintype.card_fin] using hcap

noncomputable def kernelRankEmbeddingOfCapacity [Fintype A] [Fintype G]
    (hcap : Fintype.card A * h ≤ Fintype.card G) : A × Fin h ↪ G :=
  Classical.choice (exists_kernelRankEmbedding hcap)

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

abbrev SamplerLongVariables (inactive : D → Prop) (G : Type*) (B : D → Type*)
    (h : D → ℕ) :=
  SamplerTupleIndex G (fun d : {d // ¬ inactive d} => B d.val) (fun d => h d.val)

def samplerLongEmbedding (inactive : D → Prop) (h : D → ℕ) :
    SamplerLongVariables inactive G B h ↪ SamplerTupleIndex G B h :=
  Function.Embedding.sumMap (Function.Embedding.refl G)
    (Function.Embedding.sigmaMap (Function.Embedding.subtype (fun d => ¬ inactive d))
      (fun _ => Function.Embedding.refl _))

@[simp] theorem samplerLongEmbedding_common (inactive : D → Prop) (h : D → ℕ) (g : G) :
    samplerLongEmbedding (B := B) inactive h (.inl g) = .inl g := rfl

@[simp] theorem samplerLongEmbedding_dedicated (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) (b : B d.val) (v : Fin (h d.val)) :
    samplerLongEmbedding (G := G) inactive h (.inr ⟨d, b, v⟩) =
      .inr ⟨d.val, b, v⟩ := rfl

theorem samplerLongEmbedding_common_mem_range (inactive : D → Prop) (h : D → ℕ) (g : G) :
    (Sum.inl g : SamplerTupleIndex G B h) ∈ Set.range (samplerLongEmbedding inactive h) :=
  ⟨.inl g, rfl⟩

theorem samplerLongEmbedding_dedicated_mem_range (inactive : D → Prop) (h : D → ℕ)
    (d : D) (b : B d) (v : Fin (h d)) :
    (Sum.inr ⟨d, b, v⟩ : SamplerTupleIndex G B h) ∈
      Set.range (samplerLongEmbedding inactive h) ↔ ¬ inactive d := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with g | ⟨a, c, w⟩
    · simp only [samplerLongEmbedding_common, Sum.inl_ne_inr] at hk
    · have he : a.val = d := congrArg Sigma.fst (Sum.inr.inj hk)
      exact he ▸ a.property
  · intro hd
    exact ⟨.inr ⟨⟨d, hd⟩, b, v⟩, rfl⟩

theorem samplerLongEmbedding_block (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) (b : B d.val) :
    (canonicalRankBlock (G := G) (B := fun a : {a // ¬ inactive a} => B a.val)
      (fun a => h a.val) d b).map (samplerLongEmbedding inactive h) =
        canonicalRankBlock h d.val b := by
  simp only [canonicalRankBlock, Finset.map_map]
  congr 1

theorem samplerLongEmbedding_principalExponent (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) (b : B d.val) :
    ((principalCoefficientSlot (G := G) (B := fun a : {a // ¬ inactive a} => B a.val)
      (fun a => h a.val) d b).val).mapDomain (samplerLongEmbedding inactive h) =
        (principalCoefficientSlot h d.val b).val := by
  simp only [principalCoefficientSlot, canonicalPrincipalExponent, productBlockExponent,
    Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single, samplerLongEmbedding_dedicated]

section TopPart

variable {I J R : Type*} [CommRing R]

theorem homogeneousComponent_killCompl (f : J → I) (hf : Function.Injective f)
    (P : MvPolynomial I R) (r : ℕ) :
    homogeneousComponent r (killCompl hf P) = killCompl hf (homogeneousComponent r P) := by
  ext a
  simp only [coeff_homogeneousComponent, coeff_killCompl, Finsupp.degree_mapDomain]

theorem homogeneousComponent_polynomialTranslate_top (P : MvPolynomial I R)
    (v : I → R) (r : ℕ) (hP : P.totalDegree ≤ r) :
    homogeneousComponent r (polynomialTranslate v P) = homogeneousComponent r P := by
  ext a
  simp only [coeff_homogeneousComponent]
  split_ifs with ha
  · exact top_coeff_polynomialTranslate P v a (ha.symm ▸ hP)
  · rfl

theorem homogeneousComponent_restricted_translate_top (f : J → I)
    (hf : Function.Injective f) (P : MvPolynomial I R) (v : I → R)
    (r : ℕ) (hP : P.totalDegree ≤ r) :
    homogeneousComponent r (killCompl hf (polynomialTranslate v P)) =
      killCompl hf (homogeneousComponent r P) := by
  rw [homogeneousComponent_killCompl, homogeneousComponent_polynomialTranslate_top P v r hP]

theorem homogeneousComponent_conditionPolynomial_top (f : J → I)
    (hf : Function.Injective f) (P : MvPolynomial I R) (v : I → R)
    (r : ℕ) (hP : P.totalDegree ≤ r) :
    homogeneousComponent r (conditionPolynomial f hf v P) =
      killCompl hf (homogeneousComponent r P) :=
  homogeneousComponent_restricted_translate_top f hf P _ r hP

end TopPart

theorem samplerLong_principal_coefficient {R : Type*} [CommRing R]
    (inactive : D → Prop) (h : D → ℕ) (d : {d // ¬ inactive d}) (b : B d.val)
    (P : MvPolynomial (SamplerTupleIndex G B h) R)
    (v : SamplerTupleIndex G B h → R) (hP : P.totalDegree ≤ h d.val) :
    (conditionPolynomial (samplerLongEmbedding inactive h)
      (samplerLongEmbedding inactive h).injective v P).coeff
        (principalCoefficientSlot (G := G) (B := fun a : {a // ¬ inactive a} => B a.val)
          (fun a => h a.val) d b).val =
      P.coeff (principalCoefficientSlot h d.val b).val := by
  rw [coeff_conditionPolynomial_top, samplerLongEmbedding_principalExponent]
  simpa only [principalCoefficientSlot, canonicalPrincipalExponent_degree] using hP

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev LayerSamplerLongVariables (inactive : LayerSamplerAxis I n → Prop)
    (G : Type*) (B : LayerSamplerAxis I n → Type*) :=
  SamplerLongVariables inactive G B (layerSamplerDegree I n)

def allocatedLongEmbedding (inactive : LayerSamplerAxis I n → Prop) :
    LayerSamplerLongVariables inactive G B ↪ LayerSamplerVariables G I n B :=
  samplerLongEmbedding inactive (layerSamplerDegree I n)

theorem allocatedLong_top_independent {R : Type*} [CommRing R]
    (inactive : LayerSamplerAxis I n → Prop)
    (P : MvPolynomial (LayerSamplerVariables G I n B) R)
    (v : LayerSamplerVariables G I n B → R) (j : Fin m)
    (hP : P.totalDegree ≤ j.val + 1) :
    homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v P) =
      killCompl (allocatedLongEmbedding inactive).injective
        (homogeneousComponent (j.val + 1) P) :=
  homogeneousComponent_conditionPolynomial_top _ _ P v _ hP

theorem allocatedLong_top_origin_independent {R : Type*} [CommRing R]
    (inactive : LayerSamplerAxis I n → Prop)
    (P : MvPolynomial (LayerSamplerVariables G I n B) R)
    (origin : LayerSamplerVariables G I n B → R) (j : Fin m)
    (hP : P.totalDegree ≤ j.val + 1) :
    homogeneousComponent (j.val + 1)
      (killCompl (allocatedLongEmbedding inactive).injective (polynomialTranslate origin P)) =
      killCompl (allocatedLongEmbedding inactive).injective
        (homogeneousComponent (j.val + 1) P) :=
  homogeneousComponent_restricted_translate_top _ _ P origin _ hP

theorem allocatedLongEmbedding_block (inactive : LayerSamplerAxis I n → Prop)
    (a : {a // ¬ inactive a}) (b : B a.val) :
    (canonicalRankBlock (G := G) (B := fun c : {c // ¬ inactive c} => B c.val)
      (fun c => c.val.1.val + 1) a b).map (allocatedLongEmbedding inactive) =
        allocatedRankBlock a.val b :=
  samplerLongEmbedding_block inactive (layerSamplerDegree I n) a b

theorem allocatedLong_principal_coefficient {R : Type*} [CommRing R]
    (inactive : LayerSamplerAxis I n → Prop) (a : {a // ¬ inactive a}) (b : B a.val)
    (P : MvPolynomial (LayerSamplerVariables G I n B) R)
    (v : LayerSamplerVariables G I n B → R) (hP : P.totalDegree ≤ a.val.1.val + 1) :
    (conditionPolynomial (allocatedLongEmbedding inactive)
      (allocatedLongEmbedding inactive).injective v P).coeff
        (principalCoefficientSlot (G := G) (B := fun c : {c // ¬ inactive c} => B c.val)
          (fun c => c.val.1.val + 1) a b).val =
      P.coeff (principalCoefficientSlot (layerSamplerDegree I n) a.val b).val :=
  samplerLong_principal_coefficient inactive (layerSamplerDegree I n) a b P v hP

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev AllocatedDegreeActiveAxis (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  {a : I j ⊕ Fin (n j) // ¬ inactive ⟨j, a⟩}

abbrev AllocatedDegreeRankOutput (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  E j ⊕ AllocatedDegreeActiveAxis inactive j

def allocatedDegreeLongAxis (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (a : AllocatedDegreeActiveAxis inactive j) : {a // ¬ inactive a} :=
  ⟨⟨j, a.val⟩, a.property⟩

def allocatedDegreeRankBlock (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedDegreeRankOutput E inactive j → Fin L →
      Finset (LayerSamplerLongVariables inactive G B)
  | .inl _, l => kernelRankBlock (fun a : {a : LayerSamplerAxis I n // ¬ inactive a} => a.val.1.val + 1) kernel l
  | .inr a, l => canonicalRankBlock (fun a : {a : LayerSamplerAxis I n // ¬ inactive a} => a.val.1.val + 1)
      (allocatedDegreeLongAxis inactive j a) (block a l)

theorem allocatedDegreeRankBlock_card (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (o : AllocatedDegreeRankOutput E inactive j) (l : Fin L) :
    (allocatedDegreeRankBlock (E := E) inactive j kernel block o l).card = j.val + 1 := by
  cases o with
  | inl e => exact kernelRankBlock_card _ _ _
  | inr a => exact canonicalRankBlock_card _ _ _

theorem allocatedDegreeRankBlock_disjoint (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (o : AllocatedDegreeRankOutput E inactive j) :
    Pairwise (fun l q => Disjoint (allocatedDegreeRankBlock (E := E) inactive j kernel block o l)
      (allocatedDegreeRankBlock (E := E) inactive j kernel block o q)) := by
  cases o with
  | inl e => exact kernelRankBlock_pairwise_disjoint _ _
  | inr a =>
    intro l q hlq
    exact canonicalRankBlock_disjoint _ _ ((block a).injective.ne hlq)

def allocatedDegreeRankSelected (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedDegreeRankOutput E inactive j → Fin L → LayerSamplerLongVariables inactive G B
  | .inl _, l => .inl (kernel (l, 0))
  | .inr a, l => .inr ⟨allocatedDegreeLongAxis inactive j a, block a l, ⟨0, Nat.zero_lt_succ _⟩⟩

theorem allocatedDegreeRankSelected_mem (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (o : AllocatedDegreeRankOutput E inactive j) (l : Fin L) :
    allocatedDegreeRankSelected inactive j kernel block o l ∈
      allocatedDegreeRankBlock (E := E) inactive j kernel block o l := by
  cases o with
  | inl e => exact (mem_kernelRankBlock _ _ _ _).mpr ⟨0, rfl⟩
  | inr a => exact (mem_canonicalRankBlock _ _ _ _).mpr ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩

theorem allocatedDegreeRankBlock_deck_projection_disjoint
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (e : E j) (a : AllocatedDegreeActiveAxis inactive j) (l q : Fin L) :
    Disjoint (allocatedDegreeRankBlock (E := E) inactive j kernel block (.inl e) l)
      (allocatedDegreeRankBlock (E := E) inactive j kernel block (.inr a) q) :=
  kernelRankBlock_disjoint_canonicalRankBlock _ _ _ _ _

theorem allocatedDegreeRankOutput_card_le [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    Fintype.card (AllocatedDegreeRankOutput E inactive j) ≤
      Fintype.card (E j) + Fintype.card (I j) + n j := by
  change Fintype.card (E j ⊕ AllocatedDegreeActiveAxis inactive j) ≤ _
  rw [Fintype.card_sum, add_assoc]
  apply Nat.add_le_add_left
  exact (Fintype.card_subtype_le _).trans_eq (by
    simp only [Fintype.card_sum, Fintype.card_fin])

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MvPolynomial VectorPolynomial
open scoped BigOperators Classical

variable {D G R : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R]

noncomputable def canonicalPrincipalSubblockSlot (h : D → ℕ) (d : D) {J : ℕ}
    (block : Fin J ↪ B d) :
    Fin J → BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) :=
  fun j => principalCoefficientSlot h d (block j)

omit [Fintype D] [Fintype G] [∀ d, Fintype (B d)] in
theorem canonicalPrincipalSubblockSlot_injective (h : D → ℕ) (d : D) (hd : 0 < h d)
    {J : ℕ} (block : Fin J ↪ B d) :
    Function.Injective (canonicalPrincipalSubblockSlot (G := G) h d block) :=
  (principalCoefficientSlot_injective h d hd).comp block.injective

omit [Fintype D] [Fintype G] [∀ d, Fintype (B d)] in
theorem canonicalPrincipalSubblockSlot_degree (h : D → ℕ) (d : D) {J : ℕ}
    (block : Fin J ↪ B d) (j : Fin J) :
    (canonicalPrincipalSubblockSlot (G := G) h d block j).val.degree = h d :=
  canonicalPrincipalExponent_degree h d (block j)

noncomputable def canonicalSelectedTopResidual (h : D → ℕ) (d : D) {J : ℕ}
    (block : Fin J ↪ B d)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → R) :
    MvPolynomial (SamplerTupleIndex G B h) R :=
  homogeneousComponent (h d) (modularUnselectedCoefficientPolynomial (h d)
    (canonicalPrincipalSubblockSlot h d block) fixed)

theorem canonicalBoundedCoefficient_selected_top (h : D → ℕ) (d : D) (hd : 0 < h d)
    {J : ℕ} (block : Fin J ↪ B d)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → R)
    (c : Fin J → R) :
    homogeneousComponent (h d) (modularBoundedCoefficientPolynomial (h d)
      (Function.extend (canonicalPrincipalSubblockSlot h d block) c fixed)) =
      canonicalSelectedTopResidual h d block fixed +
        ∑ j, c j • ∏ k ∈ canonicalRankBlock h d (block j), X k := by
  rw [modularBoundedCoefficientPolynomial_selected_top (h d) _
    (canonicalPrincipalSubblockSlot_injective h d hd block)
    (canonicalPrincipalSubblockSlot_degree h d block)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [canonicalPrincipalSubblockSlot, principalCoefficientSlot_monomial, smul_eq_C_mul]

omit [Fintype D] [Fintype G] [∀ d, Fintype (B d)] in

theorem samplerLong_killCompl_principal_monomial (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) (b : B d.val) (c : R) :
    killCompl (samplerLongEmbedding (G := G) inactive h).injective
      (monomial (principalCoefficientSlot h d.val b).val c) =
      c • ∏ k ∈ canonicalRankBlock (G := G)
        (B := fun a : {a // ¬ inactive a} => B a.val) (fun a => h a.val) d b, X k := by
  rw [← samplerLongEmbedding_principalExponent inactive h d b,
    killCompl_monomial_mapDomain, principalCoefficientSlot_monomial, smul_eq_C_mul]

noncomputable def canonicalSelectedLongTopResidual (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) {J : ℕ} (block : Fin J ↪ B d.val)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d.val) → R) :
    MvPolynomial (SamplerLongVariables inactive G B h) R :=
  killCompl (samplerLongEmbedding inactive h).injective
    (canonicalSelectedTopResidual h d.val block fixed)

theorem canonicalBoundedCoefficient_selected_long_top (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) (hd : 0 < h d.val) {J : ℕ} (block : Fin J ↪ B d.val)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d.val) → R)
    (c : Fin J → R) (v : SamplerTupleIndex G B h → R) :
    homogeneousComponent (h d.val)
      (conditionPolynomial (samplerLongEmbedding inactive h)
        (samplerLongEmbedding inactive h).injective v
        (modularBoundedCoefficientPolynomial (h d.val)
          (Function.extend (canonicalPrincipalSubblockSlot h d.val block) c fixed))) =
      canonicalSelectedLongTopResidual inactive h d block fixed +
        ∑ j, c j • ∏ k ∈ canonicalRankBlock (G := G)
          (B := fun a : {a // ¬ inactive a} => B a.val)
          (fun a => h a.val) d (block j), X k := by
  have hdegree : (modularBoundedCoefficientPolynomial (h d.val)
      (Function.extend (canonicalPrincipalSubblockSlot h d.val block) c fixed)).totalDegree ≤
        h d.val := by
    apply totalDegree_finsetSum_le
    intro e _
    exact (totalDegree_monomial_le e.val _).trans e.property
  rw [homogeneousComponent_conditionPolynomial_top _ _ _ v (h d.val) hdegree,
    modularBoundedCoefficientPolynomial_selected_top (h d.val) _
      (canonicalPrincipalSubblockSlot_injective h d.val hd block)
      (canonicalPrincipalSubblockSlot_degree h d.val block), map_add, map_sum]
  change canonicalSelectedLongTopResidual inactive h d block fixed + _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact samplerLong_killCompl_principal_monomial inactive h d (block j) (c j)

theorem canonicalBoundedInteger_selected_long_top (N : ℕ) (inactive : D → Prop)
    (h : D → ℕ) (d : {d // ¬ inactive d}) (hd : 0 < h d.val)
    {J : ℕ} (block : Fin J ↪ B d.val)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d.val) → ℤ)
    (c : Fin J → ℤ) (v : SamplerTupleIndex G B h → ZMod N) :
    homogeneousComponent (h d.val)
      (conditionPolynomial (samplerLongEmbedding inactive h)
        (samplerLongEmbedding inactive h).injective v
        ((integerMonomialArrayPolynomial Subtype.val
          (Function.extend (canonicalPrincipalSubblockSlot h d.val block) c fixed)).map
            (Int.castRingHom (ZMod N)))) =
      canonicalSelectedLongTopResidual inactive h d block (fun e => (fixed e : ZMod N)) +
        ∑ j, (c j : ZMod N) • ∏ k ∈ canonicalRankBlock (G := G)
          (B := fun a : {a // ¬ inactive a} => B a.val)
          (fun a => h a.val) d (block j), X k := by
  rw [← modularBoundedCoefficientPolynomial_integer_reduce]
  have hi := canonicalPrincipalSubblockSlot_injective (G := G) h d.val hd block
  have he : (fun e => ((Function.extend (canonicalPrincipalSubblockSlot h d.val block)
      c fixed e : ℤ) : ZMod N)) =
      Function.extend (canonicalPrincipalSubblockSlot h d.val block)
        (fun j => (c j : ZMod N)) (fun e => (fixed e : ZMod N)) := by
    funext e
    by_cases he : e ∈ Set.range (canonicalPrincipalSubblockSlot (G := G) h d.val block)
    · obtain ⟨j, rfl⟩ := he
      simp only [hi.extend_apply]
    · simp only [Function.extend_apply' _ _ _ he]
  rw [he]
  exact canonicalBoundedCoefficient_selected_long_top inactive h d hd block
    (fun e => (fixed e : ZMod N)) (fun j => (c j : ZMod N)) v

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]

theorem allocatedBoundedCoefficient_selected_long_top
    (inactive : LayerSamplerAxis I n → Prop) (a : {a // ¬ inactive a})
    {J : ℕ} (block : Fin J ↪ B a.val)
    (fixed : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (a.val.1.val + 1) → R)
    (c : Fin J → R) (v : LayerSamplerVariables G I n B → R) :
    homogeneousComponent (a.val.1.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (a.val.1.val + 1)
          (Function.extend (canonicalPrincipalSubblockSlot (layerSamplerDegree I n) a.val block)
            c fixed))) =
      canonicalSelectedLongTopResidual inactive (layerSamplerDegree I n) a block fixed +
        ∑ j, c j • ∏ k ∈ canonicalRankBlock (G := G)
          (B := fun b : {b // ¬ inactive b} => B b.val)
          (fun b => b.val.1.val + 1) a (block j), X k :=
  canonicalBoundedCoefficient_selected_long_top inactive (layerSamplerDegree I n) a
    (Nat.zero_lt_succ _) block fixed c v

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev SpatialDegreeOutput (X : Type*) (j : Fin m) := {_x : X // j.val = 0}

abbrev AllocatedTaggedRankOutput (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  SpatialDegreeOutput X j ⊕ AllocatedDegreeRankOutput E inactive j

def allocatedSpatialRankBlock (inactive : LayerSamplerAxis I n → Prop)
    {L : ℕ} (spatial : Fin L ↪ G) (l : Fin L) :
    Finset (LayerSamplerLongVariables inactive G B) :=
  {.inl (spatial l)}

def allocatedTaggedRankBlock (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedTaggedRankOutput X E inactive j → Fin L →
      Finset (LayerSamplerLongVariables inactive G B)
  | .inl _, l => allocatedSpatialRankBlock inactive spatial l
  | .inr o, l => allocatedDegreeRankBlock inactive j kernel block o l

theorem allocatedTaggedRankBlock_card (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (o : AllocatedTaggedRankOutput X E inactive j) (l : Fin L) :
    (allocatedTaggedRankBlock inactive j spatial kernel block o l).card = j.val + 1 := by
  cases o with
  | inl x => simp only [allocatedTaggedRankBlock, allocatedSpatialRankBlock,
      Finset.card_singleton, x.property, zero_add]
  | inr o => exact allocatedDegreeRankBlock_card inactive j kernel block o l

theorem allocatedTaggedRankBlock_disjoint (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (o : AllocatedTaggedRankOutput X E inactive j) :
    Pairwise (fun l q => Disjoint (allocatedTaggedRankBlock inactive j spatial kernel block o l)
      (allocatedTaggedRankBlock inactive j spatial kernel block o q)) := by
  cases o with
  | inl x =>
    intro l q hlq
    apply Finset.disjoint_singleton.mpr
    exact fun he => hlq (spatial.injective (Sum.inl.inj he))
  | inr o => exact allocatedDegreeRankBlock_disjoint inactive j kernel block o

def allocatedTaggedRankSelected (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedTaggedRankOutput X E inactive j → Fin L → LayerSamplerLongVariables inactive G B
  | .inl _, l => .inl (spatial l)
  | .inr o, l => allocatedDegreeRankSelected inactive j kernel block o l

theorem allocatedTaggedRankSelected_mem (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (o : AllocatedTaggedRankOutput X E inactive j) (l : Fin L) :
    allocatedTaggedRankSelected inactive j spatial kernel block o l ∈
      allocatedTaggedRankBlock inactive j spatial kernel block o l := by
  cases o with
  | inl x => exact Finset.mem_singleton_self _
  | inr o => exact allocatedDegreeRankSelected_mem inactive j kernel block o l

theorem allocatedSpatialRankBlock_product {R : Type*} [CommSemiring R]
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G) (l : Fin L) :
    (∏ k ∈ allocatedSpatialRankBlock (B := B) inactive spatial l,
      MvPolynomial.X k : MvPolynomial (LayerSamplerLongVariables inactive G B) R) =
        MvPolynomial.X (.inl (spatial l)) := by
  rw [allocatedSpatialRankBlock, Finset.prod_singleton]

theorem spatialDegreeOutput_card [Fintype X] (j : Fin m) :
    Fintype.card (SpatialDegreeOutput X j) = if j.val = 0 then Fintype.card X else 0 := by
  rw [Fintype.card_subtype]
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false, Finset.filter_true,
    Finset.filter_false, Finset.card_univ, Finset.card_empty]

theorem allocatedTaggedRankOutput_card_le [Fintype X]
    [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    Fintype.card (AllocatedTaggedRankOutput X E inactive j) ≤
      Fintype.card X + (Fintype.card (E j) + Fintype.card (I j) + n j) := by
  change Fintype.card (SpatialDegreeOutput X j ⊕ AllocatedDegreeRankOutput E inactive j) ≤ _
  rw [Fintype.card_sum]
  exact Nat.add_le_add (Fintype.card_subtype_le _) (allocatedDegreeRankOutput_card_le (E := E) inactive j)

theorem spatialDegreeOutput_sum_card [Fintype X] (hm : 0 < m) :
    (∑ j : Fin m, Fintype.card (SpatialDegreeOutput X j)) = Fintype.card X := by
  simp_rw [spatialDegreeOutput_card]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · rfl
  · intro j _ hj
    have hne : j.val ≠ 0 := fun he => hj (Fin.ext he)
    simp only [hne, ite_false]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

theorem allocatedTaggedRankOutput_sum_card_le [Fintype X]
    [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] (hm : 0 < m)
    (inactive : LayerSamplerAxis I n → Prop) :
    (∑ j : Fin m, Fintype.card (AllocatedTaggedRankOutput X E inactive j)) ≤
      Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + Fintype.card (I j) + n j) := by
  simp only [AllocatedTaggedRankOutput, Fintype.card_sum, Finset.sum_add_distrib]
  rw [spatialDegreeOutput_sum_card hm]
  simpa only [AllocatedDegreeRankOutput, Fintype.card_sum, Finset.sum_add_distrib] using
    Nat.add_le_add_left (Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      allocatedDegreeRankOutput_card_le (E := E) inactive j)) (Fintype.card X)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

abbrev AllocatedCongruenceIntegerAxis (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  {i : Fin (n j) // ¬ inactive ⟨j, Sum.inr i⟩}

abbrev AllocatedCongruenceRankOutput (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  SpatialDegreeOutput X j ⊕ (E j ⊕ AllocatedCongruenceIntegerAxis inactive j)

def allocatedCongruenceIntegerEmbedding (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    AllocatedCongruenceIntegerAxis inactive j ↪ AllocatedDegreeActiveAxis inactive j where
  toFun i := ⟨Sum.inr i.val, i.property⟩
  inj' := by
    intro i k he
    apply Subtype.ext
    exact Sum.inr.inj (congrArg Subtype.val he)

def allocatedCongruenceOutputEmbedding (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    AllocatedCongruenceRankOutput X E inactive j ↪ AllocatedTaggedRankOutput X E inactive j :=
  Function.Embedding.sumMap (Function.Embedding.refl _)
    (Function.Embedding.sumMap (Function.Embedding.refl _)
      (allocatedCongruenceIntegerEmbedding inactive j))

@[simp] theorem allocatedCongruenceOutputEmbedding_spatial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) (x : SpatialDegreeOutput X j) :
    allocatedCongruenceOutputEmbedding (E := E) inactive j (.inl x) = .inl x := rfl

@[simp] theorem allocatedCongruenceOutputEmbedding_deck
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) (e : E j) :
    allocatedCongruenceOutputEmbedding (X := X) inactive j (.inr (.inl e)) = .inr (.inl e) := rfl

@[simp] theorem allocatedCongruenceOutputEmbedding_integer
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) (i : AllocatedCongruenceIntegerAxis inactive j) :
    allocatedCongruenceOutputEmbedding (X := X) (E := E) inactive j (.inr (.inr i)) =
      .inr (.inr ⟨Sum.inr i.val, i.property⟩) := rfl

theorem allocatedCongruenceRankOutput_card_le [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    Fintype.card (AllocatedCongruenceRankOutput X E inactive j) ≤
      Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j) := by
  change Fintype.card (SpatialDegreeOutput X j ⊕
    (E j ⊕ AllocatedCongruenceIntegerAxis inactive j)) ≤ _
  simp only [Fintype.card_sum]
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  simpa only [Fintype.card_fin] using Fintype.card_subtype_le
    (fun i : Fin (n j) => ¬ inactive ⟨j, Sum.inr i⟩)

theorem allocatedCongruenceRankOutput_sum_card_le [Fintype X] [∀ j, Fintype (E j)]
    (hm : 0 < m) (inactive : LayerSamplerAxis I n → Prop) :
    (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput X E inactive j)) ≤
      Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) := by
  calc
    _ ≤ ∑ j : Fin m,
        (Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j)) :=
      Finset.sum_le_sum (fun j _ => allocatedCongruenceRankOutput_card_le inactive j)
    _ = _ := by rw [Finset.sum_add_distrib, spatialDegreeOutput_sum_card hm]

theorem allocatedCongruenceRankOutput_sum_card_le_uniform [Fintype X] [∀ j, Fintype (E j)]
    (hm : 0 < m) (inactive : LayerSamplerAxis I n → Prop) (M : ℕ)
    (hM : ∀ j, Fintype.card (E j) + n j ≤ M) :
    (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput X E inactive j)) ≤
      Fintype.card X + m * M := by
  apply (allocatedCongruenceRankOutput_sum_card_le hm inactive).trans
  apply Nat.add_le_add_left
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hM j)

theorem preparedCongruenceRankOutput_sum_card_le {X₀ J₀ : Type}
    [Fintype X] [∀ j, Fintype (E j)] (prep : RankPreparationFamily X₀ J₀ m)
    (hm : 0 < m)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) → Prop)
    {M : ℕ} (hM : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hE : ∀ j, Fintype.card (E j) ≤ Fintype.card (PreparedSamplerContinuous prep j)) :
    (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput X E inactive j)) ≤
      Fintype.card X + m * M := by
  apply allocatedCongruenceRankOutput_sum_card_le_uniform hm inactive M
  intro j
  calc
    Fintype.card (E j) + preparedSamplerTransverse prep j ≤
        Fintype.card (PreparedSamplerContinuous prep j) + preparedSamplerTransverse prep j :=
      Nat.add_le_add_right (hE j) _
    _ = Fintype.card (prep j).Coord := preparedSampler_axis_card prep j
    _ ≤ M := hM j

theorem preparedCongruenceRankOutput_sum_card_fin_le {X₀ J₀ : Type} {nX : ℕ}
    [∀ j, Fintype (E j)] (prep : RankPreparationFamily X₀ J₀ m)
    (hm : 0 < m)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) → Prop)
    {M : ℕ} (hM : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hE : ∀ j, Fintype.card (E j) ≤ Fintype.card (PreparedSamplerContinuous prep j)) :
    (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput (Fin nX) E inactive j)) ≤
      nX + m * M := by
  simpa only [Fintype.card_fin] using
    preparedCongruenceRankOutput_sum_card_le (X := Fin nX) prep hm inactive hM hE

end Erdos3.VectorPolynomial

end

end OAI
