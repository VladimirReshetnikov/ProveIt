import OAI.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability

namespace OAI

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators Matrix

theorem modularBoundedCoefficientPolynomial_booleanCoefficient
    {α K O : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h N : ℕ)
    (rows : O → Finset α) (c : BoundedCoefficientExponent K h → ZMod N) (t : O) :
    booleanCoefficient (fun s => MvPolynomial.eval
      (fun k => (integerAffineCube root D s k : ZMod N))
      (modularBoundedCoefficientPolynomial h c)) (rows t) =
      ∑ e, (boundedCoefficientJetMatrix root D h rows t e : ZMod N) * c e := by
  classical
  simp only [modularBoundedCoefficientPolynomial, map_sum, MvPolynomial.eval_monomial]
  rw [booleanCoefficient_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [booleanCoefficient_const_mul]
  rw [mul_comm]
  congr 1
  change booleanCoefficient (fun s => e.val.prod
    (fun k n => (integerAffineCube root D s k : ZMod N) ^ n)) (rows t) =
    ((booleanCoefficient (fun s => MvPolynomial.eval (integerAffineCube root D s)
      (MvPolynomial.monomial e.val (1 : ℤ))) (rows t) : ℤ) : ZMod N)
  rw [show ((booleanCoefficient (fun s => MvPolynomial.eval (integerAffineCube root D s)
      (MvPolynomial.monomial e.val (1 : ℤ))) (rows t) : ℤ) : ZMod N) =
      (Int.castRingHom (ZMod N)) (booleanCoefficient (fun s =>
        MvPolynomial.eval (integerAffineCube root D s)
          (MvPolynomial.monomial e.val (1 : ℤ))) (rows t)) from rfl,
    booleanCoefficient_map]
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod,
    Int.coe_castRingHom, Int.cast_prod, Int.cast_pow]

namespace VectorPolynomial

theorem coefficientDeckJetMap_eq_booleanCoefficient
    {α K : Type*} [DecidableEq α] [Fintype K]
    {m : ℕ} {O B : Fin m → Type*}
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (N : ℕ) (r : CoefficientDeckResidues (K := K) B N)
    (j : Fin m) (t : O j) (i : B j) :
    coefficientDeckJetMap root D rows N r j t i =
      booleanCoefficient (fun s => MvPolynomial.eval
        (fun k => (integerAffineCube root D s k : ZMod N))
        (modularBoundedCoefficientPolynomial (j.val + 1) (fun e => r j e i)))
        (rows j t) := by
  rw [modularBoundedCoefficientPolynomial_booleanCoefficient]
  change (∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • r j e) i = _
  simp only [Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open MvPolynomial VectorPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ} {E : Fin m → Type*} {N : ℕ}

noncomputable def modularDeckPolynomial (r : CoefficientDeckResidues (K := K) E N)
    (j : Fin m) (i : E j) : MvPolynomial K (ZMod N) :=
  modularBoundedCoefficientPolynomial (j.val + 1) (fun e => r j e i)

theorem coefficientDeckJetMap_eq_modularDeckPolynomial
    {α : Type*} [DecidableEq α] {O : Fin m → Type*}
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m) (t : O j) (i : E j) :
    coefficientDeckJetMap root D rows N r j t i =
      booleanCoefficient (fun s => MvPolynomial.eval
        (fun k => (integerAffineCube root D s k : ZMod N)) (modularDeckPolynomial r j i))
        (rows j t) :=
  coefficientDeckJetMap_eq_booleanCoefficient root D rows N r j t i

theorem modularDeckPolynomial_degree (r : CoefficientDeckResidues (K := K) E N)
    (j : Fin m) (i : E j) : (modularDeckPolynomial r j i).totalDegree ≤ j.val + 1 := by
  apply totalDegree_finsetSum_le
  intro e _
  exact (totalDegree_monomial_le e.val (r j e i)).trans e.property

noncomputable def resampleCoefficientDeckCoordinate {A : Type*}
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (c : A → ZMod N) :
    CoefficientDeckResidues (K := K) E N :=
  Function.update r j (fun e => Function.update (r j e) i
    (Function.extend slot c (fun e => r j e i) e))

omit [Fintype K] in
theorem resampleCoefficientDeckCoordinate_apply {A : Type*}
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (c : A → ZMod N)
    (e : BoundedCoefficientExponent K (j.val + 1)) :
    resampleCoefficientDeckCoordinate r j i slot c j e i =
      Function.extend slot c (fun e => r j e i) e := by
  simp only [resampleCoefficientDeckCoordinate, Function.update_self]

omit [Fintype K] in
theorem resampleCoefficientDeckCoordinate_selected {A : Type*}
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (hinj : Function.Injective slot)
    (c : A → ZMod N) (a : A) :
    resampleCoefficientDeckCoordinate r j i slot c j (slot a) i = c a := by
  rw [resampleCoefficientDeckCoordinate_apply, hinj.extend_apply]

theorem modularDeckPolynomial_resample_top {A : Type*} [Fintype A]
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (hinj : Function.Injective slot)
    (hdegree : ∀ a, (slot a).val.degree = j.val + 1) (c : A → ZMod N) :
    homogeneousComponent (j.val + 1)
      (modularDeckPolynomial (resampleCoefficientDeckCoordinate r j i slot c) j i) =
      homogeneousComponent (j.val + 1)
        (modularUnselectedCoefficientPolynomial (j.val + 1) slot (fun e => r j e i)) +
      ∑ a, MvPolynomial.monomial (slot a).val (c a) := by
  simp only [modularDeckPolynomial, resampleCoefficientDeckCoordinate_apply]
  exact modularBoundedCoefficientPolynomial_selected_top _ slot hinj hdegree _ c

end VectorPolynomial

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

theorem samplerLongEmbedding_kernelExponent (inactive : D → Prop) (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) :
    ((kernelRankCoefficientSlot (G := G)
      (B := fun d : {d // ¬ inactive d} => B d.val) (fun d => degree d.val) e a).val).mapDomain
        (samplerLongEmbedding inactive degree) =
      (kernelRankCoefficientSlot (B := B) degree e a).val := by
  simp only [kernelRankCoefficientSlot, productBlockExponent,
    Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single,
    kernelRankBlockEmbedding_apply, samplerLongEmbedding_common]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {E : Fin m → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)] [Fintype A]
    {N : ℕ}

theorem modularDeckPolynomial_kernel_resample_top
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (j : Fin m) (i : E j) (e : A × Fin (j.val + 1) ↪ G) (c : A → ZMod N) :
    homogeneousComponent (j.val + 1)
      (modularDeckPolynomial (resampleCoefficientDeckCoordinate r j i
        (kernelRankCoefficientSlot (layerSamplerDegree I n) e) c) j i) =
      homogeneousComponent (j.val + 1)
        (modularUnselectedCoefficientPolynomial (j.val + 1)
          (kernelRankCoefficientSlot (layerSamplerDegree I n) e) (fun q => r j q i)) +
      ∑ a, c a • ∏ k ∈ kernelRankBlock (layerSamplerDegree I n) e a, X k := by
  rw [modularDeckPolynomial_resample_top r j i _
    (kernelRankCoefficientSlot_injective _ e (Nat.zero_lt_succ _))
    (kernelRankCoefficientSlot_degree _ e)]
  simp_rw [kernelRankCoefficientSlot_monomial]

theorem modularDeckPolynomial_kernel_resample_long_top
    (inactive : LayerSamplerAxis I n → Prop)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (j : Fin m) (i : E j) (e : A × Fin (j.val + 1) ↪ G) (c : A → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N) :
    homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularDeckPolynomial (resampleCoefficientDeckCoordinate r j i
          (kernelRankCoefficientSlot (layerSamplerDegree I n) e) c) j i)) =
      killCompl (allocatedLongEmbedding inactive).injective
        (homogeneousComponent (j.val + 1)
          (modularUnselectedCoefficientPolynomial (j.val + 1)
            (kernelRankCoefficientSlot (layerSamplerDegree I n) e) (fun q => r j q i))) +
      ∑ a, c a • ∏ k ∈ kernelRankBlock
        (B := fun d : {d : LayerSamplerAxis I n // ¬ inactive d} => B d.val)
        (fun d => layerSamplerDegree I n d.val) e a, X k := by
  rw [homogeneousComponent_conditionPolynomial_top _ _ _ v _
    (modularDeckPolynomial_degree _ j i)]
  rw [modularDeckPolynomial_resample_top r j i _
    (kernelRankCoefficientSlot_injective _ e (Nat.zero_lt_succ _))
    (kernelRankCoefficientSlot_degree _ e), map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change killCompl (samplerLongEmbedding inactive (layerSamplerDegree I n)).injective
    (MvPolynomial.monomial (kernelRankCoefficientSlot (layerSamplerDegree I n) e a).val (c a)) = _
  rw [← samplerLongEmbedding_kernelExponent inactive (layerSamplerDegree I n) e a,
    killCompl_monomial_mapDomain, kernelRankCoefficientSlot_monomial]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K A : Type*} {m : ℕ} {E : Fin m → Type*} {N : ℕ}

abbrev CoefficientDeckScalarIndex (K : Type*) (E : Fin m → Type*) :=
  Σ j : Fin m, BoundedCoefficientExponent K (j.val + 1) × E j

def coefficientDeckScalarEquiv :
    CoefficientDeckResidues (K := K) E N ≃ (CoefficientDeckScalarIndex K E → ZMod N) where
  toFun r t := r t.1 t.2.1 t.2.2
  invFun f j e i := f ⟨j, e, i⟩
  left_inv _ := rfl
  right_inv _ := rfl

def coefficientDeckSelectedEmbedding (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (hinj : Function.Injective slot) :
    A ↪ CoefficientDeckScalarIndex K E where
  toFun a := ⟨j, slot a, i⟩
  inj' := by
    intro a b hab
    have he : (slot a, i) = (slot b, i) := by
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hab
    exact hinj (congrArg Prod.fst he)

theorem coefficientDeckScalarEquiv_resample
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (hinj : Function.Injective slot)
    (c : A → ZMod N) :
    coefficientDeckScalarEquiv (resampleCoefficientDeckCoordinate r j i slot c) =
      Function.extend (coefficientDeckSelectedEmbedding j i slot hinj) c
        (coefficientDeckScalarEquiv r) := by
  funext t
  rcases t with ⟨q, e, k⟩
  by_cases hq : q = j
  · subst q
    by_cases hk : k = i
    · subst k
      by_cases he : e ∈ Set.range slot
      · obtain ⟨a, rfl⟩ := he
        change resampleCoefficientDeckCoordinate r j i slot c j (slot a) i =
          Function.extend (coefficientDeckSelectedEmbedding j i slot hinj) c
            (coefficientDeckScalarEquiv r) (coefficientDeckSelectedEmbedding j i slot hinj a)
        rw [resampleCoefficientDeckCoordinate_selected r j i slot hinj,
          (coefficientDeckSelectedEmbedding j i slot hinj).injective.extend_apply]
      · have hn : (⟨j, e, i⟩ : CoefficientDeckScalarIndex K E) ∉
            Set.range (coefficientDeckSelectedEmbedding j i slot hinj) := by
          rintro ⟨a, ha⟩
          have hp : (slot a, i) = (e, i) := by
            change (⟨j, slot a, i⟩ : CoefficientDeckScalarIndex K E) = ⟨j, e, i⟩ at ha
            simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using ha
          exact he ⟨a, congrArg Prod.fst hp⟩
        change resampleCoefficientDeckCoordinate r j i slot c j e i = _
        rw [resampleCoefficientDeckCoordinate_apply, Function.extend_apply' c _ e he,
          Function.extend_apply' c _ _ hn]
        rfl
    · have hn : (⟨j, e, k⟩ : CoefficientDeckScalarIndex K E) ∉
          Set.range (coefficientDeckSelectedEmbedding j i slot hinj) := by
        rintro ⟨a, ha⟩
        have hp : (slot a, i) = (e, k) := by
          change (⟨j, slot a, i⟩ : CoefficientDeckScalarIndex K E) = ⟨j, e, k⟩ at ha
          simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using ha
        exact hk (congrArg Prod.snd hp).symm
      rw [Function.extend_apply' c _ _ hn]
      change resampleCoefficientDeckCoordinate r j i slot c j e k = r j e k
      simp [resampleCoefficientDeckCoordinate, hk]
  · have hn : (⟨q, e, k⟩ : CoefficientDeckScalarIndex K E) ∉
        Set.range (coefficientDeckSelectedEmbedding j i slot hinj) := by
      rintro ⟨a, ha⟩
      exact hq (congrArg Sigma.fst ha).symm
    rw [Function.extend_apply' c _ _ hn]
    change resampleCoefficientDeckCoordinate r j i slot c q e k = r q e k
    simp [resampleCoefficientDeckCoordinate, hq]

variable [Fintype K] [Fintype A] [∀ j, Fintype (E j)] [NeZero N]

theorem expect_resampleCoefficientDeckCoordinate
    (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (hinj : Function.Injective slot)
    (F : CoefficientDeckResidues (K := K) E N → ℝ) :
    (𝔼 r : CoefficientDeckResidues (K := K) E N,
      𝔼 c : A → ZMod N, F (resampleCoefficientDeckCoordinate r j i slot c)) = 𝔼 r, F r := by
  let e := coefficientDeckScalarEquiv (K := K) (E := E) (N := N)
  let f := coefficientDeckSelectedEmbedding j i slot hinj
  calc
    _ = 𝔼 r : CoefficientDeckScalarIndex K E → ZMod N,
        𝔼 c : A → ZMod N, F (e.symm (Function.extend f c r)) := by
      apply Fintype.expect_equiv e
      intro r
      apply Finset.expect_congr rfl
      intro c _
      rw [← coefficientDeckScalarEquiv_resample r j i slot hinj c]
      rfl
    _ = 𝔼 r : CoefficientDeckScalarIndex K E → ZMod N, F (e.symm r) :=
      expect_coordinate_resampling f f.injective (fun r => F (e.symm r))
    _ = _ := by
      apply Fintype.expect_equiv e.symm
      intro r
      rfl

theorem expect_coefficientDeck_selected
    (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (hinj : Function.Injective slot)
    (F : (A → ZMod N) → ℝ) :
    (𝔼 r : CoefficientDeckResidues (K := K) E N, F (fun a => r j (slot a) i)) =
      𝔼 c : A → ZMod N, F c := by
  rw [← expect_resampleCoefficientDeckCoordinate j i slot hinj
    (fun r => F (fun a => r j (slot a) i))]
  simp only [resampleCoefficientDeckCoordinate_selected _ _ _ slot hinj]
  exact Fintype.expect_const _

theorem coefficientDeck_expect_le_of_resampling
    (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (hinj : Function.Injective slot)
    (F : CoefficientDeckResidues (K := K) E N → ℝ) {C : ℝ}
    (hF : ∀ r, (𝔼 c : A → ZMod N, F (resampleCoefficientDeckCoordinate r j i slot c)) ≤ C) :
    (𝔼 r : CoefficientDeckResidues (K := K) E N, F r) ≤ C := by
  rw [← expect_resampleCoefficientDeckCoordinate j i slot hinj F]
  calc
    _ ≤ 𝔼 _r : CoefficientDeckResidues (K := K) E N, C :=
      Finset.expect_le_expect (fun r _ => hF r)
    _ = C := Fintype.expect_const C

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev AllocatedProjectionCoefficientIndex (K : Type*) (I : Fin m → Type*) (n : Fin m → ℕ) :=
  Σ a : LayerSamplerAxis I n, BoundedCoefficientExponent K (a.1.val + 1)

abbrev AllocatedActualCoefficientIndex (G X : Type*) (I E : Fin m → Type*)
    (n : Fin m → ℕ) (B : LayerSamplerAxis I n → Type*) :=
  (Option (LayerSamplerVariables G I n B) × X) ⊕
    (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E ⊕
      AllocatedProjectionCoefficientIndex (LayerSamplerVariables G I n B) I n)

abbrev AllocatedSelectedCoefficientIndex (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :=
  Σ j : Fin m, AllocatedTaggedRankOutput X E inactive j × Fin L

noncomputable def allocatedActualCoefficientSlot
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedSelectedCoefficientIndex X E inactive L → AllocatedActualCoefficientIndex G X I E n B
  | ⟨_j, .inl x, l⟩ => .inl (some (.inl (spatial l)), x.val)
  | ⟨j, .inr (.inl i), l⟩ => .inr (.inl ⟨j,
      kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j) l, i⟩)
  | ⟨j, .inr (.inr a), l⟩ => .inr (.inr ⟨⟨j, a.val⟩,
      principalCoefficientSlot (layerSamplerDegree I n) ⟨j, a.val⟩ (block j a l)⟩)

theorem allocatedActualCoefficientSlot_injective
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩) :
    Function.Injective (allocatedActualCoefficientSlot (X := X) (E := E) inactive spatial kernel block) := by
  rintro ⟨j, o, l⟩ ⟨k, p, q⟩ he
  cases o with
  | inl x =>
    cases p with
    | inl y =>
      have hjk : j = k := Fin.ext (x.property.trans y.property.symm)
      subst k
      change Sum.inl (some (Sum.inl (spatial l)), x.val) =
        Sum.inl (some (Sum.inl (spatial q)), y.val) at he
      have hp := Sum.inl.inj he
      have hl : l = q := spatial.injective
        (Sum.inl.inj (Option.some.inj (congrArg Prod.fst hp)))
      have hxy : x = y := Subtype.ext (congrArg Prod.snd hp)
      subst q
      subst y
      rfl
    | inr p => cases p <;> cases he
  | inr o =>
    cases p with
    | inl y => cases o <;> cases he
    | inr p =>
      cases o with
      | inl i =>
        cases p with
        | inl t =>
          have hh := Sum.inl.inj (Sum.inr.inj he)
          have hjk : j = k := congrArg Sigma.fst hh
          subst k
          have hp : (kernelRankCoefficientSlot (B := B) (layerSamplerDegree I n) (kernel j) l, i) =
              (kernelRankCoefficientSlot (B := B) (layerSamplerDegree I n) (kernel j) q, t) := by
            simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hh
          have hl : l = q := kernelRankCoefficientSlot_injective
            (layerSamplerDegree I n) (kernel j) (Nat.zero_lt_succ _) (congrArg Prod.fst hp)
          have hit : i = t := congrArg Prod.snd hp
          subst q
          subst t
          rfl
        | inr a => cases he
      | inr a =>
        cases p with
        | inl t => cases he
        | inr b =>
          have hh := Sum.inr.inj (Sum.inr.inj he)
          have haxis : (⟨j, a.val⟩ : LayerSamplerAxis I n) = ⟨k, b.val⟩ := congrArg Sigma.fst hh
          have hjk : j = k := congrArg Sigma.fst haxis
          subst k
          have hab : a = b := Subtype.ext (by
            simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using haxis)
          subst b
          have hslot : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, a.val⟩
              (block j a l) = principalCoefficientSlot (layerSamplerDegree I n) ⟨j, a.val⟩
              (block j a q) := by
            exact eq_of_heq (Sigma.mk.inj hh).2
          have hblocks := principalCoefficientSlot_injective (G := G)
            (layerSamplerDegree I n) ⟨j, a.val⟩ (Nat.zero_lt_succ _) hslot
          have hl : l = q := (block j a).injective hblocks
          subst q
          rfl

noncomputable def allocatedActualCoefficientEmbedding
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedSelectedCoefficientIndex X E inactive L ↪ AllocatedActualCoefficientIndex G X I E n B :=
  ⟨allocatedActualCoefficientSlot inactive spatial kernel block,
    allocatedActualCoefficientSlot_injective inactive spatial kernel block⟩

variable {R : Type*}

def allocatedReadNoise (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    Option (LayerSamplerVariables G I n B) × X → R :=
  fun t => f (.inl t)

def allocatedReadDeck (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    ∀ j : Fin m, BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → R :=
  fun j e i => f (.inr (.inl ⟨j, e, i⟩))

def allocatedReadProjection (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    ∀ a : LayerSamplerAxis I n,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (a.1.val + 1) → R :=
  fun a e => f (.inr (.inr ⟨a, e⟩))

def allocatedActualCoefficientEquiv (R : Type*) :
    (AllocatedActualCoefficientIndex G X I E n B → R) ≃
      ((Option (LayerSamplerVariables G I n B) × X → R) ×
       (∀ j : Fin m, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
          (j.val + 1) → E j → R) ×
       (∀ a : LayerSamplerAxis I n,
          BoundedCoefficientExponent (LayerSamplerVariables G I n B) (a.1.val + 1) → R)) where
  toFun f := (allocatedReadNoise f, allocatedReadDeck f, allocatedReadProjection f)
  invFun p t := match t with
    | .inl t => p.1 t
    | .inr (.inl ⟨j, e, i⟩) => p.2.1 j e i
    | .inr (.inr ⟨a, e⟩) => p.2.2 a e
  left_inv f := by
    funext t
    rcases t with t | t | t <;> rfl
  right_inv p := rfl

theorem allocatedActualCoefficientSlot_read_spatial
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (f : AllocatedActualCoefficientIndex G X I E n B → R)
    (j : Fin m) (x : SpatialDegreeOutput X j) (l : Fin L) :
    f (allocatedActualCoefficientSlot inactive spatial kernel block ⟨j, .inl x, l⟩) =
      allocatedReadNoise f (some (.inl (spatial l)), x.val) := rfl

theorem allocatedActualCoefficientSlot_read_deck
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (f : AllocatedActualCoefficientIndex G X I E n B → R)
    (j : Fin m) (i : E j) (l : Fin L) :
    f (allocatedActualCoefficientSlot inactive spatial kernel block ⟨j, .inr (.inl i), l⟩) =
      allocatedReadDeck f j (kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j) l) i := rfl

theorem allocatedActualCoefficientSlot_read_projection
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (f : AllocatedActualCoefficientIndex G X I E n B → R)
    (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j) (l : Fin L) :
    f (allocatedActualCoefficientSlot inactive spatial kernel block ⟨j, .inr (.inr a), l⟩) =
      allocatedReadProjection f ⟨j, a.val⟩
        (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, a.val⟩ (block j a l)) := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K A : Type*} {m : ℕ} {E : Fin m → Type*} {N : ℕ}

noncomputable def resampleCoefficientDeckLayer
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (c : E j → A → ZMod N) :
    CoefficientDeckResidues (K := K) E N :=
  Function.update r j (fun e i => Function.extend slot (c i) (fun e => r j e i) e)

theorem resampleCoefficientDeckLayer_apply
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (c : E j → A → ZMod N)
    (e : BoundedCoefficientExponent K (j.val + 1)) (i : E j) :
    resampleCoefficientDeckLayer r j slot c j e i =
      Function.extend slot (c i) (fun e => r j e i) e := by
  simp only [resampleCoefficientDeckLayer, Function.update_self]

theorem resampleCoefficientDeckLayer_selected
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (hinj : Function.Injective slot)
    (c : E j → A → ZMod N) (a : A) (i : E j) :
    resampleCoefficientDeckLayer r j slot c j (slot a) i = c i a := by
  rw [resampleCoefficientDeckLayer_apply, hinj.extend_apply]

theorem modularDeckPolynomial_resampleLayer [Fintype K]
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (c : E j → A → ZMod N)
    (i : E j) :
    modularDeckPolynomial (resampleCoefficientDeckLayer r j slot c) j i =
      modularDeckPolynomial (resampleCoefficientDeckCoordinate r j i slot (c i)) j i := by
  simp only [modularDeckPolynomial, resampleCoefficientDeckLayer_apply,
    resampleCoefficientDeckCoordinate_apply]

theorem exists_coefficientDeck_layer_witness [Fintype K]
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (c : E j → A → ZMod N) :
    ∃ r' : CoefficientDeckResidues (K := K) E N, ∀ i : E j,
      modularDeckPolynomial r' j i =
        modularDeckPolynomial (resampleCoefficientDeckCoordinate r j i slot (c i)) j i :=
  ⟨resampleCoefficientDeckLayer r j slot c, modularDeckPolynomial_resampleLayer r j slot c⟩

def coefficientDeckLayerSelectedEmbedding (j : Fin m)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (hinj : Function.Injective slot) :
    E j × A ↪ CoefficientDeckScalarIndex K E where
  toFun p := ⟨j, slot p.2, p.1⟩
  inj' := by
    intro a b hab
    have hp : (slot a.2, a.1) = (slot b.2, b.1) := by
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hab
    exact Prod.ext (congrArg Prod.snd hp) (hinj (congrArg Prod.fst hp))

def coefficientDeckLayerFreshEquiv (j : Fin m) :
    (E j → A → ZMod N) ≃ (E j × A → ZMod N) where
  toFun c p := c p.1 p.2
  invFun c i a := c (i, a)
  left_inv _ := rfl
  right_inv _ := rfl

theorem coefficientDeckScalarEquiv_resampleLayer
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (hinj : Function.Injective slot)
    (c : E j → A → ZMod N) :
    coefficientDeckScalarEquiv (resampleCoefficientDeckLayer r j slot c) =
      Function.extend (coefficientDeckLayerSelectedEmbedding j slot hinj)
        (coefficientDeckLayerFreshEquiv j c) (coefficientDeckScalarEquiv r) := by
  funext t
  rcases t with ⟨q, e, i⟩
  by_cases hq : q = j
  · subst q
    by_cases he : e ∈ Set.range slot
    · obtain ⟨a, rfl⟩ := he
      change resampleCoefficientDeckLayer r j slot c j (slot a) i =
        Function.extend (coefficientDeckLayerSelectedEmbedding j slot hinj)
          (coefficientDeckLayerFreshEquiv j c) (coefficientDeckScalarEquiv r)
          (coefficientDeckLayerSelectedEmbedding j slot hinj (i, a))
      rw [resampleCoefficientDeckLayer_selected r j slot hinj,
        (coefficientDeckLayerSelectedEmbedding j slot hinj).injective.extend_apply]
      rfl
    · have hn : (⟨j, e, i⟩ : CoefficientDeckScalarIndex K E) ∉
          Set.range (coefficientDeckLayerSelectedEmbedding j slot hinj) := by
        rintro ⟨a, ha⟩
        have hp : (slot a.2, a.1) = (e, i) := by
          change (⟨j, slot a.2, a.1⟩ : CoefficientDeckScalarIndex K E) = ⟨j, e, i⟩ at ha
          simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using ha
        exact he ⟨a.2, congrArg Prod.fst hp⟩
      change resampleCoefficientDeckLayer r j slot c j e i = _
      rw [resampleCoefficientDeckLayer_apply, Function.extend_apply' (c i) _ e he,
        Function.extend_apply' _ _ _ hn]
      rfl
  · have hn : (⟨q, e, i⟩ : CoefficientDeckScalarIndex K E) ∉
        Set.range (coefficientDeckLayerSelectedEmbedding j slot hinj) := by
      rintro ⟨a, ha⟩
      exact hq (congrArg Sigma.fst ha).symm
    rw [Function.extend_apply' _ _ _ hn]
    change resampleCoefficientDeckLayer r j slot c q e i = r q e i
    simp [resampleCoefficientDeckLayer, hq]

variable [Fintype K] [Fintype A] [∀ j, Fintype (E j)] [NeZero N]

theorem expect_resampleCoefficientDeckLayer
    (j : Fin m) (slot : A → BoundedCoefficientExponent K (j.val + 1))
    (hinj : Function.Injective slot) (F : CoefficientDeckResidues (K := K) E N → ℝ) :
    (𝔼 r : CoefficientDeckResidues (K := K) E N,
      𝔼 c : E j → A → ZMod N, F (resampleCoefficientDeckLayer r j slot c)) = 𝔼 r, F r := by
  let e := coefficientDeckScalarEquiv (K := K) (E := E) (N := N)
  let f := coefficientDeckLayerSelectedEmbedding (E := E) j slot hinj
  let g := coefficientDeckLayerFreshEquiv (E := E) (A := A) (N := N) j
  calc
    _ = 𝔼 r : CoefficientDeckScalarIndex K E → ZMod N,
        𝔼 c : E j × A → ZMod N, F (e.symm (Function.extend f c r)) := by
      apply Fintype.expect_equiv e
      intro r
      apply Fintype.expect_equiv g
      intro c
      rw [← coefficientDeckScalarEquiv_resampleLayer r j slot hinj c]
      rfl
    _ = 𝔼 r : CoefficientDeckScalarIndex K E → ZMod N, F (e.symm r) :=
      expect_coordinate_resampling f f.injective (fun r => F (e.symm r))
    _ = _ := by
      apply Fintype.expect_equiv e.symm
      intro r
      rfl

theorem expect_coefficientDeck_layer_selected
    (j : Fin m) (slot : A → BoundedCoefficientExponent K (j.val + 1))
    (hinj : Function.Injective slot) (F : (E j → A → ZMod N) → ℝ) :
    (𝔼 r : CoefficientDeckResidues (K := K) E N, F (fun i a => r j (slot a) i)) =
      𝔼 c : E j → A → ZMod N, F c := by
  rw [← expect_resampleCoefficientDeckLayer j slot hinj (fun r => F (fun i a => r j (slot a) i))]
  simp only [resampleCoefficientDeckLayer_selected _ _ slot hinj]
  exact Fintype.expect_const _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)] {N L : ℕ} [NeZero N]

noncomputable local instance selectedIndexFintype
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    Fintype (AllocatedSelectedCoefficientIndex X E inactive L) := inferInstance

noncomputable local instance selectedIndexDecidableEq
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    DecidableEq (AllocatedSelectedCoefficientIndex X E inactive L) := Classical.decEq _

theorem expect_allocatedActualCoefficient_selected
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (F : (AllocatedSelectedCoefficientIndex X E inactive L → ZMod N) → ℝ) :
    (𝔼 c : AllocatedActualCoefficientIndex G X I E n B → ZMod N,
      F (c ∘ allocatedActualCoefficientSlot inactive spatial kernel block)) =
      𝔼 d : AllocatedSelectedCoefficientIndex X E inactive L → ZMod N, F d := by
  exact uniform_expect_coordinate_pullback
    (X := fun _ : AllocatedActualCoefficientIndex G X I E n B => ZMod N)
    (allocatedActualCoefficientSlot inactive spatial kernel block)
    (allocatedActualCoefficientSlot_injective inactive spatial kernel block) F

theorem expect_allocatedActualCoefficient_resample
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (F : (AllocatedActualCoefficientIndex G X I E n B → ZMod N) → ℝ) :
    (𝔼 c : AllocatedActualCoefficientIndex G X I E n B → ZMod N,
      𝔼 d : AllocatedSelectedCoefficientIndex X E inactive L → ZMod N,
        F (Function.extend (allocatedActualCoefficientSlot inactive spatial kernel block) d c)) =
      𝔼 c : AllocatedActualCoefficientIndex G X I E n B → ZMod N, F c :=
  expect_coordinate_resampling (allocatedActualCoefficientSlot inactive spatial kernel block)
    (allocatedActualCoefficientSlot_injective inactive spatial kernel block) F

theorem expect_allocatedActualCoefficient_selected_subfamily {T : Type*} [Fintype T]
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (e : T ↪ AllocatedSelectedCoefficientIndex X E inactive L) (F : (T → ZMod N) → ℝ) :
    (𝔼 c : AllocatedActualCoefficientIndex G X I E n B → ZMod N,
      F (fun t => c (allocatedActualCoefficientSlot inactive spatial kernel block (e t)))) =
      𝔼 d : T → ZMod N, F d := by
  exact uniform_expect_coordinate_pullback
    (X := fun _ : AllocatedActualCoefficientIndex G X I E n B => ZMod N)
    (fun t => allocatedActualCoefficientSlot inactive spatial kernel block (e t))
    ((allocatedActualCoefficientSlot_injective inactive spatial kernel block).comp e.injective) F

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev AllocatedCongruenceCoefficientIndex (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :=
  Σ j : Fin m, AllocatedCongruenceRankOutput X E inactive j × Fin L

abbrev AllocatedSmoothRankCoefficientIndex (X : Type*)
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :=
  Σ j : Fin m, (SpatialDegreeOutput X j ⊕ AllocatedCongruenceIntegerAxis inactive j) × Fin L

abbrev AllocatedDeckRankCoefficientIndex (E : Fin m → Type*) (L : ℕ) :=
  Σ j : Fin m, E j × Fin L

def allocatedCongruenceCoefficientSplit (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    AllocatedCongruenceCoefficientIndex X E inactive L ≃
      AllocatedSmoothRankCoefficientIndex X inactive L ⊕ AllocatedDeckRankCoefficientIndex E L where
  toFun k := match k with
    | ⟨j,.inl x,l⟩ => .inl ⟨j,.inl x,l⟩
    | ⟨j,.inr (.inl e),l⟩ => .inr ⟨j,e,l⟩
    | ⟨j,.inr (.inr i),l⟩ => .inl ⟨j,.inr i,l⟩
  invFun k := match k with
    | .inl ⟨j,.inl x,l⟩ => ⟨j,.inl x,l⟩
    | .inr ⟨j,e,l⟩ => ⟨j,.inr (.inl e),l⟩
    | .inl ⟨j,.inr i,l⟩ => ⟨j,.inr (.inr i),l⟩
  left_inv := by rintro ⟨j,(x | e | i),l⟩ <;> rfl
  right_inv := by rintro (⟨j,(x | i),l⟩ | ⟨j,e,l⟩) <;> rfl

def allocatedCongruenceCoefficientEmbedding (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    AllocatedCongruenceCoefficientIndex X E inactive L ↪
      AllocatedSelectedCoefficientIndex X E inactive L :=
  Function.Embedding.sigmaMap (Function.Embedding.refl _)
    (fun j => Function.Embedding.prodMap (allocatedCongruenceOutputEmbedding inactive j)
      (Function.Embedding.refl _))

noncomputable def allocatedCongruenceActualCoefficientEmbedding
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedCongruenceCoefficientIndex X E inactive L ↪ AllocatedActualCoefficientIndex G X I E n B :=
  (allocatedCongruenceCoefficientEmbedding inactive L).trans
    (allocatedActualCoefficientEmbedding inactive spatial kernel block)

noncomputable def allocatedMixedSelectedValues (inactive : LayerSamplerAxis I n → Prop)
    {L N : ℕ} (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    AllocatedCongruenceCoefficientIndex X E inactive L → ℤ :=
  Sum.elim x (fun j => (deck j).val) ∘ allocatedCongruenceCoefficientSplit inactive L

theorem allocatedMixedSelectedValues_spatial (inactive : LayerSamplerAxis I n → Prop)
    {L N : ℕ} (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N)
    (j : Fin m) (z : SpatialDegreeOutput X j) (l : Fin L) :
    allocatedMixedSelectedValues inactive x deck ⟨j,.inl z,l⟩ = x ⟨j,.inl z,l⟩ := rfl

theorem allocatedMixedSelectedValues_deck (inactive : LayerSamplerAxis I n → Prop)
    {L N : ℕ} (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N)
    (j : Fin m) (e : E j) (l : Fin L) :
    allocatedMixedSelectedValues inactive x deck ⟨j,.inr (.inl e),l⟩ = (deck ⟨j,e,l⟩).val := rfl

theorem allocatedMixedSelectedValues_integer (inactive : LayerSamplerAxis I n → Prop)
    {L N : ℕ} (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N)
    (j : Fin m) (i : AllocatedCongruenceIntegerAxis inactive j) (l : Fin L) :
    allocatedMixedSelectedValues inactive x deck ⟨j,.inr (.inr i),l⟩ = x ⟨j,.inr i,l⟩ := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

def AllocatedRankComponentCoefficient
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    AllocatedCongruenceRankOutput X E inactive j → Type _
  | .inl _ => Option (LayerSamplerVariables G I n B)
  | .inr _ => BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)

abbrev AllocatedRankComponentCoefficientIndex
    (G X : Type*) (I E : Fin m → Type*) (n : Fin m → ℕ)
    (B : LayerSamplerAxis I n → Type*) (inactive : LayerSamplerAxis I n → Prop) :=
  Σ t : (Σ j : Fin m, AllocatedCongruenceRankOutput X E inactive j),
    AllocatedRankComponentCoefficient (G := G) (B := B) inactive t.1 t.2

def allocatedRankComponentCoefficientSlot
    (inactive : LayerSamplerAxis I n → Prop) :
    AllocatedRankComponentCoefficientIndex G X I E n B inactive →
      AllocatedActualCoefficientIndex G X I E n B
  | ⟨⟨_j, .inl x⟩, q⟩ => .inl (q, x.val)
  | ⟨⟨j, .inr (.inl i)⟩, q⟩ => .inr (.inl ⟨j, q, i⟩)
  | ⟨⟨j, .inr (.inr i)⟩, q⟩ => .inr (.inr ⟨⟨j, .inr i.val⟩, q⟩)

theorem allocatedRankComponentCoefficientSlot_injective
    (inactive : LayerSamplerAxis I n → Prop) :
    Function.Injective
      (allocatedRankComponentCoefficientSlot (G := G) (X := X) (E := E) (B := B) inactive) := by
  rintro ⟨⟨j, o⟩, q⟩ ⟨⟨k, p⟩, r⟩ he
  cases o with
  | inl x =>
    cases p with
    | inl y =>
      have hjk : j = k := Fin.ext (x.property.trans y.property.symm)
      subst k
      have hp : (q, x.val) = (r, y.val) := Sum.inl.inj he
      have hxy : x = y := Subtype.ext (congrArg Prod.snd hp)
      subst y
      have hqr : q = r := congrArg Prod.fst hp
      subst r
      rfl
    | inr p => cases p <;> cases he
  | inr o =>
    cases p with
    | inl y => cases o <;> cases he
    | inr p =>
      cases o with
      | inl i =>
        cases p with
        | inl t =>
          have hh := Sum.inl.inj (Sum.inr.inj he)
          have hjk : j = k := congrArg Sigma.fst hh
          subst k
          have hp : (q, i) = (r, t) := by
            simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and,
              AllocatedRankComponentCoefficient] using hh
          have hit : i = t := congrArg Prod.snd hp
          subst t
          have hqr : q = r := congrArg Prod.fst hp
          subst r
          rfl
        | inr a => cases he
      | inr a =>
        cases p with
        | inl t => cases he
        | inr b =>
          have hh := Sum.inr.inj (Sum.inr.inj he)
          have haxis : (⟨j, .inr a.val⟩ : LayerSamplerAxis I n) = ⟨k, .inr b.val⟩ :=
            congrArg Sigma.fst hh
          have hjk : j = k := congrArg Sigma.fst haxis
          subst k
          have hab : a = b := Subtype.ext (by
            apply Sum.inr.inj
            exact eq_of_heq (Sigma.mk.inj haxis).2)
          subst b
          have hqr : q = r := eq_of_heq (Sigma.mk.inj hh).2
          subst r
          rfl

def allocatedRankComponentCoefficientEmbedding
    (inactive : LayerSamplerAxis I n → Prop) :
    AllocatedRankComponentCoefficientIndex G X I E n B inactive ↪
      AllocatedActualCoefficientIndex G X I E n B :=
  ⟨allocatedRankComponentCoefficientSlot inactive,
    allocatedRankComponentCoefficientSlot_injective inactive⟩

noncomputable def allocatedRankComponentSelectedSlot
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (j : Fin m) : (o : AllocatedCongruenceRankOutput X E inactive j) →
      Fin L → AllocatedRankComponentCoefficient (G := G) (B := B) inactive j o
  | .inl _ => spatialKernelRankSlot spatial
  | .inr (.inl _) => kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j)
  | .inr (.inr i) => canonicalPrincipalSubblockSlot (layerSamplerDegree I n)
      ⟨j, .inr i.val⟩ (block j (allocatedCongruenceIntegerEmbedding inactive j i))

theorem allocatedRankComponentSelectedSlot_injective
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j) :
    Function.Injective (allocatedRankComponentSelectedSlot inactive spatial kernel block j o) := by
  rcases o with x | i | a
  · exact spatialKernelRankSlot_injective spatial
  · exact kernelRankCoefficientSlot_injective (layerSamplerDegree I n) (kernel j)
      (Nat.zero_lt_succ _)
  · exact canonicalPrincipalSubblockSlot_injective (layerSamplerDegree I n)
      ⟨j, .inr a.val⟩ (Nat.zero_lt_succ _)
      (block j (allocatedCongruenceIntegerEmbedding inactive j a))

noncomputable def allocatedRankComponentSelectedEmbedding
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j) :
    Fin L ↪ AllocatedRankComponentCoefficient (G := G) (B := B) inactive j o :=
  ⟨allocatedRankComponentSelectedSlot inactive spatial kernel block j o,
    allocatedRankComponentSelectedSlot_injective inactive spatial kernel block j o⟩

theorem allocatedRankComponentCoefficientEmbedding_selected
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j) (l : Fin L) :
    allocatedRankComponentCoefficientEmbedding inactive
      ⟨⟨j, o⟩, allocatedRankComponentSelectedEmbedding inactive spatial kernel block j o l⟩ =
      allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block ⟨j, o, l⟩ := by
  rcases o with x | i | a <;> rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

def allocatedMixedCoefficientEquiv (inactive : LayerSamplerAxis I n → Prop) (L : ℕ)
    (R : Type*) [AddCommGroup R] :
    ((AllocatedSmoothRankCoefficientIndex X inactive L ⊕ AllocatedDeckRankCoefficientIndex E L) → R) ≃+
      (AllocatedCongruenceCoefficientIndex X E inactive L → R) where
  toFun f := f ∘ allocatedCongruenceCoefficientSplit inactive L
  invFun f := f ∘ (allocatedCongruenceCoefficientSplit inactive L).symm
  left_inv f := by funext j; simp only [Function.comp_apply, Equiv.apply_symm_apply]
  right_inv f := by funext j; simp only [Function.comp_apply, Equiv.symm_apply_apply]
  map_add' _ _ := rfl

noncomputable local instance congruenceIndexFintype [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    Fintype (AllocatedCongruenceCoefficientIndex X E inactive L) := inferInstance

noncomputable local instance congruenceIndexDecidableEq
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    DecidableEq (AllocatedCongruenceCoefficientIndex X E inactive L) := Classical.decEq _

theorem allocatedMixedCoefficient_uniform_event [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (L M : ℕ) [NeZero M]
    (F : (AllocatedCongruenceCoefficientIndex X E inactive L → ZMod M) → Prop) :
    (FiniteProbabilityWeights.uniform
      ((AllocatedSmoothRankCoefficientIndex X inactive L ⊕ AllocatedDeckRankCoefficientIndex E L) → ZMod M)).eventProbability
        (fun f => F (allocatedMixedCoefficientEquiv inactive L (ZMod M) f)) =
      (FiniteProbabilityWeights.uniform
        (AllocatedCongruenceCoefficientIndex X E inactive L → ZMod M)).eventProbability F := by
  exact uniform_mean_surjective_hom
    (allocatedMixedCoefficientEquiv (X := X) (E := E) inactive L (ZMod M)).toAddMonoidHom
    (allocatedMixedCoefficientEquiv (X := X) (E := E) inactive L (ZMod M)).surjective
    (fun f => if F f then (1 : ℝ) else 0)

theorem allocatedMixedCoefficientEquiv_cast (inactive : LayerSamplerAxis I n → Prop)
    {L N : ℕ} [NeZero N] (M : ℕ)
    (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    allocatedMixedCoefficientEquiv inactive L (ZMod M)
      (Sum.elim (fun j => (x j : ZMod M)) (fun j => ZMod.cast (deck j))) =
        fun j => (allocatedMixedSelectedValues inactive x deck j : ZMod M) := by
  funext j
  rcases j with ⟨j,(z | e | i),l⟩
  · rfl
  · exact (ZMod.cast_eq_val _).trans (Int.cast_natCast _).symm
  · rfl

end Erdos3.VectorPolynomial

end

end OAI
