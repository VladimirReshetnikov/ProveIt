import OAI.Combinatorics.Progressions.Linear.JoinedPairProjection

namespace OAI

universe u

section

namespace Erdos3.NilpotentLieFiltration

open Module
open RationalFilteredNilmanifold

section ControlledWitness

variable {σ ι V : Type*} [LieRing V] [LieAlgebra ℚ V] {s : ℕ}
  (H : NilpotentLieFiltration V s) (b : Basis ι ℚ V) (ω : ι → ℕ)
  (hH : ∀ k, H.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))

def ControlledSymbolFactorizationAtFast (η : V →ₗ[ℚ] ℚ) (side : σ → ℝ)
    (X : H.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ)
    (U : LieSubalgebra ℚ H.AssociatedGraded) : Prop :=
  ∃ (m : ℕ) (E P R : H.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (v : ι → H.AssociatedGraded),
    0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ E * P * R = X ∧
    H.SymbolSlowBound b ω hH (fun _ => 1) side (Real.exp p) E ∧
    H.SymbolRationalGrid b ω hH (fun _ => 1) m R ∧
    Submodule.span ℚ (Set.range v) = U.toSubmodule ∧
    BasisGradedSubmodule (H.associatedGradedBasis b ω hH) ω U.toSubmodule ∧
    (∀ i j, rationalLogHeight ((H.associatedGradedBasis b ω hH).repr (v i) j) ≤ p) ∧
    (∀ x ∈ U, basisGradeProjection (H.associatedGradedBasis b ω hH) ω s x = x →
      H.gradedFrequency b ω hH η x = 0) ∧
    P.coord ∈ realificationLieSubalgebra (H.symbolPointwiseSubalgebra b ω hH (fun _ => 1) U)

theorem ControlledSymbolFactorization.exists_fastWitness
    {η : V →ₗ[ℚ] ℚ} {side : σ → ℝ}
    {X : H.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    (h : H.ControlledSymbolFactorization b ω hH η side X p) :
    ∃ U, H.ControlledSymbolFactorizationAtFast b ω hH η side X p U := by
  obtain ⟨m, E, P, R, U, v, hdata⟩ := h
  exact ⟨U, m, E, P, R, v, hdata⟩

theorem ControlledSymbolFactorizationAtFast.graded_top_frequency
    {η : V →ₗ[ℚ] ℚ} {side : σ → ℝ}
    {X : H.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    {U : LieSubalgebra ℚ H.AssociatedGraded}
    (h : H.ControlledSymbolFactorizationAtFast b ω hH η side X p U) :
    ∀ x ∈ U, basisGradeProjection (H.associatedGradedBasis b ω hH) ω s x = x →
      H.gradedFrequency b ω hH η x = 0 := by
  obtain ⟨m, E, P, R, v, hm, hmp, heq, hE, hR, hv, hgraded, hheight, hzero, hP⟩ := h
  exact hzero

end ControlledWitness

section GradedIntersection

variable {V J : Type*} {P : J → Type*} [LieRing V] [LieAlgebra ℚ V]
  [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)] {s : ℕ}
  (H : NilpotentLieFiltration V s) (G : ∀ j, NilpotentLieFiltration (P j) s)
  (φ : ∀ j, V →ₗ⁅ℚ⁆ P j)
  (hφ : ∀ j k, ∀ x ∈ H.layer k, φ j x ∈ (G j).layer k)

noncomputable def joinedGradedPairFast
    (U : ∀ j, LieSubalgebra ℚ (G j).AssociatedGraded) (js : List J) :
    LieSubalgebra ℚ H.AssociatedGraded :=
  ⨅ j : {j // j ∈ js}, (U j.val).comap (H.associatedGradedMap (G j.val) (φ j.val) (hφ j.val))

theorem joinedGradedPairFast_refiltered_mem
    (U : ∀ j, LieSubalgebra ℚ (G j).AssociatedGraded) (js : List J)
    (k : ℕ) (x : V) (hx : x ∈ H.gradedRefiltrationLayer
      (H.joinedGradedPairFast G φ hφ U js) k) (j : J) (hj : j ∈ js) :
    φ j x ∈ (G j).gradedRefiltrationLayer (U j) k := by
  obtain ⟨hxH, hxU⟩ := (H.mem_gradedRefiltrationLayer _ k x).mp hx
  have hpiece : H.associatedGradedMap (G j) (φ j) (hφ j)
      (H.associatedGradedPieceMap k ⟨x, hxH⟩) ∈ U j :=
    (iInf_le (fun a : {j // j ∈ js} =>
      (U a.val).comap (H.associatedGradedMap (G a.val) (φ a.val) (hφ a.val))) ⟨j, hj⟩) hxU
  apply ((G j).mem_gradedRefiltrationLayer (U j) k (φ j x)).mpr
  refine ⟨hφ j k x hxH, ?_⟩
  simpa only [H.associatedGradedMap_piece] using hpiece

theorem joinedGradedPairFast_top_frequency
    {ι : J → Type*} (b : ∀ j, Basis (ι j) ℚ (P j)) (ω : ∀ j, ι j → ℕ)
    (hG : ∀ j k, (G j).layer k = Submodule.span ℚ (b j '' {i | k ≤ ω j i}))
    (U : ∀ j, LieSubalgebra ℚ (G j).AssociatedGraded) (js : List J)
    (η : ∀ j, P j →ₗ[ℚ] ℚ)
    (hzero : ∀ j ∈ js, ∀ a ∈ U j,
      basisGradeProjection ((G j).associatedGradedBasis (b j) (ω j) (hG j)) (ω j) s a = a →
      (G j).gradedFrequency (b j) (ω j) (hG j) (η j) a = 0)
    (x : V) (hx : x ∈ H.gradedRefiltrationLayer
      (H.joinedGradedPairFast G φ hφ U js) s) (j : J) (hj : j ∈ js) :
    η j (φ j x) = 0 :=
  (G j).frequency_zero_on_refiltered_top (b j) (ω j) (hG j) (U j) (η j) (hzero j hj)
    (φ j x) (H.joinedGradedPairFast_refiltered_mem G φ hφ U js s x hx j hj)

end GradedIntersection

section PairConstraints

variable {L W : Type u} {J Y : Type*} {M : J → Type u}
  [LieRing L] [LieAlgebra ℚ L] [LieRing W] [LieAlgebra ℚ W]
  [LieRing Y] [LieAlgebra ℚ Y]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {s : ℕ}
  (F : NilpotentLieFiltration L s) (H : NilpotentLieFiltration (L × W) s)
  (G : ∀ j, NilpotentLieFiltration (PairAlgebra L (M j)) s)
  (ρ : ∀ j, W →ₗ⁅ℚ⁆ M j)
  (hproj : ∀ j k, ∀ x ∈ H.layer k, joinedPairProjection (ρ j) x ∈ (G j).layer k)
  {ι : J → Type*} (b : ∀ j, Basis (ι j) ℚ (PairAlgebra L (M j)))
  (ω : ∀ j, ι j → ℕ)
  (hG : ∀ j k, (G j).layer k = Submodule.span ℚ (b j '' {i | k ≤ ω j i}))
  (U : ∀ j, LieSubalgebra ℚ (G j).AssociatedGraded) (js : List J)
  (eta : J → L →ₗ[ℚ] ℚ) (theta : ∀ j, M j →ₗ[ℚ] ℚ)
  (hzero : ∀ j ∈ js, ∀ a ∈ U j,
    basisGradeProjection ((G j).associatedGradedBasis (b j) (ω j) (hG j)) (ω j) s a = a →
    (G j).gradedFrequency (b j) (ω j) (hG j) (pairFrequency (eta j) (theta j)) a = 0)
  (hfst : ∀ x ∈ H.layer s, x.1 ∈ F.layer s)

include b ω hG hzero hfst

theorem joinedPairFastTop_le :
    H.gradedRefiltrationLayer
      (H.joinedGradedPairFast G (fun j => joinedPairProjection (ρ j)) hproj U js) s ≤
      F.joinedFrequencyTop eta js (fun j => (theta j).comp (ρ j).toLinearMap) := by
  intro x hx
  apply (F.mem_joinedFrequencyTop eta js _ x).mpr
  refine ⟨hfst x (H.gradedRefiltrationLayer_le _ s hx), ?_⟩
  intro j hj
  have hz := H.joinedGradedPairFast_top_frequency G
    (fun j => joinedPairProjection (ρ j)) hproj b ω hG U js
    (fun j => pairFrequency (eta j) (theta j)) hzero x hx j hj
  simpa only [pairFrequency_joinedPairProjection, LinearMap.comp_apply,
    LieHom.coe_toLinearMap] using hz

theorem joinedPairFastTop_quotient_le (π : L →ₗ⁅ℚ⁆ Y) :
    (H.gradedRefiltrationLayer
      (H.joinedGradedPairFast G (fun j => joinedPairProjection (ρ j)) hproj U js) s).map
      (F.pivotProductQuotientMap π eta js).toLinearMap ≤
      F.joinedFrequencyQuotientTop π eta js (fun j => (theta j).comp (ρ j).toLinearMap) := by
  exact Submodule.map_mono (F.joinedPairFastTop_le H G ρ hproj b ω hG U js eta theta hzero hfst)

theorem joinedPairFastTop_quotient_kernel_eq_zero (π : L →ₗ⁅ℚ⁆ Y)
    (x : (L ⧸ F.pivotAnnihilatorIdeal π eta js) × W)
    (hx : x ∈ (H.gradedRefiltrationLayer
      (H.joinedGradedPairFast G (fun j => joinedPairProjection (ρ j)) hproj U js) s).map
      (F.pivotProductQuotientMap π eta js).toLinearMap)
    (hkernel : F.pivotProductMarkedMap π eta js x = 0) : x = 0 :=
  F.joinedFrequencyQuotientTop_kernel_eq_zero π eta js
    (fun j => (theta j).comp (ρ j).toLinearMap) x
    (F.joinedPairFastTop_quotient_le H G ρ hproj b ω hG U js eta theta hzero hfst π hx) hkernel

end PairConstraints

section ActualFactorizations

theorem exists_joinedPairFastTop_of_controlled_factorizations
    {L W : Type u} {J Y σ : Type*} {M : J → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing W] [LieAlgebra ℚ W]
    [LieRing Y] [LieAlgebra ℚ Y]
    [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {s : ℕ}
    (F : NilpotentLieFiltration L s) (H : NilpotentLieFiltration (L × W) s)
    (G : ∀ j, NilpotentLieFiltration (PairAlgebra L (M j)) s)
    (ρ : ∀ j, W →ₗ⁅ℚ⁆ M j)
    (hproj : ∀ j k, ∀ x ∈ H.layer k, joinedPairProjection (ρ j) x ∈ (G j).layer k)
    {ι : J → Type*} (b : ∀ j, Basis (ι j) ℚ (PairAlgebra L (M j)))
    (ω : ∀ j, ι j → ℕ)
    (hG : ∀ j k, (G j).layer k = Submodule.span ℚ (b j '' {i | k ≤ ω j i}))
    (js : List J) (eta : J → L →ₗ[ℚ] ℚ) (theta : ∀ j, M j →ₗ[ℚ] ℚ)
    (side : σ → ℝ) (X : ∀ j, (G j).RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ)
    (hfactor : ∀ j, (G j).ControlledSymbolFactorization (b j) (ω j) (hG j)
      (pairFrequency (eta j) (theta j)) side (X j) p)
    (hfst : ∀ x ∈ H.layer s, x.1 ∈ F.layer s) (π : L →ₗ⁅ℚ⁆ Y) :
    ∃ U : ∀ j, LieSubalgebra ℚ (G j).AssociatedGraded,
      (∀ j, (G j).ControlledSymbolFactorizationAtFast (b j) (ω j) (hG j)
        (pairFrequency (eta j) (theta j)) side (X j) p (U j)) ∧
      (H.gradedRefiltrationLayer
        (H.joinedGradedPairFast G (fun j => joinedPairProjection (ρ j)) hproj U js) s).map
        (F.pivotProductQuotientMap π eta js).toLinearMap ≤
        F.joinedFrequencyQuotientTop π eta js (fun j => (theta j).comp (ρ j).toLinearMap) ∧
      ∀ x : (L ⧸ F.pivotAnnihilatorIdeal π eta js) × W,
        x ∈ (H.gradedRefiltrationLayer
          (H.joinedGradedPairFast G (fun j => joinedPairProjection (ρ j)) hproj U js) s).map
          (F.pivotProductQuotientMap π eta js).toLinearMap →
        F.pivotProductMarkedMap π eta js x = 0 → x = 0 := by
  choose U hU using fun j => (hfactor j).exists_fastWitness (G j) (b j) (ω j) (hG j)
  have hzero (j : J) (_hj : j ∈ js) :=
    (hU j).graded_top_frequency (G j) (b j) (ω j) (hG j)
  exact ⟨U, hU,
    F.joinedPairFastTop_quotient_le H G ρ hproj b ω hG U js eta theta hzero hfst π,
    F.joinedPairFastTop_quotient_kernel_eq_zero H G ρ hproj b ω hG U js eta theta hzero hfst π⟩

end ActualFactorizations

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module RationalFilteredNilmanifold

section GradedIntersection

variable {V J κ : Type*} {P : J → Type*} [LieRing V] [LieAlgebra ℚ V]
  [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)] {s : ℕ}
  (H : NilpotentLieFiltration V s) (G : ∀ j, NilpotentLieFiltration (P j) s)
  (e : Basis κ ℚ V) (μ : κ → ℕ)
  (hH : ∀ k, H.layer k = Submodule.span ℚ (e '' {i | k ≤ μ i}))
  (φ : ∀ j, V →ₗ⁅ℚ⁆ P j)
  (hφ : ∀ j k, ∀ x ∈ H.layer k, φ j x ∈ (G j).layer k)
  {ι : J → Type*} (b : ∀ j, Basis (ι j) ℚ (P j)) (ω : ∀ j, ι j → ℕ)
  (hG : ∀ j k, (G j).layer k = Submodule.span ℚ (b j '' {i | k ≤ ω j i}))
  (U : ∀ j, LieSubalgebra ℚ (G j).AssociatedGraded) (js : List J)

theorem joinedGradedPairFast_graded
    (hU : ∀ j ∈ js, BasisGradedSubmodule
      ((G j).associatedGradedBasis (b j) (ω j) (hG j)) (ω j) (U j).toSubmodule) :
    BasisGradedSubmodule (H.associatedGradedBasis e μ hH) μ
      (H.joinedGradedPairFast G φ hφ U js).toSubmodule := by
  intro k x hx
  change basisGradeProjection (H.associatedGradedBasis e μ hH) μ k x ∈
    H.joinedGradedPairFast G φ hφ U js
  apply (lieSubalgebra_mem_iInf _ _).mpr
  intro j
  have hxj := (iInf_le (fun a : {j // j ∈ js} =>
    (U a.val).comap (H.associatedGradedMap (G a.val) (φ a.val) (hφ a.val))) j) hx
  exact H.associatedGradedMap_comap_graded (G j.val) e μ hH
    (b j.val) (ω j.val) (hG j.val) (φ j.val) (hφ j.val) (U j.val)
    (hU j.val j.property) k x hxj

end GradedIntersection

section ActualPivotQuotient

variable {L W : Type u} {J Y κ κQ : Type*} {M : J → Type u}
  [LieRing L] [LieAlgebra ℚ L] [LieRing W] [LieAlgebra ℚ W]
  [LieRing Y] [LieAlgebra ℚ Y]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {s : ℕ}
  (F : NilpotentLieFiltration L s) (P : NilpotentLieFiltration W s)
  (G : ∀ j, NilpotentLieFiltration (PairAlgebra L (M j)) s)
  (ρ : ∀ j, W →ₗ⁅ℚ⁆ M j)
  (hproj : ∀ j k, ∀ x ∈ (F.prod P).layer k,
    joinedPairProjection (ρ j) x ∈ (G j).layer k)
  (e : Basis κ ℚ (L × W)) (μ : κ → ℕ)
  (hH : ∀ k, (F.prod P).layer k = Submodule.span ℚ (e '' {i | k ≤ μ i}))
  {ι : J → Type*} (b : ∀ j, Basis (ι j) ℚ (PairAlgebra L (M j)))
  (ω : ∀ j, ι j → ℕ)
  (hG : ∀ j k, (G j).layer k = Submodule.span ℚ (b j '' {i | k ≤ ω j i}))
  (U : ∀ j, LieSubalgebra ℚ (G j).AssociatedGraded) (js : List J)
  (hU : ∀ j ∈ js, BasisGradedSubmodule
    ((G j).associatedGradedBasis (b j) (ω j) (hG j)) (ω j) (U j).toSubmodule)
  (eta : J → L →ₗ[ℚ] ℚ) (theta : ∀ j, M j →ₗ[ℚ] ℚ)
  (π : L →ₗ⁅ℚ⁆ Y)
  (q : Basis κQ ℚ ((L ⧸ F.pivotAnnihilatorIdeal π eta js) × W)) (ν : κQ → ℕ)
  (hQ : ∀ k, (F.pivotProductQuotientFiltration π eta js P).layer k =
    Submodule.span ℚ (q '' {i | k ≤ ν i}))

noncomputable def joinedPairQuotientFast :
    LieSubalgebra ℚ (F.pivotProductQuotientFiltration π eta js P).AssociatedGraded :=
  ((F.prod P).joinedGradedPairFast G (fun j => joinedPairProjection (ρ j)) hproj U js).map
    ((F.prod P).associatedGradedMap (F.pivotProductQuotientFiltration π eta js P)
      (F.pivotProductQuotientMap π eta js)
      (F.pivotProductQuotientMap_mem_layer π eta js P))

include e μ hH b ω hG hU q ν hQ in

theorem joinedPairQuotientFast_layer_eq (k : ℕ) :
    (F.pivotProductQuotientFiltration π eta js P).gradedRefiltrationLayer
      (F.joinedPairQuotientFast P G ρ hproj U js eta π) k =
    ((F.prod P).gradedRefiltrationLayer
      ((F.prod P).joinedGradedPairFast G (fun j => joinedPairProjection (ρ j)) hproj U js) k).map
      (F.pivotProductQuotientMap π eta js).toLinearMap := by
  symm
  exact (F.prod P).gradedRefiltrationLayer_map
    (F.pivotProductQuotientFiltration π eta js P) e μ hH q ν hQ
    (F.pivotProductQuotientMap π eta js) (F.pivotProductQuotientMap_mem_layer π eta js P)
    _ ((F.prod P).joinedGradedPairFast_graded G e μ hH
      (fun j => joinedPairProjection (ρ j)) hproj b ω hG U js hU)
    (F.pivotProductQuotientMap_layer_surjective π eta js P) k

include e μ hH b ω hG hU q ν hQ in
theorem joinedPairQuotientFast_graded :
    BasisGradedSubmodule
      ((F.pivotProductQuotientFiltration π eta js P).associatedGradedBasis q ν hQ) ν
      (F.joinedPairQuotientFast P G ρ hproj U js eta π).toSubmodule :=
  (F.prod P).associatedGradedMap_image_graded
    (F.pivotProductQuotientFiltration π eta js P) e μ hH q ν hQ
    (F.pivotProductQuotientMap π eta js) (F.pivotProductQuotientMap_mem_layer π eta js P)
    _ ((F.prod P).joinedGradedPairFast_graded G e μ hH
      (fun j => joinedPairProjection (ρ j)) hproj b ω hG U js hU)

include e μ hH b ω hG hU q ν hQ in

theorem joinedPairQuotientFast_layer_surjective
    (k : ℕ)
    (y : (F.pivotProductQuotientFiltration π eta js P).gradedRefiltrationSubalgebra
      (F.joinedPairQuotientFast P G ρ hproj U js eta π))
    (hy : y ∈ ((F.pivotProductQuotientFiltration π eta js P).gradedRefiltration
      (F.joinedPairQuotientFast P G ρ hproj U js eta π)).layer k) :
    ∃ x ∈ ((F.prod P).gradedRefiltration
      ((F.prod P).joinedGradedPairFast G (fun j => joinedPairProjection (ρ j)) hproj U js)).layer k,
      (F.prod P).gradedRefiltrationMap (F.pivotProductQuotientFiltration π eta js P)
        (F.pivotProductQuotientMap π eta js) (F.pivotProductQuotientMap_mem_layer π eta js P)
        ((F.prod P).joinedGradedPairFast G (fun j => joinedPairProjection (ρ j)) hproj U js) x = y :=
  (F.prod P).gradedRefiltrationMap_layer_surjective
    (F.pivotProductQuotientFiltration π eta js P) e μ hH q ν hQ
    (F.pivotProductQuotientMap π eta js) (F.pivotProductQuotientMap_mem_layer π eta js P)
    _ ((F.prod P).joinedGradedPairFast_graded G e μ hH
      (fun j => joinedPairProjection (ρ j)) hproj b ω hG U js hU)
    (F.pivotProductQuotientMap_layer_surjective π eta js P) k y hy

include e μ hH b ω hG hU q ν hQ in

theorem joinedPairQuotientFast_top_le
    (hzero : ∀ j ∈ js, ∀ a ∈ U j,
      basisGradeProjection ((G j).associatedGradedBasis (b j) (ω j) (hG j)) (ω j) s a = a →
      (G j).gradedFrequency (b j) (ω j) (hG j) (pairFrequency (eta j) (theta j)) a = 0) :
    (F.pivotProductQuotientFiltration π eta js P).gradedRefiltrationLayer
      (F.joinedPairQuotientFast P G ρ hproj U js eta π) s ≤
      F.joinedFrequencyQuotientTop π eta js (fun j => (theta j).comp (ρ j).toLinearMap) := by
  rw [F.joinedPairQuotientFast_layer_eq P G ρ hproj e μ hH b ω hG U js hU eta π q ν hQ s]
  exact F.joinedPairFastTop_quotient_le (F.prod P) G ρ hproj b ω hG U js eta theta hzero
    (fun _ hx => hx.1) π

include e μ hH b ω hG hU q ν hQ in

theorem joinedPairQuotientFast_top_kernel_eq_zero
    (hzero : ∀ j ∈ js, ∀ a ∈ U j,
      basisGradeProjection ((G j).associatedGradedBasis (b j) (ω j) (hG j)) (ω j) s a = a →
      (G j).gradedFrequency (b j) (ω j) (hG j) (pairFrequency (eta j) (theta j)) a = 0)
    (x : (L ⧸ F.pivotAnnihilatorIdeal π eta js) × W)
    (hx : x ∈ (F.pivotProductQuotientFiltration π eta js P).gradedRefiltrationLayer
      (F.joinedPairQuotientFast P G ρ hproj U js eta π) s)
    (hkernel : F.pivotProductMarkedMap π eta js x = 0) : x = 0 :=
  F.joinedFrequencyQuotientTop_kernel_eq_zero π eta js
    (fun j => (theta j).comp (ρ j).toLinearMap) x
    (F.joinedPairQuotientFast_top_le P G ρ hproj e μ hH b ω hG U js hU eta theta π q ν hQ hzero hx)
    hkernel

end ActualPivotQuotient

end Erdos3.NilpotentLieFiltration

end

end OAI
