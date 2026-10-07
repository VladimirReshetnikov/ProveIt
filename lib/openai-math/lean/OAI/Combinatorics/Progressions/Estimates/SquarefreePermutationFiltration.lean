/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Algebra.Lie.Prod
import OAI.Combinatorics.Progressions.Geometry.SquarefreeAlgebraCoordinates
import OAI.Combinatorics.Progressions.Nilpotent.BCHConjugationLinear
import OAI.Combinatorics.Progressions.Nilpotent.SquarefreeSupportBracket
import OAI.Combinatorics.Progressions.Polynomial.AdaptedBinomialFactorization
import OAI.Combinatorics.Progressions.Polynomial.DegreeRankSunflower
import OAI.Combinatorics.Progressions.Polynomial.RealBlockPolynomialEval
import OAI.Combinatorics.Progressions.Polynomial.SquarefreeTotalDegree

namespace OAI

section

namespace Erdos3

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

theorem squarefreePermute_monomial_lie (e : ι ≃ κ) (a b : SquarefreeIndex ι) (v w : L) :
    squarefreePermute e ⁅squarefreeMonomial a v, squarefreeMonomial b w⁆ =
      ⁅squarefreePermute e (squarefreeMonomial a v),
        squarefreePermute e (squarefreeMonomial b w)⁆ := by
  by_cases hab : Disjoint a.val.support b.val.support
  · rw [squarefreeMonomial_lie_disjoint a b hab]
    simp only [squarefreePermute_monomial]
    rw [squarefreeMonomial_lie_disjoint _ _ ((SquarefreeIndex.permute_disjoint e a b).mpr hab),
      SquarefreeIndex.permute_disjointAdd]
  · rw [squarefreeMonomial_lie_overlap a b hab, map_zero]
    simp only [squarefreePermute_monomial]
    rw [squarefreeMonomial_lie_overlap _ _
      (fun h => hab ((SquarefreeIndex.permute_disjoint e a b).mp h))]

theorem squarefreePermute_lie (e : ι ≃ κ) (x y : SquarefreePolynomial ι L) :
    squarefreePermute e ⁅x, y⁆ = ⁅squarefreePermute e x, squarefreePermute e y⁆ := by
  classical
  conv_lhs =>
    rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y, sum_lie_sum]
    simp only [map_sum]
  conv_rhs =>
    rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y]
    simp only [map_sum]
    rw [sum_lie_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact squarefreePermute_monomial_lie e a b _ _

noncomputable def squarefreePermuteLie (e : ι ≃ κ) :
    SquarefreePolynomial ι L ≃ₗ⁅ℚ⁆ SquarefreePolynomial κ L :=
  { squarefreePermute e with map_lie' := squarefreePermute_lie e _ _ }

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}

theorem layer_eq_bot_above_step (F : NilpotentLieFiltration L s) {i : ℕ}
    (hi : s < i) : F.layer i = ⊥ := by
  apply bot_unique
  rw [← F.terminal]
  exact F.antitone (by omega)

def raiseStep (F : NilpotentLieFiltration L s) (hst : s ≤ t) : NilpotentLieFiltration L t where
  layer := F.layer
  antitone := F.antitone
  one_eq_top := F.one_eq_top
  lie_mem := F.lie_mem
  terminal := F.layer_eq_bot_above_step (by omega)

theorem raiseStep_layer (F : NilpotentLieFiltration L s) (hst : s ≤ t) (i : ℕ) :
    (F.raiseStep hst).layer i = F.layer i := rfl

theorem raiseStep_realification_layer (F : NilpotentLieFiltration L s) (hst : s ≤ t) (i : ℕ) :
    (F.raiseStep hst).realification.layer i = F.realification.layer i := rfl

noncomputable def raiseStepOrbit (F : NilpotentLieFiltration L s) (hst : s ≤ t)
    {σ : Type*} {w : σ → ℕ} (g : F.PolynomialOrbit w) : (F.raiseStep hst).PolynomialOrbit w :=
  polynomialOrbitOfLog g.log g.adapted

theorem raiseStepOrbit_log (F : NilpotentLieFiltration L s) (hst : s ≤ t)
    {σ : Type*} {w : σ → ℕ} (g : F.PolynomialOrbit w) :
    (F.raiseStepOrbit hst g).log = g.log := rfl

end Erdos3.NilpotentLieFiltration

namespace Erdos3

open Module

theorem bchSubgroupCoordinates_changeStep
    {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
    (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥)
    (e : Basis ι ℚ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hs)) :
    bchSubgroupCoordinates e (Γ.map (NilpotentLieBCHGroup.changeStep hs ht).toMonoidHom) =
      bchSubgroupCoordinates e Γ := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg, heq⟩ := Subgroup.mem_map.mp hx
    have hcoord := congrArg NilpotentLieBCHGroup.coord heq
    have hg' : g = ⟨e.equivFun.symm x⟩ := NilpotentLieBCHGroup.ext hcoord
    change (⟨e.equivFun.symm x⟩ : NilpotentLieBCHGroup L s hs) ∈ Γ
    rwa [← hg']
  · intro hx
    exact Subgroup.mem_map.mpr ⟨⟨e.equivFun.symm x⟩, hx, rfl⟩

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeComponent (a : SquarefreeIndex ι) :
    F.SquarefreeAlgebra π →ₗ[ℚ] F.SquarefreeAlgebra π where
  toFun x := ⟨squarefreeMonomial a (squarefreePolynomialEquiv x.val a),
    F.squarefreeMonomial_component_mem π x.val x.property a⟩
  map_add' x y := by
    apply Subtype.ext
    change squarefreeMonomial a (squarefreePolynomialEquiv (x.val + y.val) a) = _
    simp only [map_add, Pi.add_apply]
    rfl
  map_smul' r x := by
    apply Subtype.ext
    change squarefreeMonomial a (squarefreePolynomialEquiv (r • x.val) a) = _
    simp only [map_smul, Pi.smul_apply]
    rfl

theorem squarefreeComponent_apply (a : SquarefreeIndex ι) (x : F.SquarefreeAlgebra π) :
    (F.squarefreeComponent π a x).val =
      squarefreeMonomial a (squarefreePolynomialEquiv x.val a) := rfl

theorem sum_squarefreeComponent (x : F.SquarefreeAlgebra π) :
    ∑ a : SquarefreeIndex ι, F.squarefreeComponent π a x = x := by
  classical
  apply Subtype.ext
  change (F.squarefreeAdaptedSubalgebra π).incl (∑ a, F.squarefreeComponent π a x) = x.val
  rw [map_sum]
  exact sum_squarefreeMonomial x.val

theorem squarefreeAlgebra_lowerCentralSeries_eq_bot :
    LieModule.lowerCentralSeries ℚ (F.SquarefreeAlgebra π) (F.SquarefreeAlgebra π) s = ⊥ :=
  lie_subalgebra_lowerCentralSeries_eq_bot
    (squarefreePolynomial_lowerCentralSeries_eq_bot F.ordinary.lowerCentralSeries_eq_bot)
    (F.squarefreeAdaptedSubalgebra π)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (hF : F.layer (s + 1) = ⊥)

def dropTop : NilpotentLieFiltration L s where
  layer := F.layer
  antitone := F.antitone
  one_eq_top := F.one_eq_top
  lie_mem := F.lie_mem
  terminal := hF

@[simp] theorem dropTop_layer (i : ℕ) : (F.dropTop hF).layer i = F.layer i := rfl

@[simp] theorem dropTop_realification_layer (i : ℕ) :
    (F.dropTop hF).realification.layer i = F.realification.layer i := rfl

end Erdos3.NilpotentLieFiltration

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem rank_zero_top_eq_bot (F : DegreeRankLieFiltration L s 0) :
    F.associatedDegree.layer s = ⊥ := by
  change F.layer s 0 = ⊥
  rw [F.rank_zero_eq_one]
  exact F.terminal

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeMultidegreeLayer (c : ι → ℕ) : Submodule ℚ (F.SquarefreeAlgebra π) :=
  (squarefreeSupportModule (fun a : SquarefreeIndex ι => c ≤ fun i => a.val i)).comap
    (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap

noncomputable def squarefreeDegreeLayer (n : ℕ) : Submodule ℚ (F.SquarefreeAlgebra π) :=
  (squarefreeSupportModule (fun a : SquarefreeIndex ι => n ≤ ∑ i, a.val i)).comap
    (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap

theorem mem_squarefreeMultidegreeLayer (c : ι → ℕ) (x : F.SquarefreeAlgebra π) :
    x ∈ F.squarefreeMultidegreeLayer π c ↔
      ∀ a : SquarefreeIndex ι, ¬c ≤ (fun i => a.val i) → squarefreePolynomialEquiv x.val a = 0 :=
  Iff.rfl

theorem mem_squarefreeDegreeLayer (n : ℕ) (x : F.SquarefreeAlgebra π) :
    x ∈ F.squarefreeDegreeLayer π n ↔
      ∀ a : SquarefreeIndex ι, ¬n ≤ ∑ i, a.val i → squarefreePolynomialEquiv x.val a = 0 :=
  Iff.rfl

theorem squarefreeMultidegreeLayer_antitone : Antitone (F.squarefreeMultidegreeLayer π) := by
  intro c d h x hx a ha
  exact hx a (fun hd => ha (h.trans hd))

theorem squarefreeDegreeLayer_antitone : Antitone (F.squarefreeDegreeLayer π) := by
  intro n m h x hx a ha
  exact hx a (fun hm => ha (h.trans hm))

theorem squarefreeMultidegreeLayer_lie_mem {c d : ι → ℕ} {x y : F.SquarefreeAlgebra π}
    (hx : x ∈ F.squarefreeMultidegreeLayer π c) (hy : y ∈ F.squarefreeMultidegreeLayer π d) :
    ⁅x, y⁆ ∈ F.squarefreeMultidegreeLayer π (c + d) := by
  apply squarefreeSupportModule_lie_mem (x := x.val) (y := y.val) ?_ hx hy
  intro a b hab ha hb i
  exact Nat.add_le_add (ha i) (hb i)

theorem squarefreeDegreeLayer_lie_mem {n m : ℕ} {x y : F.SquarefreeAlgebra π}
    (hx : x ∈ F.squarefreeDegreeLayer π n) (hy : y ∈ F.squarefreeDegreeLayer π m) :
    ⁅x, y⁆ ∈ F.squarefreeDegreeLayer π (n + m) := by
  apply squarefreeSupportModule_lie_mem (x := x.val) (y := y.val) ?_ hx hy
  intro a b hab ha hb
  rw [squarefreeDisjointAdd_total]
  exact Nat.add_le_add ha hb

theorem squarefreeMultidegreeLayer_le_degree (c : ι → ℕ) (n : ℕ) (h : n ≤ ∑ i, c i) :
    F.squarefreeMultidegreeLayer π c ≤ F.squarefreeDegreeLayer π n := by
  intro x hx a ha
  apply hx a
  intro hca
  exact ha (h.trans (Finset.sum_le_sum fun i _ => hca i))

theorem squarefreeComponent_mem_multidegree (a : SquarefreeIndex ι) (x : F.SquarefreeAlgebra π) :
    F.squarefreeComponent π a x ∈ F.squarefreeMultidegreeLayer π (fun i => a.val i) := by
  exact squarefreeMonomial_mem_support a (fun _ => le_rfl) _

theorem squarefreeComponent_eq_zero_of_degree {n : ℕ} {x : F.SquarefreeAlgebra π}
    (hx : x ∈ F.squarefreeDegreeLayer π n) (a : SquarefreeIndex ι) (ha : ¬n ≤ ∑ i, a.val i) :
    F.squarefreeComponent π a x = 0 := by
  apply Subtype.ext
  change squarefreeMonomial a (squarefreePolynomialEquiv x.val a) = 0
  have hz : squarefreePolynomialEquiv x.val a = 0 := hx a ha
  rw [hz, map_zero]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeDegreeLayer_one : F.squarefreeDegreeLayer π 1 = ⊤ := by
  apply top_unique
  intro x _ a ha
  have hzero : a.val = 0 := (exponent_total_eq_zero_iff a.val).mp (by omega)
  exact (x.property a).2 hzero

theorem squarefreeDegreeLayer_terminal : F.squarefreeDegreeLayer π (Fintype.card ι + 1) = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply Subtype.ext
  apply squarefreePolynomialEquiv.injective
  ext a
  apply hx a
  have h := squarefreeExponent_total_le a
  omega

noncomputable def squarefreeOrdinaryFiltration :
    NilpotentLieFiltration (F.SquarefreeAlgebra π) (Fintype.card ι) where
  layer := F.squarefreeDegreeLayer π
  antitone := F.squarefreeDegreeLayer_antitone π
  one_eq_top := F.squarefreeDegreeLayer_one π
  lie_mem := F.squarefreeDegreeLayer_lie_mem π
  terminal := F.squarefreeDegreeLayer_terminal π

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonProductLayer (n : ℕ) : Submodule ℚ (L × F.SquarefreeAlgebra π) :=
  (F.ordinary.layer n).prod (F.squarefreeDegreeLayer π n)

theorem comparisonProductLayer_antitone : Antitone (F.comparisonProductLayer π) :=
  fun _ _ h _ hx => ⟨F.ordinary.antitone h hx.1, F.squarefreeDegreeLayer_antitone π h hx.2⟩

theorem comparisonProductLayer_lie_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonProductLayer π i) (hy : y ∈ F.comparisonProductLayer π j) :
    ⁅x, y⁆ ∈ F.comparisonProductLayer π (i + j) :=
  ⟨F.ordinary.lie_mem hx.1 hy.1, F.squarefreeDegreeLayer_lie_mem π hx.2 hy.2⟩

theorem comparisonProductLayer_one : F.comparisonProductLayer π 1 = ⊤ := by
  unfold comparisonProductLayer
  rw [F.ordinary.one_eq_top, F.squarefreeDegreeLayer_one]
  ext x
  simp only [Submodule.mem_prod, Submodule.mem_top, and_self]

theorem comparisonProductLayer_terminal :
    F.comparisonProductLayer π (max s (Fintype.card ι) + 1) = ⊥ := by
  change (F.ordinary.layer _).prod ((F.squarefreeOrdinaryFiltration π).layer _) = ⊥
  rw [F.ordinary.layer_eq_bot_above_step (by omega),
    (F.squarefreeOrdinaryFiltration π).layer_eq_bot_above_step (by omega)]
  ext x
  simp only [Submodule.mem_prod, Submodule.mem_bot, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeMultidegreeLayer_zero : F.squarefreeMultidegreeLayer π 0 = ⊤ := by
  apply top_unique
  intro x _ a ha
  exact False.elim (ha (fun _ => Nat.zero_le _))

theorem squarefreeMultidegreeLayer_terminal (c : ι → ℕ) (hc : ¬c ≤ (fun _ => 1)) :
    F.squarefreeMultidegreeLayer π c = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply Subtype.ext
  apply squarefreePolynomialEquiv.injective
  ext a
  exact hx a (fun hca => hc (fun i => (hca i).trans (a.property i)))

theorem squarefree_degree_eq (n : ℕ) :
    F.squarefreeDegreeLayer π n =
      ⨆ (c : ι → ℕ) (_hc : n ≤ ∑ i, c i), F.squarefreeMultidegreeLayer π c := by
  classical
  apply le_antisymm
  · intro x hx
    rw [← F.sum_squarefreeComponent π x]
    apply Submodule.sum_mem
    intro a _
    by_cases ha : n ≤ ∑ i, a.val i
    · have hle : F.squarefreeMultidegreeLayer π (fun i => a.val i) ≤
          ⨆ (c : ι → ℕ) (_hc : n ≤ ∑ i, c i), F.squarefreeMultidegreeLayer π c :=
        le_iSup_of_le (fun i => a.val i) (le_iSup_of_le ha le_rfl)
      exact hle (F.squarefreeComponent_mem_multidegree π a x)
    · rw [F.squarefreeComponent_eq_zero_of_degree π hx a ha]
      exact Submodule.zero_mem _
  · apply iSup_le
    intro c
    apply iSup_le
    intro hc
    exact F.squarefreeMultidegreeLayer_le_degree π c n hc

noncomputable def squarefreeMultidegreeFiltration :
    MultidegreeLieFiltration ι (F.SquarefreeAlgebra π) (Fintype.card ι) (fun _ => 1) where
  ordinary := F.squarefreeOrdinaryFiltration π
  layer := F.squarefreeMultidegreeLayer π
  antitone := F.squarefreeMultidegreeLayer_antitone π
  zero_eq_top := F.squarefreeMultidegreeLayer_zero π
  lie_mem := F.squarefreeMultidegreeLayer_lie_mem π
  terminal := F.squarefreeMultidegreeLayer_terminal π
  degree_eq := F.squarefree_degree_eq π

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

omit [Fintype ι] [Fintype σ] in
theorem blockPermutation_symm (e : ι ≃ ι) (he : ∀ i, π (e i) = π i) :
    ∀ i, π (e.symm i) = π i := by
  intro i
  simpa only [Equiv.apply_symm_apply] using (he (e.symm i)).symm

theorem squarefreePermute_mem_adapted (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (x : SquarefreePolynomial ι L) (hx : x ∈ F.squarefreeAdaptedModule π) :
    squarefreePermute e x ∈ F.squarefreeAdaptedModule π := by
  intro a
  rw [squarefreePermute_coefficient]
  have hd : blockDegree π ((SquarefreeIndex.permute e).symm a).val = blockDegree π a.val :=
    SquarefreeIndex.permute_blockDegree π e.symm (blockPermutation_symm π e he) a
  refine ⟨?_, ?_⟩
  · rw [← hd]
    exact (hx _).1
  · intro ha
    exact (hx _).2 ((SquarefreeIndex.permute_zero_iff e.symm a).mpr ha)

noncomputable def squarefreeBlockPermute (e : ι ≃ ι) (he : ∀ i, π (e i) = π i) :
    F.SquarefreeAlgebra π ≃ₗ⁅ℚ⁆ F.SquarefreeAlgebra π where
  toFun x := ⟨squarefreePermute e x.val, F.squarefreePermute_mem_adapted π e he _ x.property⟩
  invFun x := ⟨squarefreePermute e.symm x.val,
    F.squarefreePermute_mem_adapted π e.symm (blockPermutation_symm π e he) _ x.property⟩
  left_inv x := Subtype.ext (squarefreePermute_symm_apply e x.val)
  right_inv x := Subtype.ext (squarefreePermute_symm_apply e.symm x.val)
  map_add' x y := Subtype.ext (map_add (squarefreePermute e) x.val y.val)
  map_smul' r x := Subtype.ext (map_smul (squarefreePermute e) r x.val)
  map_lie' {x y} := Subtype.ext (squarefreePermute_lie e x.val y.val)

theorem squarefreeBlockPermute_apply (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (x : F.SquarefreeAlgebra π) :
    (F.squarefreeBlockPermute π e he x).val = squarefreePermute e x.val := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeLayerMap (a : SquarefreeIndex ι) :
    F.layer (blockDegree π a.val) →ₗ[ℚ] F.SquarefreeAlgebra π := by
  classical
  exact if ha : a.val = 0 then 0 else
    { toFun := fun v => ⟨squarefreeMonomial a v.val, F.squarefreeMonomial_mem_adapted π a ha v.val v.property⟩
      map_add' := fun v w => Subtype.ext (map_add (squarefreeMonomial a) v.val w.val)
      map_smul' := fun r v => Subtype.ext (map_smul (squarefreeMonomial a) r v.val) }

theorem squarefreeLayerMap_zero (a : SquarefreeIndex ι) (ha : a.val = 0)
    (v : F.layer (blockDegree π a.val)) : F.squarefreeLayerMap π a v = 0 := by
  simp only [squarefreeLayerMap, dite_eq_left ha, LinearMap.zero_apply]

theorem squarefreeLayerMap_coe (a : SquarefreeIndex ι) (ha : a.val ≠ 0)
    (v : F.layer (blockDegree π a.val)) :
    (F.squarefreeLayerMap π a v).val = squarefreeMonomial a v.val := by
  simp only [squarefreeLayerMap, dite_eq_right ha, LinearMap.coe_mk, AddHom.coe_mk]

theorem squarefreeLayerMap_mem (a : SquarefreeIndex ι) (v : F.layer (blockDegree π a.val)) :
    F.squarefreeLayerMap π a v ∈ F.squarefreeMultidegreeLayer π (fun i => a.val i) := by
  by_cases ha : a.val = 0
  · rw [F.squarefreeLayerMap_zero π a ha]
    exact Submodule.zero_mem _
  · change (F.squarefreeLayerMap π a v).val ∈ squarefreeSupportModule _
    rw [F.squarefreeLayerMap_coe π a ha]
    exact squarefreeMonomial_mem_support a (fun _ => le_rfl) v.val

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem factorialBlockMonomial_mem_adapted (a : σ → ℕ) (ha : a ≠ 0)
    (x : L) (hx : x ∈ F.layer a) :
    factorialBlockMonomial π a x ∈ F.squarefreeAdaptedModule π := by
  classical
  intro c
  rw [factorialBlockMonomial_coefficient]
  by_cases hca : blockDegree π c.val = a
  · rw [ite_eq_left hca]
    refine ⟨?_, ?_⟩
    · rw [hca]
      exact (F.layer a).smul_mem _ hx
    · intro hc
      apply False.elim
      apply ha
      rw [hc, blockDegree_zero] at hca
      exact hca.symm
  · rw [ite_eq_right hca]
    exact ⟨(F.layer _).zero_mem, fun _ => rfl⟩

noncomputable def blockLayerMap (a : σ → ℕ) (ha : a ≠ 0) :
    F.layer a →ₗ[ℚ] F.SquarefreeAlgebra π where
  toFun x := ⟨factorialBlockMonomial π a x.val,
    F.factorialBlockMonomial_mem_adapted π a ha x.val x.property⟩
  map_add' x y := Subtype.ext (map_add (factorialBlockMonomial π a) x.val y.val)
  map_smul' r x := Subtype.ext (map_smul (factorialBlockMonomial π a) r x.val)

theorem blockLayerMap_coe (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    (F.blockLayerMap π a ha x).val = factorialBlockMonomial π a x.val := rfl

theorem blockLayerMap_mem_degree (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    F.blockLayerMap π a ha x ∈ F.squarefreeDegreeLayer π (∑ i, a i) := by
  classical
  intro c hc
  change squarefreePolynomialEquiv (factorialBlockMonomial π a x.val) c = 0
  rw [factorialBlockMonomial_coefficient]
  apply ite_eq_right
  intro hca
  apply hc
  have ht : (∑ i, a i) = ∑ j, c.val j := by
    rw [← hca]
    exact blockDegree_total π c.val
  exact ht.le

theorem blockLayerMap_permute (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a)
    (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i) :
    F.squarefreeBlockPermute π e he (F.blockLayerMap π a ha x) = F.blockLayerMap π a ha x := by
  apply Subtype.ext
  rw [F.squarefreeBlockPermute_apply, F.blockLayerMap_coe]
  apply squarefreePolynomialEquiv.injective
  ext c
  classical
  simp only [squarefreePermute_coefficient, factorialBlockMonomial_coefficient,
    SquarefreeIndex.permute_symm,
    SquarefreeIndex.permute_blockDegree π e.symm (blockPermutation_symm π e he)]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

omit [Fintype ι] in
theorem SquarefreeIndex.permute_one (a : SquarefreeIndex ι) : permute (1 : Equiv.Perm ι) a = a := by
  apply Subtype.ext
  ext i
  rfl

omit [Fintype ι] in
theorem SquarefreeIndex.permute_mul (e f : Equiv.Perm ι) (a : SquarefreeIndex ι) :
    permute (e * f) a = permute e (permute f a) := by
  apply Subtype.ext
  ext i
  rfl

theorem squarefreePermute_one (x : SquarefreePolynomial ι L) :
    squarefreePermute (1 : Equiv.Perm ι) x = x := by
  apply squarefreePolynomialEquiv.injective
  ext a
  rw [squarefreePermute_coefficient]
  apply congrArg (squarefreePolynomialEquiv x)
  exact SquarefreeIndex.permute_one a

theorem squarefreePermute_mul (e f : Equiv.Perm ι) (x : SquarefreePolynomial ι L) :
    squarefreePermute (e * f) x = squarefreePermute e (squarefreePermute f x) := by
  apply squarefreePolynomialEquiv.injective
  ext a
  rw [squarefreePermute_coefficient, squarefreePermute_coefficient, squarefreePermute_coefficient]
  apply congrArg (squarefreePolynomialEquiv x)
  apply Subtype.ext
  ext i
  rfl

namespace MultidegreeLieFiltration

variable {σ : Type*} [Fintype σ] {s : ℕ} {bound : σ → ℕ}
  (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeBlockPermute_one (x : F.SquarefreeAlgebra π) :
    F.squarefreeBlockPermute π 1 (fun _ => rfl) x = x :=
  Subtype.ext (squarefreePermute_one x.val)

theorem squarefreeBlockPermute_mul (e f : Equiv.Perm ι)
    (he : ∀ i, π (e i) = π i) (hf : ∀ i, π (f i) = π i)
    (x : F.SquarefreeAlgebra π) :
    F.squarefreeBlockPermute π (e * f) (fun i => (he (f i)).trans (hf i)) x =
      F.squarefreeBlockPermute π e he (F.squarefreeBlockPermute π f hf x) :=
  Subtype.ext (squarefreePermute_mul e f x.val)

end MultidegreeLieFiltration
end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeBlockPermute_mem_degree (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (n : ℕ) (x : F.SquarefreeAlgebra π) :
    F.squarefreeBlockPermute π e he x ∈ F.squarefreeDegreeLayer π n ↔
      x ∈ F.squarefreeDegreeLayer π n := by
  apply squarefreePermute_mem_support_iff
  intro a
  rw [SquarefreeIndex.permute_total]

theorem squarefreeBlockPermute_mem_multidegree (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (c : ι → ℕ) (x : F.SquarefreeAlgebra π) :
    F.squarefreeBlockPermute π e he x ∈ F.squarefreeMultidegreeLayer π (fun i => c (e.symm i)) ↔
      x ∈ F.squarefreeMultidegreeLayer π c := by
  exact squarefreePermute_mem_support_iff e _ _
    (fun a => SquarefreeIndex.permutedBound_le_iff e c a) x.val

theorem squarefreeBlockPermute_mem_topDegree (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (x : F.SquarefreeAlgebra π) :
    F.squarefreeBlockPermute π e he x ∈ F.squarefreeMultidegreeLayer π (fun _ => 1) ↔
      x ∈ F.squarefreeMultidegreeLayer π (fun _ => 1) :=
  F.squarefreeBlockPermute_mem_multidegree π e he (fun _ => 1) x

end Erdos3.MultidegreeLieFiltration

end

end OAI
