import OAI.Combinatorics.Progressions.Estimates.FreeWeightedEvaluationBounds
import OAI.Combinatorics.Progressions.Linear.FreeWeightedRankGenerators
import OAI.Combinatorics.Progressions.Polynomial.DegreeRankAdaptedBasis

namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def quotientLie (I : LieIdeal ℚ L) {t : ℕ} (ht : t ≤ s)
    (hI : F.layer s (t + 1) ≤ I.toSubmodule) : DegreeRankLieFiltration (L ⧸ I) s t where
  rank_le_degree := ht
  layer d i := (F.layer d i).map (lieQuotientMap I).toLinearMap
  lex_antitone := fun h => Submodule.map_mono (F.lex_antitone h)
  one_eq_top := by
    rw [F.one_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective I)
  rank_zero_eq_one := fun d => congrArg (Submodule.map (lieQuotientMap I).toLinearMap)
    (F.rank_zero_eq_one d)
  overshoot := fun d i h => congrArg (Submodule.map (lieQuotientMap I).toLinearMap)
    (F.overshoot d i h)
  lie_mem := by
    rintro d e i j x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨⁅a, b⁆, F.lie_mem ha hb, (lieQuotientMap I).map_lie a b⟩
  terminal := by
    apply bot_unique
    rintro x ⟨a, ha, rfl⟩
    exact (lieQuotientMap_eq_zero I a).mpr (hI ha)

theorem quotientLie_mem (I : LieIdeal ℚ L) {t : ℕ} (ht : t ≤ s)
    (hI : F.layer s (t + 1) ≤ I.toSubmodule) {d i : ℕ} {x : L}
    (hx : x ∈ F.layer d i) :
    lieQuotientMap I x ∈ (F.quotientLie I ht hI).layer d i := ⟨x, hx, rfl⟩

def quotientRank (t : ℕ) (ht : t ≤ s) :
    DegreeRankLieFiltration (L ⧸ F.layerIdeal s (t + 1)) s t :=
  F.quotientLie (F.layerIdeal s (t + 1)) ht le_rfl

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

def FreeDegreeRankLieAlgebra (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x) :=
  FreeWeightedNilpotentLieAlgebra X s w ⧸
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1)

namespace FreeDegreeRankLieAlgebra

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)

noncomputable instance instLieRing : LieRing (FreeDegreeRankLieAlgebra X s r w hw) :=
  inferInstanceAs (LieRing (FreeWeightedNilpotentLieAlgebra X s w ⧸
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1)))

noncomputable instance instLieAlgebra : LieAlgebra ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  inferInstanceAs (LieAlgebra ℚ (FreeWeightedNilpotentLieAlgebra X s w ⧸
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1)))

noncomputable def mk : FreeWeightedNilpotentLieAlgebra X s w →ₗ⁅ℚ⁆ FreeDegreeRankLieAlgebra X s r w hw :=
  lieQuotientMap ((FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1))

theorem mk_surjective : Function.Surjective (mk X s r w hw) := lieQuotientMap_surjective _

noncomputable def projection : FreeNilpotentLieAlgebra X s →ₗ⁅ℚ⁆ FreeDegreeRankLieAlgebra X s r w hw :=
  (mk X s r w hw).comp (FreeWeightedNilpotentLieAlgebra.mk X s w)

theorem projection_surjective : Function.Surjective (projection X s r w hw) :=
  (mk_surjective X s r w hw).comp (FreeWeightedNilpotentLieAlgebra.mk_surjective X s w)

theorem mk_eq_zero (x : FreeWeightedNilpotentLieAlgebra X s w) :
    mk X s r w hw x = 0 ↔
      x ∈ (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).rankLayer s (r + 1) :=
  lieQuotientMap_eq_zero _ x

theorem lowerCentralSeries_eq_bot :
    LieModule.lowerCentralSeries ℚ (FreeDegreeRankLieAlgebra X s r w hw)
      (FreeDegreeRankLieAlgebra X s r w hw) s = ⊥ :=
  lie_quotient_lowerCentralSeries_eq_bot (FreeWeightedNilpotentLieAlgebra.lowerCentralSeries_eq_bot X s w) _

noncomputable def of (x : X) : FreeDegreeRankLieAlgebra X s r w hw :=
  mk X s r w hw (FreeWeightedNilpotentLieAlgebra.of X s w x)

noncomputable def filtration (hr : r ≤ s) : DegreeRankLieFiltration (FreeDegreeRankLieAlgebra X s r w hw) s r :=
  (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.quotientRank r hr

theorem of_mem_layer (hr : r ≤ s) (x : X) :
    of X s r w hw x ∈ (filtration X s r w hw hr).layer (w x) 1 := by
  refine ⟨FreeWeightedNilpotentLieAlgebra.of X s w x, ?_, rfl⟩
  change FreeWeightedNilpotentLieAlgebra.of X s w x ∈
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).rankLayer (w x) 1
  rw [NilpotentLieFiltration.rankLayer_one]
  exact FreeWeightedNilpotentLieAlgebra.of_mem_layer X s w hw x

instance finite [Fintype X] : Module.Finite ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  Module.Finite.of_surjective (mk X s r w hw).toLinearMap (mk_surjective X s r w hw)

theorem finrank_le [Fintype X] :
    Module.finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw) ≤ (s + 1) * (Fintype.card X + 1) ^ s :=
  (LinearMap.finrank_le_finrank_of_surjective (mk_surjective X s r w hw)).trans
    (FreeWeightedNilpotentLieAlgebra.finrank_le X s w)

end FreeDegreeRankLieAlgebra

end Erdos3

end

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (G : DegreeRankLieFiltration L s r) (w : X → ℕ) (hw : ∀ x, 0 < w x)
  (f : X → L) (hf : ∀ x, f x ∈ G.layer (w x) 0)

theorem FreeWeightedNilpotentLieAlgebra.lift_mem_degreeRank {d i : ℕ}
    {x : FreeWeightedNilpotentLieAlgebra X s w}
    (hx : x ∈ (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).rankLayer d i) :
    FreeWeightedNilpotentLieAlgebra.lift G.associatedDegree w f hf x ∈ G.layer d i := by
  apply NilpotentLieFiltration.map_rankLayer
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw) G
    (FreeWeightedNilpotentLieAlgebra.lift G.associatedDegree w f hf) ?_ hx
  intro d x hx
  exact FreeWeightedNilpotentLieAlgebra.lift_mem_layer G.associatedDegree w f hf hw hx

namespace FreeDegreeRankLieAlgebra

noncomputable def lift : FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆ L :=
  lieQuotientDescend
    ((FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1))
    (FreeWeightedNilpotentLieAlgebra.lift G.associatedDegree w f hf)
    (fun x hx => by
      have h := FreeWeightedNilpotentLieAlgebra.lift_mem_degreeRank G w hw f hf hx
      simpa only [G.terminal, Submodule.mem_bot] using h)

theorem lift_mk (x : FreeWeightedNilpotentLieAlgebra X s w) :
    lift G w hw f hf (mk X s r w hw x) =
      FreeWeightedNilpotentLieAlgebra.lift G.associatedDegree w f hf x := rfl

theorem lift_projection (x : FreeNilpotentLieAlgebra X s) :
    lift G w hw f hf (projection X s r w hw x) =
      FreeNilpotentLieAlgebra.lift f G.associatedDegree.lowerCentralSeries_eq_bot x := rfl

@[simp] theorem lift_of (x : X) : lift G w hw f hf (of X s r w hw x) = f x :=
  FreeWeightedNilpotentLieAlgebra.lift_of G.associatedDegree w f hf x

theorem lift_mem_layer (hr : r ≤ s) {d i : ℕ} {x : FreeDegreeRankLieAlgebra X s r w hw}
    (hx : x ∈ (filtration X s r w hw hr).layer d i) : lift G w hw f hf x ∈ G.layer d i := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact FreeWeightedNilpotentLieAlgebra.lift_mem_degreeRank G w hw f hf ha

theorem hom_ext {φ ψ : FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆ L}
    (h : ∀ x, φ (of X s r w hw x) = ψ (of X s r w hw x)) : φ = ψ := by
  have heq : φ.comp (mk X s r w hw) = ψ.comp (mk X s r w hw) :=
    FreeWeightedNilpotentLieAlgebra.hom_ext w h
  apply LieHom.ext
  intro x
  obtain ⟨a, rfl⟩ := mk_surjective X s r w hw x
  exact LieHom.congr_fun heq a

end FreeDegreeRankLieAlgebra

end Erdos3

end

section

namespace Erdos3

namespace FreeWeightedNilpotentLieAlgebra

variable (X : Type*) [Fintype X] (s : ℕ) (w : X → ℕ)

noncomputable def canonicalRankGenerators (d k : ℕ) : Finset (FreeWeightedNilpotentLieAlgebra X s w) := by
  classical
  exact layerGenerators X s w (d + 1) ∪
    finiteWeightedLieValues (rankAlphabetVector X s w) (rankAlphabetWeight X s w) d k

theorem canonicalRankGenerators_span (hw : ∀ x, 0 < w x) (d k : ℕ) :
    Submodule.span ℚ (canonicalRankGenerators X s w d k : Set _) =
      (filtration X s w hw).rankLayer d k := by
  classical
  rw [(filtration X s w hw).rankLayer_eq_weighted_tree_span
    (rankAlphabetVector X s w) (rankAlphabetWeight X s w) (rankAlphabetWeight_pos X s w)
    (rankAlphabetVector_mem X s w hw) (rankAlphabet_spans_layer X s w hw)]
  simp only [canonicalRankGenerators, Finset.coe_union, Submodule.span_union]
  rw [← layer_eq_span X s w hw (d + 1),
    weightedLieTreeSpan_eq_finite_span _ _ (rankAlphabetWeight_pos X s w)]

end FreeWeightedNilpotentLieAlgebra

namespace FreeDegreeRankLieAlgebra

open Module

variable (X : Type*) [Fintype X] (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)

noncomputable def layerGenerators (d k : ℕ) : Finset (FreeDegreeRankLieAlgebra X s r w hw) := by
  classical
  exact (FreeWeightedNilpotentLieAlgebra.canonicalRankGenerators X s w d k).image (mk X s r w hw)

theorem layer_eq_span (hr : r ≤ s) (d k : ℕ) :
    (filtration X s r w hw hr).layer d k = Submodule.span ℚ (layerGenerators X s r w hw d k : Set _) := by
  classical
  change ((FreeWeightedNilpotentLieAlgebra.filtration X s w hw).rankLayer d k).map
    (mk X s r w hw).toLinearMap = _
  rw [← FreeWeightedNilpotentLieAlgebra.canonicalRankGenerators_span X s w hw d k, Submodule.map_span]
  simp only [layerGenerators, Finset.coe_image]
  rfl

noncomputable def layerFamily (hr : r ≤ s) (d k : ℕ)
    (x : layerGenerators X s r w hw d k) : (filtration X s r w hw hr).layer d k :=
  ⟨x.val, by rw [layer_eq_span]; exact Submodule.subset_span x.property⟩

theorem layerFamily_span (hr : r ≤ s) (d k : ℕ) :
    Submodule.span ℚ (Set.range (layerFamily X s r w hw hr d k)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff _ _).mpr
  have hrange : Set.range (Subtype.val : layerGenerators X s r w hw d k →
      FreeDegreeRankLieAlgebra X s r w hw) = (layerGenerators X s r w hw d k : Set _) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [hrange]
  exact (layer_eq_span X s r w hw hr d k).symm

theorem layerGenerators_logHeight {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ (FreeDegreeRankLieAlgebra X s r w hw)) {p : ℝ}
    (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p)
    (hgen : ∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
      rationalLogHeight (b.repr (projection X s r w hw x) i) ≤ p)
    (d k : ℕ) (hd : d ≤ s) (x : FreeDegreeRankLieAlgebra X s r w hw)
    (hx : x ∈ layerGenerators X s r w hw d k) (j : ι) :
    rationalLogHeight (b.repr x j) ≤ (p + 3) ^ (6 * s + 2) := by
  classical
  let H := ⌈Real.exp p⌉₊
  have hv (a : FreeWeightedNilpotentLieAlgebra.RankAlphabet X s w) (i : ι) :
      RationalHeightLE (b.repr (mk X s r w hw (FreeWeightedNilpotentLieAlgebra.rankAlphabetVector X s w a)) i) H := by
    obtain ⟨z, hz, hza⟩ := Finset.mem_image.mp a.2.property
    change RationalHeightLE (b.repr (mk X s r w hw a.2.val) i) H
    rw [← hza]
    exact rationalHeightLE_ceil_exp
      (hgen z (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w _ hz) i)
  have hraw : RationalHeightLE (b.repr x j) (lieTreeHeight (Fintype.card ι) H s) := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact (rationalHeightLE_ceil_exp
        (hgen z (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w _ hz) j)).mono
          (lieTreeHeight_ge_input _ _ _)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      rw [map_lieTreeEval]
      exact (finiteLieTrees_coordinate_height b
        (fun a => mk X s r w hw (FreeWeightedNilpotentLieAlgebra.rankAlphabetVector X s w a))
        (fun i j k => rationalHeightLE_ceil_exp (hc i j k)) hv d a (Finset.mem_filter.mp ha).1 j).mono
          (lieTreeHeight_mono _ _ hd)
  apply rationalLogHeight_le_of_height hraw
  simpa only [show p + 1 + 2 = p + 3 by ring] using
    lieTreeHeight_le_exp (Fintype.card ι) H s
      (hp.trans (le_add_of_nonneg_right zero_le_one))
      (hn.trans (le_add_of_nonneg_right zero_le_one)) (ceil_exp_le_exp_add_one hp)

end FreeDegreeRankLieAlgebra

end Erdos3

end

section

namespace Erdos3.FreeDegreeRankLieAlgebra

open Module
open scoped Matrix

variable {X ι κ L : Type*} [Fintype X] [Fintype ι] [Fintype κ] [DecidableEq κ]
  [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}

theorem lift_basis_matrix_logHeight
    (F : DegreeRankLieFiltration L s r) (w : X → ℕ) (hw : ∀ x, 0 < w x) (f : X → L)
    (hf : ∀ x, f x ∈ F.layer (w x) 0)
    (e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s))
    (he : ∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s)
    (b : Basis κ ℚ (FreeDegreeRankLieAlgebra X s r w hw)) (t : Basis ι ℚ L)
    (S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) κ ℚ)
    (hS : LinearMap.toMatrix e b (projection X s r w hw).toLinearMap * S = 1)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ p)
    (ht : (Fintype.card ι : ℝ) ≤ p)
    (hSH : ∀ i j, rationalLogHeight (S i j) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants t i j k) ≤ p)
    (hg : ∀ x i, rationalLogHeight (t.repr (f x) i) ≤ p) (i : ι) (j : κ) :
    rationalLogHeight (LinearMap.toMatrix b t (lift F w hw f hf).toLinearMap i j) ≤
      ((p + 3) ^ (6 * s + 2) + p + 2) ^ 4 := by
  classical
  let R := (p + 3) ^ (6 * s + 2) + p
  have hpR : p ≤ R := le_add_of_nonneg_left (by positivity)
  have hpowR : (p + 3) ^ (6 * s + 2) ≤ R := le_add_of_nonneg_right hp
  let σ := Matrix.toLin b e S
  have hσ : projection X s r w hw (σ (b j)) = b j := basisMatrix_section e b (projection X s r w hw).toLinearMap S hS (b j)
  have hcoord (k) : e.repr (σ (b j)) k = S k j := by
    simpa only [σ, LinearMap.toMatrix_toLin] using
      (LinearMap.toMatrix_apply b e (Matrix.toLin b e S) k j).symm
  rw [LinearMap.toMatrix_apply]
  have heval : lift F w hw f hf (b j) =
      FreeNilpotentLieAlgebra.lift f F.associatedDegree.lowerCentralSeries_eq_bot (σ (b j)) := by
    calc
      _ = lift F w hw f hf (projection X s r w hw (σ (b j))) := congrArg (lift F w hw f hf) hσ.symm
      _ = _ := lift_projection F w hw f hf (σ (b j))
  change rationalLogHeight (t.repr (lift F w hw f hf (b j)) i) ≤ (R + 2) ^ 4
  rw [heval]
  apply linearMap_coordinate_logHeight e t
    (FreeNilpotentLieAlgebra.lift f F.associatedDegree.lowerCentralSeries_eq_bot).toLinearMap (hp.trans hpR)
    (by simpa only [Fintype.card_fin] using hn.trans hpR) ?_ (σ (b j)) ?_ i
  · intro u v
    have h := FreeNilpotentLieAlgebra.lift_basis_matrix_logHeight t f
      F.associatedDegree.lowerCentralSeries_eq_bot e he hp ht hc hg v u
    apply le_trans _ hpowR
    simpa only [LinearMap.toMatrix_apply] using h
  · intro k
    rw [hcoord]
    exact (hSH k j).trans hpR

end Erdos3.FreeDegreeRankLieAlgebra

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_free_degree_rank_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (r : ℕ) (w : X → ℕ)
      (hw : ∀ x, 0 < w x) (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw) : ℝ) ≤ (p + C) ^ C ∧
      ∃ b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
          (FreeDegreeRankLieAlgebra X s r w hw),
        (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C) ∧
        (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) i) ≤ (p + C) ^ C) ∧
        ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
          (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
          (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
          ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
              (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ,
            LinearMap.toMatrix e b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap * S = 1 ∧
            ∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hmodel⟩ := exists_bounded_free_weighted_model s
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let V₀ : Polynomial ℕ := (Polynomial.C (s + 1) * (Polynomial.X + 2) ^ (3 ^ s) + 2) ^ (3 ^ s)
  let T₀ := B₀ + V₀ + (B₀ + 3) ^ (6 * s + 2) + 2
  let W₀ := T₀ + (T₀ + 3) ^ 51
  let R₀ := (W₀ + 2) ^ 4 + W₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R₀ + (R₀ + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro X _ r w hw p hp hX
  classical
  let B := (p + a) ^ a
  let V := (((s + 1 : ℕ) : ℝ) * (p + 2) ^ (3 ^ s) + 2) ^ (3 ^ s)
  let E := (B + 3) ^ (6 * s + 2)
  let T := B + V + E + 2
  let W := T + (T + 3) ^ 51
  let R := (W + 2) ^ 4 + W
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hBT : B ≤ T := (le_add_of_nonneg_right hV).trans
    ((le_add_of_nonneg_right hE).trans (le_add_of_nonneg_right (by norm_num)))
  have hVT : V ≤ T := (le_add_of_nonneg_left hB).trans
    ((le_add_of_nonneg_right hE).trans (le_add_of_nonneg_right (by norm_num)))
  have hET : E ≤ T := (le_add_of_nonneg_left (add_nonneg hB hV)).trans
    (le_add_of_nonneg_right (by norm_num))
  have hT : 0 ≤ T := hB.trans hBT
  have hTW : T ≤ W := le_add_of_nonneg_right (by positivity)
  have hW : 0 ≤ W := hT.trans hTW
  have hWR : W ≤ R := le_add_of_nonneg_left (by positivity)
  have hR : 0 ≤ R := hW.trans hWR
  have hprojR : (W + 2) ^ 4 ≤ R := le_add_of_nonneg_right hW
  have hsmall (k : ℕ) (hk : k ≤ 51) : (T + 1 + 2) ^ k ≤ W := by
    rw [show T + 1 + 2 = T + 3 from
      (add_assoc T 1 2).trans (congrArg (fun z : ℝ => T + z) (by norm_num))]
    exact (pow_le_pow_right₀ (by linarith only [hT]) hk).trans (le_add_of_nonneg_left hT)
  have hsum : R + (R + 3) ^ 5 ≤ (p + C) ^ C := by
    simpa [B₀, V₀, T₀, W₀, R₀, B, V, E, T, W, R, Polynomial.eval₂_pow] using hbudget p hp
  have hRC : R ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (R + 3) ^ 5)).trans hsum
  have hSC : (R + 3) ^ 5 ≤ (p + C) ^ C := (le_add_of_nonneg_left hR).trans hsum
  have hBC : B ≤ (p + C) ^ C := hBT.trans (hTW.trans (hWR.trans hRC))
  obtain ⟨hdim, e, _, _, _, _, _, hc, hgen, e₀, he₀, hdim₀, _⟩ := hmodel X w hw p hp hX
  let A := FreeWeightedNilpotentLieAlgebra.topRankGenerators X s w (r + 1)
  let I := (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1)
  let v : A → FreeWeightedNilpotentLieAlgebra X s w := Subtype.val
  have hrange : Set.range v = (A : Set (FreeWeightedNilpotentLieAlgebra X s w)) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule := by
    rw [hrange]
    exact FreeWeightedNilpotentLieAlgebra.topRankGenerators_span X s w hw (r + 1)
  have hcount : (Fintype.card A : ℝ) ≤ V := by
    have hcard := FreeWeightedNilpotentLieAlgebra.topRankGenerators_card_le X s w (r + 1)
    have hbase := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Fintype.card X + 2)
      (add_le_add hX (le_refl (2 : ℝ))) (3 ^ s)
    calc
      _ ≤ (((s + 1 : ℕ) : ℝ) * ((Fintype.card X : ℝ) + 2) ^ (3 ^ s) + 2) ^ (3 ^ s) := by
        simpa only [A, Fintype.card_coe, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          using (Nat.cast_le.mpr hcard : ((FreeWeightedNilpotentLieAlgebra.topRankGenerators X s w (r + 1)).card : ℝ) ≤ _)
      _ ≤ V := pow_le_pow_left₀ (by positivity)
        (add_le_add (mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg (s + 1))) (le_refl (2 : ℝ))) _
  have hv (i) (j : A) : rationalLogHeight (e.repr (v j) i) ≤ T :=
    (FreeWeightedNilpotentLieAlgebra.topRankGenerators_logHeight X s w e hB
      (by simpa only [Fintype.card_fin] using hdim) hc hgen (r + 1) j.val j.property i).trans hET
  obtain ⟨d, hd, b, D, _, hmatrix, _, hD, _, hbracket⟩ :=
    exists_lie_quotient_basis_exp_height e I v hspan (one_le_ceil_exp T)
      (fun i j => rationalHeightLE_ceil_exp (hv i j))
      (fun i j k => rationalHeightLE_ceil_exp ((hc i j k).trans hBT))
      (hT.trans (le_add_of_nonneg_right zero_le_one))
      (by simpa only [Fintype.card_fin] using hdim.trans (hBT.trans (le_add_of_nonneg_right zero_le_one)))
      (hcount.trans (hVT.trans (le_add_of_nonneg_right zero_le_one)))
      (ceil_exp_le_exp_add_one hT)
  change Basis (Fin d) ℚ (FreeDegreeRankLieAlgebra X s r w hw) at b
  change LinearMap.toMatrix e b (FreeDegreeRankLieAlgebra.mk X s r w hw).toLinearMap = D at hmatrix
  have hfin : finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw) = d := by
    simpa only [Fintype.card_fin] using finrank_eq_card_basis b
  subst d
  have hdimq : (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw) : ℝ) ≤ B :=
    (Nat.cast_le.mpr (by simpa only [Fintype.card_fin] using hd)).trans hdim
  have hD' (i j) : rationalLogHeight (D i j) ≤ W :=
    ((rationalLogHeight_le_iff _ _).mpr (hD i j)).trans (hsmall 7 (by omega))
  have htree (x : FreeNilpotentLieAlgebra X s)
      (hx : x ∈ FreeNilpotentLieAlgebra.treeGenerators X s) (j) :
      rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) j) ≤ R := by
    apply le_trans _ hprojR
    apply linearMap_coordinate_logHeight e b (FreeDegreeRankLieAlgebra.mk X s r w hw).toLinearMap hW
      (by simpa only [Fintype.card_fin] using hdim.trans (hBT.trans hTW)) ?_
      (FreeWeightedNilpotentLieAlgebra.mk X s w x) (fun i => (hgen x hx i).trans (hBT.trans hTW)) j
    intro i j
    have h := hD' j i
    rw [← hmatrix, LinearMap.toMatrix_apply] at h
    exact h
  let M := LinearMap.toMatrix e₀ b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap
  have hM (i j) : rationalLogHeight (M i j) ≤ R := by
    dsimp only [M]
    rw [LinearMap.toMatrix_apply]
    exact htree (e₀ j) (he₀ j) i
  obtain ⟨S, hMS, hS⟩ := exists_rational_section_exp_height M
    (basisMatrix_surjective e₀ b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap
      (FreeDegreeRankLieAlgebra.projection_surjective X s r w hw))
    (one_le_ceil_exp R) (fun i j => rationalHeightLE_ceil_exp (hM i j))
    (hR.trans (le_add_of_nonneg_right zero_le_one))
    (by simpa only [Fintype.card_fin] using (hdimq.trans
      (hBT.trans (hTW.trans (hWR.trans (le_add_of_nonneg_right zero_le_one))))))
    (ceil_exp_le_exp_add_one hR)
  refine ⟨hdimq.trans hBC, b, ?_, fun x hx i => (htree x hx i).trans hRC,
    e₀, he₀, hdim₀.trans hBC, S, hMS, ?_⟩
  · intro i j k
    exact ((rationalLogHeight_le_iff _ _).mpr (hbracket i j k)).trans
      ((hsmall 51 (by omega)).trans (hWR.trans hRC))
  · intro i j
    apply le_trans ((rationalLogHeight_le_iff _ _).mpr (hS i j))
    simpa only [show R + 1 + 2 = R + 3 from
      (add_assoc R 1 2).trans (congrArg (fun z : ℝ => R + z) (by norm_num))] using hSC

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_adapted_free_degree_rank_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (r : ℕ) (hr : r ≤ s)
      (w : X → ℕ) (hw : ∀ x, 0 < w x) (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw) : ℝ) ≤ (p + C) ^ C ∧
      ∃ b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
          (FreeDegreeRankLieAlgebra X s r w hw),
        IsCentralLieBasis b ∧
        (∀ i j, ∃ c ≤ finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw),
          (FreeDegreeRankLieAlgebra.filtration X s r w hw hr).layer i j = basisTail b c) ∧
        (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C) ∧
        (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) i) ≤ (p + C) ^ C) ∧
        ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
          (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
          (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
          ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
              (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ,
            LinearMap.toMatrix e b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap * S = 1 ∧
            ∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hmodel⟩ := exists_bounded_free_degree_rank_model s
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let P₀ := (B₀ + 3) ^ (6 * s + 2)
  let Q₀ := P₀ + (P₀ + 3) ^ 5
  let R₀ := (Q₀ + 2) ^ 4 + (P₀ + 3) ^ 11 + B₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R₀ + (R₀ + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro X _ r hr w hw p hp hX
  classical
  let B := (p + a) ^ a
  let P := (B + 3) ^ (6 * s + 2)
  let Q := P + (P + 3) ^ 5
  let R := (Q + 2) ^ 4 + (P + 3) ^ 11 + B
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hBP : B ≤ P :=
    (le_power_budget hB (by omega : 1 ≤ 6 * s + 2)).trans
      (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl B) (by norm_num : (2 : ℝ) ≤ 3)) _)
  have hPQ : P ≤ Q := le_add_of_nonneg_right (by positivity)
  have hIQ : (P + 3) ^ 5 ≤ Q := le_add_of_nonneg_left hP
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hBR : B ≤ R := le_add_of_nonneg_left (by positivity)
  have hR : 0 ≤ R := hB.trans hBR
  have hprojectionR : (Q + 2) ^ 4 ≤ R :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (P + 3) ^ 11)).trans (le_add_of_nonneg_right hB)
  have hstructureR : (P + 3) ^ 11 ≤ R :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (Q + 2) ^ 4)).trans (le_add_of_nonneg_right hB)
  have hsum : R + (R + 3) ^ 5 ≤ (p + C) ^ C := by
    simpa [B₀, P₀, Q₀, R₀, B, P, Q, R, Polynomial.eval₂_pow] using hbudget p hp
  have hRC : R ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (R + 3) ^ 5)).trans hsum
  have hSC : (R + 3) ^ 5 ≤ (p + C) ^ C := (le_add_of_nonneg_left hR).trans hsum
  obtain ⟨hdim, q, hc, hgen, e, he, hdim₀, _⟩ := hmodel X r w hw p hp hX
  let F := FreeDegreeRankLieAlgebra.filtration X s r w hw hr
  let v (i j : Fin (s + 1)) := FreeDegreeRankLieAlgebra.layerFamily X s r w hw hr i.val j.val
  have hv (i j : Fin (s + 1)) (x : FreeDegreeRankLieAlgebra.layerGenerators X s r w hw i.val j.val) (k) :
      rationalLogHeight (q.repr (v i j x : FreeDegreeRankLieAlgebra X s r w hw) k) ≤ P := by
    exact FreeDegreeRankLieAlgebra.layerGenerators_logHeight X s r w hw q hB
      (by simpa only [Fintype.card_fin] using hdim) hc hgen i.val j.val
      (Nat.le_of_lt_succ i.isLt) x.val x.property k
  obtain ⟨b, hcentral, hlayer, _, hinverse, hstructure⟩ := F.exists_rank_adapted_basis_logHeight q v
    (fun i j => FreeDegreeRankLieAlgebra.layerFamily_span X s r w hw hr i.val j.val) hP
    (by simpa only [Fintype.card_fin] using hdim.trans hBP) hv
    (fun i j k => (hc i j k).trans hBP)
  have htree (x : FreeNilpotentLieAlgebra X s)
      (hx : x ∈ FreeNilpotentLieAlgebra.treeGenerators X s) (j) :
      rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) j) ≤ R := by
    apply le_trans _ hprojectionR
    exact linearMap_coordinate_logHeight q b LinearMap.id hQ
      (by simpa only [Fintype.card_fin] using hdim.trans (hBP.trans hPQ))
      (fun i k => (hinverse i k).trans hIQ) (FreeDegreeRankLieAlgebra.projection X s r w hw x)
      (fun i => (hgen x hx i).trans (hBP.trans hPQ)) j
  let A := LinearMap.toMatrix e b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap
  have hA (i j) : rationalLogHeight (A i j) ≤ R := by
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact htree (e j) (he j) i
  obtain ⟨S, hAS, hS⟩ := exists_rational_section_exp_height A
    (basisMatrix_surjective e b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap
      (FreeDegreeRankLieAlgebra.projection_surjective X s r w hw))
    (one_le_ceil_exp R) (fun i j => rationalHeightLE_ceil_exp (hA i j))
    (hR.trans (le_add_of_nonneg_right zero_le_one))
    (by simpa only [Fintype.card_fin] using
      (hdim.trans (hBR.trans (le_add_of_nonneg_right zero_le_one))))
    (ceil_exp_le_exp_add_one hR)
  refine ⟨hdim.trans (hBR.trans hRC), b, hcentral, hlayer,
    fun i j k => (hstructure i j k).trans (hstructureR.trans hRC),
    fun x hx i => (htree x hx i).trans hRC, e, he, hdim₀.trans (hBR.trans hRC), S, hAS, ?_⟩
  intro i j
  apply le_trans ((rationalLogHeight_le_iff _ _).mpr (hS i j))
  simpa only [show R + 1 + 2 = R + 3 from
    (add_assoc R 1 2).trans (congrArg (fun z : ℝ => R + z) (by norm_num))] using hSC

end Erdos3

end

end OAI
