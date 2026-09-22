import Surreal.Foundations.SmallNormalFormUnion
import Surreal.HahnSeries.WorkspaceEmbedding

/-!
# Embedding a small Hahn workspace into formal normal forms

A strictly increasing additive map of a small exponent group into the
actual surreal exponents embeds its entire real Hahn field in the formal
small-support field. Increasing Hahn exponents use the convention t^a =
omega^(-a), so the native decreasing growth exponents are negated.
This construction is entirely formal and precedes transport to actual
surreal arithmetic.
-/

universe u v

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

/-- Repackage a native Hahn series when its support is small in the birthday universe. -/
def ofHahn (x : _root_.HahnSeries (_root_.Surreal.{u}ᵒᵈ) ℝ)
    (hs : Small.{u} x.support) : SmallNormalForm.{u} :=
  _root_.SurrealHahnSeries.mk (fun a => x.coeff (OrderDual.toDual a)) hs
    x.isWF_support

@[simp] theorem ofLex_ofHahn (x : _root_.HahnSeries (_root_.Surreal.{u}ᵒᵈ) ℝ)
    (hs : Small.{u} x.support) : ofLex (ofHahn x hs).val = x := by
  ext a
  rfl

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Convert increasing valuation exponents to decreasing native growth exponents. -/
def hahnGrowthMap (e : Γ →+ SignSequence.{u}) : Γ →+ _root_.Surreal.{u}ᵒᵈ where
  toFun a := OrderDual.toDual (-toSurreal (e a))
  map_zero' := by simp
  map_add' a b := by simp only [map_add, toSurreal_add, neg_add]; rfl

omit [IsOrderedAddMonoid Γ] in
theorem hahnGrowthMap_strictMono (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    StrictMono (hahnGrowthMap e) := by
  intro a b hab
  change -toSurreal (e b) < -toSurreal (e a)
  exact neg_lt_neg ((toSurreal_lt_iff _ _).mpr (he hab))

variable [Small.{u} Γ]

private theorem small_hahnWorkspace_image (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) :
    Small.{u} (Surreal.HahnSeries.workspaceEmbedding (hahnGrowthMap e)
      (hahnGrowthMap_strictMono e he) x).support := by
  rw [Surreal.HahnSeries.support_workspaceEmbedding]
  infer_instance

/-- Every Hahn series on a small exponent workspace gives a small formal form. -/
def hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    _root_.HahnSeries Γ ℝ →+* SmallNormalForm.{u} where
  toFun x := ofHahn (Surreal.HahnSeries.workspaceEmbedding (hahnGrowthMap e)
    (hahnGrowthMap_strictMono e he) x) (small_hahnWorkspace_image e he x)
  map_zero' := by
    apply Subtype.ext
    change toLex (Surreal.HahnSeries.workspaceEmbedding (hahnGrowthMap e) (hahnGrowthMap_strictMono e he) 0) = 0
    rw [map_zero]
    rfl
  map_one' := by
    apply Subtype.ext
    change toLex (Surreal.HahnSeries.workspaceEmbedding (hahnGrowthMap e) (hahnGrowthMap_strictMono e he) 1) = 1
    rw [map_one]
    rfl
  map_add' x y := by
    apply Subtype.ext
    change toLex (Surreal.HahnSeries.workspaceEmbedding (hahnGrowthMap e) (hahnGrowthMap_strictMono e he) (x + y)) = _
    rw [map_add]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    change toLex (Surreal.HahnSeries.workspaceEmbedding (hahnGrowthMap e) (hahnGrowthMap_strictMono e he) (x * y)) = _
    rw [map_mul]
    rfl

@[simp] theorem ofLex_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) :
    ofLex (hahnEmbedding e he x).val =
      Surreal.HahnSeries.workspaceEmbedding (hahnGrowthMap e) (hahnGrowthMap_strictMono e he) x :=
  ofLex_ofHahn _ (small_hahnWorkspace_image e he x)

/-- The original coefficient occurs at the negative growth exponent. -/
@[simp] theorem coeff_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) (a : Γ) : coeff (hahnEmbedding e he x) (-e a) = x.coeff a := by
  change (ofLex (hahnEmbedding e he x).val).coeff (OrderDual.toDual (toSurreal (-e a))) = _
  rw [ofLex_hahnEmbedding, toSurreal_neg]
  exact Surreal.HahnSeries.workspaceEmbedding_coeff _ _ x a

/-- No coefficient occurs outside the embedded growth exponents. -/
theorem coeff_hahnEmbedding_of_not_mem_range (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) {b : SignSequence.{u}}
    (hb : b ∉ Set.range (fun a => -e a)) : coeff (hahnEmbedding e he x) b = 0 := by
  have hn : OrderDual.toDual (toSurreal b) ∉ Set.range (hahnGrowthMap e) := by
    rintro ⟨a, ha⟩
    apply hb
    refine ⟨a, ?_⟩
    apply (toSurreal_inj _ _).mp
    rw [toSurreal_neg]
    exact congrArg OrderDual.ofDual ha
  change (ofLex (hahnEmbedding e he x).val).coeff (OrderDual.toDual (toSurreal b)) = 0
  rw [ofLex_hahnEmbedding]
  exact Surreal.HahnSeries.workspaceEmbedding_coeff_of_not_mem_range _ _ x hn

/-- The formal support is exactly the reindexed workspace support. -/
theorem support_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) :
    support (hahnEmbedding e he x) = (fun a => -e a) '' x.support := by
  ext b
  constructor
  · intro hb
    have hr : b ∈ Set.range (fun a => -e a) := by
      by_contra hn
      exact hb (coeff_hahnEmbedding_of_not_mem_range e he x hn)
    obtain ⟨a, rfl⟩ := hr
    exact ⟨a, by simpa only [mem_support, coeff_hahnEmbedding, _root_.HahnSeries.mem_support] using hb, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    simpa only [mem_support, coeff_hahnEmbedding, _root_.HahnSeries.mem_support] using ha

/-- Single workspace monomials retain their coefficients and negate their exponents. -/
@[simp] theorem hahnEmbedding_single (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (a : Γ) (r : ℝ) :
    hahnEmbedding e he (_root_.HahnSeries.single a r) = single (-e a) r := by
  apply ext
  intro b
  rw [coeff_single]
  change (ofLex (hahnEmbedding e he (_root_.HahnSeries.single a r)).val).coeff
    (OrderDual.toDual (toSurreal b)) = _
  rw [ofLex_hahnEmbedding, Surreal.HahnSeries.workspaceEmbedding_single]
  rw [_root_.HahnSeries.coeff_single]
  congr 1
  apply propext
  change OrderDual.toDual (toSurreal b) = hahnGrowthMap e a ↔ b = -e a
  change toSurreal b = -toSurreal (e a) ↔ b = -e a
  rw [← toSurreal_neg, toSurreal_inj]

/-- The workspace embedding preserves every formal series distinctly. -/
theorem hahnEmbedding_injective (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    Function.Injective (hahnEmbedding e he) := by
  intro x y h
  apply _root_.HahnSeries.ext
  funext a
  simpa only [coeff_hahnEmbedding] using congrArg (fun F => coeff F (-e a)) h

end

end Surreal.Foundations.SmallNormalForm
