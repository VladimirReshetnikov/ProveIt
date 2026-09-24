import Surreal.HahnSeries.MvEvaluation
import Surreal.HahnSeries.StandardPart

/-!
# Hahn workspace embeddings and strong sums

An injective order-preserving additive embedding of exponent groups gives an
actual Hahn algebra embedding. The transported supports stay partially well
ordered, and every coefficient fiber of a transported summable family is
finite. Consequently the embedding commutes with strong Hahn sums and with
admissible formal-series evaluation, supplying workspace compatibility for
`found:thm:workspace`.

These are Hahn-to-Hahn maps. No embedding into the actual surreal or
surcomplex carrier is assumed or constructed here.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ Δ R α : Type*}
  [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [AddCommMonoid Δ] [LinearOrder Δ] [IsOrderedCancelAddMonoid Δ] [CommRing R]

/-- Embed a Hahn workspace along a strictly increasing additive exponent map. -/
def workspaceEmbedding (e : Γ →+ Δ) (he : StrictMono e) : R⟦Γ⟧ →ₐ[R] R⟦Δ⟧ :=
  embDomainAlgHom e he.injective (fun _ _ => he.le_iff_le)

@[simp] theorem workspaceEmbedding_coeff (e : Γ →+ Δ) (he : StrictMono e)
    (x : R⟦Γ⟧) (g : Γ) : (workspaceEmbedding e he x).coeff (e g) = x.coeff g :=
  embDomain_coeff

theorem workspaceEmbedding_coeff_of_not_mem_range (e : Γ →+ Δ) (he : StrictMono e)
    (x : R⟦Γ⟧) {g : Δ} (hg : g ∉ Set.range e) :
    (workspaceEmbedding e he x).coeff g = 0 := embDomain_notin_range hg

@[simp] theorem workspaceEmbedding_single (e : Γ →+ Δ) (he : StrictMono e)
    (g : Γ) (r : R) : workspaceEmbedding e he (single g r) = single (e g) r :=
  embDomain_single

/-- The embedding preserves precisely the support, reindexed by the exponent map. -/
theorem support_workspaceEmbedding (e : Γ →+ Δ) (he : StrictMono e) (x : R⟦Γ⟧) :
    (workspaceEmbedding e he x).support = e '' x.support := by
  apply Set.Subset.antisymm support_embDomain_subset
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_support, embDomain_coeff]
  exact hg

theorem workspaceEmbedding_injective (e : Γ →+ Δ) (he : StrictMono e) :
    Function.Injective (workspaceEmbedding e he : R⟦Γ⟧ → R⟦Δ⟧) := embDomain_injective

/-- The additive valuation is mapped by the same exponent embedding, including infinity. -/
theorem orderTop_workspaceEmbedding (e : Γ →+ Δ) (he : StrictMono e) (x : R⟦Γ⟧) :
    (workspaceEmbedding e he x).orderTop = WithTop.map e x.orderTop := orderTop_embDomain

theorem orderTop_workspaceEmbedding_nonneg_iff (e : Γ →+ Δ) (he : StrictMono e)
    (x : R⟦Γ⟧) : 0 ≤ (workspaceEmbedding e he x).orderTop ↔ 0 ≤ x.orderTop := by
  by_cases hx : x = 0
  · simp [hx]
  rw [orderTop_workspaceEmbedding, ← order_eq_orderTop_of_ne_zero hx, WithTop.map_coe]
  change ((0 : Δ) : WithTop Δ) ≤ ↑(e x.order) ↔ ((0 : Γ) : WithTop Γ) ≤ ↑x.order
  rw [WithTop.coe_le_coe, WithTop.coe_le_coe, ← e.map_zero]
  exact he.le_iff_le

theorem orderTop_workspaceEmbedding_pos_iff (e : Γ →+ Δ) (he : StrictMono e)
    (x : R⟦Γ⟧) : 0 < (workspaceEmbedding e he x).orderTop ↔ 0 < x.orderTop := by
  by_cases hx : x = 0
  · simp [hx]
  rw [orderTop_workspaceEmbedding, ← order_eq_orderTop_of_ne_zero hx, WithTop.map_coe]
  change ((0 : Δ) : WithTop Δ) < ↑(e x.order) ↔ ((0 : Γ) : WithTop Γ) < ↑x.order
  rw [WithTop.coe_lt_coe, WithTop.coe_lt_coe, ← e.map_zero]
  exact he.lt_iff_lt

@[simp] theorem coeff_zero_workspaceEmbedding (e : Γ →+ Δ) (he : StrictMono e)
    (x : R⟦Γ⟧) : (workspaceEmbedding e he x).coeff 0 = x.coeff 0 := by
  rw [← e.map_zero]
  exact workspaceEmbedding_coeff e he x 0

/-- Transport a strongly summable family to the larger exponent workspace.
Support well-ordering and finite coefficient fibers are both proved here. -/
def mapExponentsFamily (e : Γ →+ Δ) (he : StrictMono e) (s : SummableFamily Γ R α) :
    SummableFamily Δ R α where
  toFun a := workspaceEmbedding e he (s a)
  isPWO_iUnion_support' := by
    apply (s.isPWO_iUnion_support.image_of_monotone he.monotone).mono
    intro g hg
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hg
    rw [support_workspaceEmbedding] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact Set.mem_image_of_mem e (Set.mem_iUnion.mpr ⟨a, hb⟩)
  finite_co_support' := by
    intro g
    by_cases hg : g ∈ Set.range e
    · obtain ⟨b, rfl⟩ := hg
      simp only [workspaceEmbedding_coeff]
      exact s.finite_co_support' b
    · have hzero : {a | (workspaceEmbedding e he (s a)).coeff g ≠ 0} = ∅ := by
        ext a
        simp only [Set.mem_setOf_eq, workspaceEmbedding_coeff_of_not_mem_range e he _ hg,
          ne_eq, not_true_eq_false, Set.mem_empty_iff_false]
      rw [hzero]
      exact Set.finite_empty

@[simp] theorem mapExponentsFamily_apply (e : Γ →+ Δ) (he : StrictMono e)
    (s : SummableFamily Γ R α) (a : α) :
    mapExponentsFamily e he s a = workspaceEmbedding e he (s a) := rfl

/-- Exponent embeddings commute with the actual strongly summable Hahn sum. -/
theorem hsum_mapExponentsFamily (e : Γ →+ Δ) (he : StrictMono e)
    (s : SummableFamily Γ R α) :
    (mapExponentsFamily e he s).hsum = workspaceEmbedding e he s.hsum := by
  ext g
  by_cases hg : g ∈ Set.range e
  · obtain ⟨b, rfl⟩ := hg
    rw [SummableFamily.coeff_hsum, workspaceEmbedding_coeff, SummableFamily.coeff_hsum]
    apply finsum_congr
    intro a
    exact workspaceEmbedding_coeff e he (s a) b
  · rw [SummableFamily.coeff_hsum, workspaceEmbedding_coeff_of_not_mem_range e he _ hg]
    apply finsum_eq_zero_of_forall_eq_zero
    intro a
    exact workspaceEmbedding_coeff_of_not_mem_range e he (s a) hg

/-- Admissible univariate formal evaluation is independent of enlargement of
its exponent workspace. -/
theorem workspaceEmbedding_evaluate (e : Γ →+ Δ) (he : StrictMono e)
    (x : R⟦Γ⟧) (hx : 0 < x.orderTop) (F : PowerSeries R) :
    workspaceEmbedding e he (evaluate x hx F) =
      evaluate (workspaceEmbedding e he x)
        ((orderTop_workspaceEmbedding_pos_iff e he x).mpr hx) F := by
  have hfamily : mapExponentsFamily e he (SummableFamily.powerSeriesFamily x F) =
      SummableFamily.powerSeriesFamily (workspaceEmbedding e he x) F := by
    ext1 n
    rw [mapExponentsFamily_apply, SummableFamily.powerSeriesFamily_of_orderTop_pos hx,
      SummableFamily.powerSeriesFamily_of_orderTop_pos
        ((orderTop_workspaceEmbedding_pos_iff e he x).mpr hx), map_smul, map_pow]
  change workspaceEmbedding e he (SummableFamily.powerSeriesFamily x F).hsum =
    (SummableFamily.powerSeriesFamily (workspaceEmbedding e he x) F).hsum
  rw [← hsum_mapExponentsFamily, hfamily]

/-- Finite-variable strong evaluation is also independent of enlargement of
the exponent workspace. -/
theorem workspaceEmbedding_mvEvaluate {σ : Type*} [Fintype σ]
    (e : Γ →+ Δ) (he : StrictMono e) (x : σ → R⟦Γ⟧)
    (hx : ∀ i, 0 < (x i).orderTop) (F : MvPowerSeries σ R) :
    workspaceEmbedding e he (mvEvaluate x hx F) =
      mvEvaluate (fun i => workspaceEmbedding e he (x i))
        (fun i => (orderTop_workspaceEmbedding_pos_iff e he (x i)).mpr (hx i)) F := by
  have hfamily : mapExponentsFamily e he (mvEvaluationFamily x hx F) =
      mvEvaluationFamily (fun i => workspaceEmbedding e he (x i))
        (fun i => (orderTop_workspaceEmbedding_pos_iff e he (x i)).mpr (hx i)) F := by
    ext1 d
    simp only [mapExponentsFamily_apply, mvEvaluationFamily_apply, map_smul, map_prod, map_pow]
  rw [mvEvaluate_apply, ← hsum_mapExponentsFamily, hfamily, mvEvaluate_apply]

end


noncomputable section

variable {Γ Δ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ] [Field K]

/-- The native additive Hahn valuations are compatible with workspace embedding. -/
theorem addVal_workspaceEmbedding (e : Γ →+ Δ) (he : StrictMono e) (x : K⟦Γ⟧) :
    addVal Δ K (workspaceEmbedding e he x) = WithTop.map e (addVal Γ K x) :=
  orderTop_workspaceEmbedding e he x

/-- The workspace embedding restricts to the nonnegative-order subrings. -/
def workspaceEmbeddingNonnegative (e : Γ →+ Δ) (he : StrictMono e) :
    nonnegativeSubring Γ K →+* nonnegativeSubring Δ K :=
  ((workspaceEmbedding e he).toRingHom.comp (nonnegativeSubring Γ K).subtype).codRestrict _
    (fun x => (orderTop_workspaceEmbedding_nonneg_iff e he x.val).mpr x.property)

@[simp] theorem coe_workspaceEmbeddingNonnegative (e : Γ →+ Δ) (he : StrictMono e)
    (x : nonnegativeSubring Γ K) :
    (workspaceEmbeddingNonnegative e he x : K⟦Δ⟧) = workspaceEmbedding e he (x : K⟦Γ⟧) := rfl

/-- Standard part is unchanged by enlargement of the exponent workspace. -/
@[simp] theorem standardPart_workspaceEmbedding (e : Γ →+ Δ) (he : StrictMono e)
    (x : nonnegativeSubring Γ K) :
    standardPart Δ K (workspaceEmbeddingNonnegative e he x) = standardPart Γ K x :=
  coeff_zero_workspaceEmbedding e he x.val

/-- Compatibility of the residue-field maps as an equality of ring homomorphisms. -/
theorem standardPart_comp_workspaceEmbedding (e : Γ →+ Δ) (he : StrictMono e) :
    (standardPart Δ K).comp (workspaceEmbeddingNonnegative e he) = standardPart Γ K := by
  ext x
  exact standardPart_workspaceEmbedding e he x

end

end Surreal.HahnSeries
