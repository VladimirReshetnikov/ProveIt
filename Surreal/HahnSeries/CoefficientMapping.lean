import Surreal.HahnSeries.Evaluation

/-!
# Coefficient maps preserve Hahn sums and admissible evaluation

A coefficient ring homomorphism may remove support and increase Hahn order.
It still preserves both strong summability conditions and the corresponding
Hahn sums. Consequently it commutes with formal evaluation at positive order.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ R S ι : Type*} [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [CommRing R] [CommRing S]

/-- A coefficient ring homomorphism induces a Hahn ring homomorphism. -/
def mapCoefficients (f : R →+* S) : R⟦Γ⟧ →+* S⟦Γ⟧ where
  toFun x := x.map f
  map_zero' := _root_.HahnSeries.map_zero f.toZeroHom
  map_one' := _root_.HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' _ _ := _root_.HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := _root_.HahnSeries.map_mul f.toNonUnitalRingHom

@[simp] theorem coeff_mapCoefficients (f : R →+* S) (x : R⟦Γ⟧) (g : Γ) :
    (mapCoefficients f x).coeff g = f (x.coeff g) := rfl

@[simp] theorem mapCoefficients_single (f : R →+* S) (g : Γ) (r : R) :
    mapCoefficients f (single g r) = single g (f r) :=
  _root_.HahnSeries.map_single f.toZeroHom

theorem support_mapCoefficients_subset (f : R →+* S) (x : R⟦Γ⟧) :
    (mapCoefficients f x).support ⊆ x.support :=
  support_map_subset x f.toZeroHom

/-- Mapping coefficients can increase, but cannot decrease, Hahn order. -/
theorem orderTop_le_mapCoefficients (f : R →+* S) (x : R⟦Γ⟧) :
    x.orderTop ≤ (mapCoefficients f x).orderTop := by
  apply le_orderTop_iff_forall.mpr
  intro g hg
  rw [coeff_mapCoefficients, coeff_eq_zero_of_lt_orderTop hg, map_zero]

theorem orderTop_mapCoefficients_pos (f : R →+* S) (x : R⟦Γ⟧)
    (hx : 0 < x.orderTop) : 0 < (mapCoefficients f x).orderTop :=
  hx.trans_le (orderTop_le_mapCoefficients f x)

/-- Map an actual strongly summable family. Its support union and every
coefficient fiber are subsets of those of the original family. -/
def mapCoefficientsFamily (f : R →+* S) (s : SummableFamily Γ R ι) :
    SummableFamily Γ S ι where
  toFun i := mapCoefficients f (s i)
  isPWO_iUnion_support' := s.isPWO_iUnion_support.mono <|
    Set.iUnion_mono fun i => support_mapCoefficients_subset f (s i)
  finite_co_support' g := (s.finite_co_support g).subset <| by
    intro i hi hz
    exact hi (by simp [coeff_mapCoefficients, hz])

@[simp] theorem mapCoefficientsFamily_apply (f : R →+* S)
    (s : SummableFamily Γ R ι) (i : ι) :
    mapCoefficientsFamily f s i = mapCoefficients f (s i) := rfl

/-- Coefficient maps commute with every strongly summable Hahn sum. -/
theorem mapCoefficients_hsum (f : R →+* S) (s : SummableFamily Γ R ι) :
    mapCoefficients f s.hsum = (mapCoefficientsFamily f s).hsum := by
  apply _root_.HahnSeries.ext
  funext g
  simp only [coeff_mapCoefficients, SummableFamily.coeff_hsum,
    mapCoefficientsFamily_apply]
  exact f.toAddMonoidHom.map_finsum (s.finite_co_support g)

/-- The mapped evaluation family is the evaluation family of the mapped
formal coefficients at the mapped Hahn argument. -/
theorem mapCoefficientsFamily_powerSeriesFamily (f : R →+* S) (x : R⟦Γ⟧)
    (hx : 0 < x.orderTop) (F : PowerSeries R) :
    mapCoefficientsFamily f (SummableFamily.powerSeriesFamily x F) =
      SummableFamily.powerSeriesFamily (mapCoefficients f x) (F.map f) := by
  ext n
  simp only [mapCoefficientsFamily_apply,
    SummableFamily.powerSeriesFamily_of_orderTop_pos hx,
    SummableFamily.powerSeriesFamily_of_orderTop_pos (orderTop_mapCoefficients_pos f x hx),
    PowerSeries.coeff_map, ← single_zero_mul_eq_smul, map_mul, map_pow,
    mapCoefficients_single]

/-- Coefficient maps commute with actual admissible formal evaluation.
The mapped argument remains admissible even when its leading term vanishes. -/
theorem mapCoefficients_evaluate (f : R →+* S) (x : R⟦Γ⟧)
    (hx : 0 < x.orderTop) (F : PowerSeries R) :
    mapCoefficients f (evaluate x hx F) =
      evaluate (mapCoefficients f x) (orderTop_mapCoefficients_pos f x hx) (F.map f) := by
  change mapCoefficients f (SummableFamily.powerSeriesFamily x F).hsum =
    (SummableFamily.powerSeriesFamily (mapCoefficients f x) (F.map f)).hsum
  rw [mapCoefficients_hsum, mapCoefficientsFamily_powerSeriesFamily f x hx F]

end
end Surreal.HahnSeries
