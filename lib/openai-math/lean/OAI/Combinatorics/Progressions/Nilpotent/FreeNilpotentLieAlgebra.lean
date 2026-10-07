import OAI.Combinatorics.Progressions.Estimates.QuotientInducedMark

namespace OAI

section

namespace Erdos3

variable (X : Type*) (s : ℕ)

def FreeNilpotentLieAlgebra :=
  FreeLieAlgebra ℚ X ⧸ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s

namespace FreeNilpotentLieAlgebra

noncomputable instance instLieRing : LieRing (FreeNilpotentLieAlgebra X s) :=
  inferInstanceAs (LieRing (FreeLieAlgebra ℚ X ⧸
    LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s))

noncomputable instance instLieAlgebra : LieAlgebra ℚ (FreeNilpotentLieAlgebra X s) :=
  inferInstanceAs (LieAlgebra ℚ (FreeLieAlgebra ℚ X ⧸
    LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s))

noncomputable def mk : FreeLieAlgebra ℚ X →ₗ⁅ℚ⁆ FreeNilpotentLieAlgebra X s :=
  lieQuotientMap (LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s)

theorem mk_surjective : Function.Surjective (mk X s) :=
  lieQuotientMap_surjective _

theorem mk_eq_zero (x : FreeLieAlgebra ℚ X) :
    mk X s x = 0 ↔ x ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s :=
  lieQuotientMap_eq_zero _ x

theorem lowerCentralSeries_eq_bot :
    LieModule.lowerCentralSeries ℚ (FreeNilpotentLieAlgebra X s) (FreeNilpotentLieAlgebra X s) s = ⊥ := by
  rw [← LieIdeal.lowerCentralSeries_map_eq s (mk_surjective X s), LieIdeal.map_eq_bot_iff]
  intro x hx
  exact (mk_eq_zero X s x).mpr hx

noncomputable def of (x : X) : FreeNilpotentLieAlgebra X s := mk X s (FreeLieAlgebra.of ℚ x)

variable {X s} {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem lowerCentralSeries_le_lift_ker (f : X → L)
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s ≤
      (FreeLieAlgebra.lift ℚ f).ker := by
  apply LieIdeal.map_eq_bot_iff.mp
  apply bot_unique
  rw [← hnil]
  exact LieIdeal.map_lowerCentralSeries_le s

noncomputable def lift (f : X → L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    FreeNilpotentLieAlgebra X s →ₗ⁅ℚ⁆ L :=
  lieQuotientDescend _ (FreeLieAlgebra.lift ℚ f) (lowerCentralSeries_le_lift_ker f hnil)

theorem lift_mk (f : X → L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (x : FreeLieAlgebra ℚ X) : lift f hnil (mk X s x) = FreeLieAlgebra.lift ℚ f x := rfl

@[simp] theorem lift_of (f : X → L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (x : X) :
    lift f hnil (of X s x) = f x := FreeLieAlgebra.lift_of_apply _ _

theorem hom_ext {f g : FreeNilpotentLieAlgebra X s →ₗ⁅ℚ⁆ L}
    (h : ∀ x, f (of X s x) = g (of X s x)) : f = g := by
  have heq : f.comp (mk X s) = g.comp (mk X s) := FreeLieAlgebra.hom_ext h
  apply LieHom.ext
  intro x
  obtain ⟨y, rfl⟩ := mk_surjective X s x
  exact LieHom.congr_fun heq y

theorem mk_truncation (x : FreeLieAlgebra ℚ X) :
    mk X s (freeLieTruncation s x) = mk X s x := by
  have h := lift_freeLieTruncation ((mk X s) ∘ FreeLieAlgebra.of ℚ)
    (lowerCentralSeries_eq_bot X s) x
  simpa only [FreeLieAlgebra.lift_comp_of] using h

end FreeNilpotentLieAlgebra

end Erdos3

end

end OAI
