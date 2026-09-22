import Surreal.Foundations.SmallNormalFormHahnEmbedding
import Surreal.Foundations.SignSequenceWorkspaceExponents
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Localizing small formal families in one divisible Hahn workspace

Pullback along an increasing additive exponent map restricts coefficients
to its negative growth image. If that image contains the formal support,
the Hahn embedding recovers the original form. The rational span of a
small family's supports therefore gives one small divisible workspace for
the whole family, in particular for every polynomial's coefficients.
No closedness assumption on the formal or actual surreal field is used.
-/

universe u v w

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ]

/-- Restrict formal coefficients to the negative image of a workspace exponent map. -/
def hahnPreimage (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : SmallNormalForm.{u}) : _root_.HahnSeries Γ ℝ := by
  let f : Γ → ℝ := fun a => coeff F (-e a)
  let r : (· < · : Function.support f → Function.support f → Prop) ↪r
      (· > · : support F → support F → Prop) :=
    { toFun a := ⟨-e a.val, a.property⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact he.injective (neg_injective (congrArg Subtype.val hab))
      map_rel_iff' := by
        intro a b
        change -e b.val < -e a.val ↔ a.val < b.val
        rw [neg_lt_neg_iff]
        exact he.lt_iff_lt }
  exact ⟨f, Set.IsWF.isPWO (r.wellFounded (wellFoundedOn_support F))⟩

@[simp] theorem coeff_hahnPreimage (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : SmallNormalForm.{u}) (a : Γ) : (hahnPreimage e he F).coeff a = coeff F (-e a) := rfl

variable [IsOrderedAddMonoid Γ] [Small.{u} Γ]

/-- Pullback is an actual preimage whenever the exponent image contains the support. -/
theorem hahnEmbedding_hahnPreimage (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : SmallNormalForm.{u}) (hF : support F ⊆ Set.range (fun a => -e a)) :
    hahnEmbedding e he (hahnPreimage e he F) = F := by
  apply ext
  intro b
  by_cases hb : b ∈ Set.range (fun a => -e a)
  · obtain ⟨a, rfl⟩ := hb
    rw [coeff_hahnEmbedding, coeff_hahnPreimage]
  · rw [coeff_hahnEmbedding_of_not_mem_range e he _ hb]
    exact (not_ne_iff.mp (fun hbF => hb (hF hbF))).symm

omit [IsOrderedAddMonoid Γ] [Small.{u} Γ] in
/-- The pullback retains exactly the coefficients whose exponents lie in the workspace. -/
theorem support_hahnPreimage (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : SmallNormalForm.{u}) :
    (hahnPreimage e he F).support = (fun a => -e a) ⁻¹' support F := rfl

section Family

variable {ι : Type w} [Small.{u} ι]

/-- The common embedding from the rational span of all growth supports in a small family. -/
def familyWorkspaceEmbedding (F : ι → SmallNormalForm.{u}) :
    _root_.HahnSeries (workspaceExponents (⋃ i, support (F i))) ℝ →+* SmallNormalForm.{u} :=
  hahnEmbedding (workspaceExponents (⋃ i, support (F i))).subtype.toAddMonoidHom
    (fun _ _ h => h)

theorem familyWorkspaceEmbedding_injective (F : ι → SmallNormalForm.{u}) :
    Function.Injective (familyWorkspaceEmbedding F) := hahnEmbedding_injective _ _

/-- Each member's canonical coefficient pullback to the common workspace. -/
def familyHahnPreimage (F : ι → SmallNormalForm.{u}) (i : ι) :
    _root_.HahnSeries (workspaceExponents (⋃ j, support (F j))) ℝ :=
  hahnPreimage (workspaceExponents (⋃ j, support (F j))).subtype.toAddMonoidHom
    (fun _ _ h => h) (F i)

/-- The common workspace simultaneously contains the entire small input family. -/
@[simp] theorem familyWorkspaceEmbedding_preimage (F : ι → SmallNormalForm.{u}) (i : ι) :
    familyWorkspaceEmbedding F (familyHahnPreimage F i) = F i := by
  apply hahnEmbedding_hahnPreimage
  intro a ha
  have ham : a ∈ workspaceExponents (⋃ j, support (F j)) :=
    subset_workspaceExponents _ (Set.mem_iUnion.mpr ⟨i, ha⟩)
  refine ⟨⟨-a, (workspaceExponents _).neg_mem ham⟩, ?_⟩
  exact _root_.neg_neg a

theorem mem_range_familyWorkspaceEmbedding (F : ι → SmallNormalForm.{u}) (i : ι) :
    F i ∈ Set.range (familyWorkspaceEmbedding F) :=
  ⟨familyHahnPreimage F i, familyWorkspaceEmbedding_preimage F i⟩

end Family

/-- Every formal polynomial descends to one small divisible real Hahn workspace. -/
theorem exists_polynomial_hahn_preimage (P : Polynomial SmallNormalForm.{u}) :
    ∃ Q : Polynomial (_root_.HahnSeries (workspaceExponents (⋃ n, support (P.coeff n))) ℝ),
      Q.map (familyWorkspaceEmbedding P.coeff) = P := by
  apply (Polynomial.mem_lifts P).mp
  apply (Polynomial.lifts_iff_coeff_lifts P).mpr
  exact mem_range_familyWorkspaceEmbedding P.coeff

end

end Surreal.Foundations.SmallNormalForm
