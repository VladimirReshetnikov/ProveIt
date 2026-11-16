import PA194SourceKnown
import PA194SourcePredecessor
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Coherence of addition in the source theory

`sA2`: if `w` is a sum of `u₁, u₂` and `w'` a sum of `v₁, v₂`, with `u₁ ≅ v₁` and `u₂ ≅ v₂`,
then `w ≅ w'` (all six ordinal representatives).

In a structure the proof is by induction on `u₁` (`letter_induction` for `psiA2`):

* `add_zero_left`: a sum of an empty representative and `b` is `b` itself;
* for `u₁` empty, `v₁` is empty too (`iso_right_empty`), so `w = u₂` and `w' = v₂`;
* for `u₁` a successor of `x`, `v₁` is a successor of some `v₀` with `x ≅ v₀`
  (`dom_zero_or_succ`, `iso_cancel`), the predecessor law gives `d, d'` with
  `x + u₂ = d`, `v₀ + v₂ = d'` and `w, w'` their successors, the induction hypothesis gives
  `d ≅ d'`, and successors of isomorphic representatives are isomorphic (one of the ten
  known facts).

`a2_supply`: `T ⊢ tHyp sA2` for the adjunctive source theory with full separation, in every
model of `IΣ₁`, from `TenFacts`.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194Schematic

/-- The body of `sA2` with its first variable free: coherence of the sums with first
summand `#0`. -/
def psiA2 : SF 1 :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ (sDom #5 🡒 sDom #4 🡒 sDom #3 🡒 sDom #2 🡒 sDom #1 🡒 sDom #0 🡒
    sAdd #5 #4 #3 🡒 sAdd #2 #1 #0 🡒 sIso #5 #2 🡒 sIso #4 #1 🡒 sIso #3 #0)

theorem ev_psiA2 {M : Type} [s : Structure NL M] (x : M) : ev ![x] psiA2 ↔
    ∀ u₂ w v₁ v₂ w' : M, mD x → mD u₂ → mD w → mD v₁ → mD v₂ → mD w' →
      mA x u₂ w → mA v₁ v₂ w' → mI x v₁ → mI u₂ v₂ → mI w w' := by
  simp [psiA2]

end PA194GuardedCompiler

namespace PA194SourceModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194Schematic PA194GuardedCompiler
open M6.PA.RelationalSource

attribute [local instance] PA194ModelLogic.sourceLanguageAdjTheory

section model
variable {N : Type} [s : Structure SourceL N] [Structure.Eq SourceL N]

/-- A sum of an empty representative and `b` is `b`. -/
theorem add_zero_left {u c w : N} (hu : SZero u) (h : SAdd u c w) : w = c := by
  obtain ⟨e, g, _, ⟨hgd, hf, _, hbase, _⟩, hedge⟩ := h
  have he : e = u := by
    rcases (hgd e).mp ⟨c, hbase⟩ with h | h
    · exact absurd h (hu e)
    · exact h
  rw [he] at hbase
  exact hf u w c ⟨hedge, hbase⟩

/-- Coherence of the sums with first summand `x`. -/
def PA2 (x : N) : Prop :=
  ∀ u₂ w v₁ v₂ w' : N, SDom x → SDom u₂ → SDom w → SDom v₁ → SDom v₂ → SDom w' →
    SAdd x u₂ w → SAdd v₁ v₂ w' → SIso x v₁ → SIso u₂ v₂ → SIso w w'

theorem ev_psiA2_iff (f : ℕ → N) (x : N) :
    @ev N (sourceLetters s f) 1 ![x] psiA2 ↔ PA2 x := by
  rw [@ev_psiA2 N (sourceLetters s f) x]
  simp only [mD_iff, mA_iff, mI_iff, PA2]

variable (hsep : ∀ (p : Semiproposition SourceL 1) (f : ℕ → N),
  FirstOrder.Semiformula.Evalf (s := s) f (separationFormula p))
include hsep

theorem sem_a2 (f : ℕ → N) (K : Known N) : ∀ x : N, SDom x → PA2 x := by
  have key := letter_induction hsep f psiA2
    (by
      intro z _ zz
      refine (ev_psiA2_iff f z).mpr ?_
      intro u₂ w v₁ v₂ w' _ _ _ _ _ _ a1 a2 i1 i2
      have e1 : w = u₂ := add_zero_left zz a1
      have e2 : w' = v₂ := add_zero_left (iso_right_empty i1 zz) a2
      rw [e1, e2]
      exact i2)
    (by
      intro x y dx dy sxy ih
      have ih' := (ev_psiA2_iff f x).mp ih
      refine (ev_psiA2_iff f y).mpr ?_
      intro u₂ w v₁ v₂ w' _ du dw dv1 dv2 dw' a1 a2 i1 i2
      obtain ⟨d, dd, ad, sd⟩ := add_predecessor hsep dx sxy a1
      rcases dom_zero_or_succ dv1 with zv | ⟨v0, dv0, sv⟩
      · exact absurd ((sxy x).mpr (Or.inr rfl)) (iso_left_empty i1 zv x)
      · have i0 : SIso x v0 := iso_cancel hsep dy dv1 sxy sv i1
        obtain ⟨d', dd', ad', sd'⟩ := add_predecessor hsep dv0 sv a2
        have id : SIso d d' := ih' u₂ d v0 v₂ d' dx du dd dv0 dv2 dd' ad ad' i0 i2
        exact K.s2 d w d' w' dd dw dd' dw' sd sd' id)
  intro x hx
  exact (ev_psiA2_iff f x).mp (key x hx)

/-- Coherence of addition in a structure, under the ten known facts. -/
theorem valid_a2 (f : ℕ → N) :
    @ev N (sourceLetters s f) 0 (![] : Fin 0 → N) (sWith10 sA2) := by
  refine (@ev_sWith10 N (sourceLetters s f) sA2).mpr fun H => ?_
  refine (@ev_sA2 N (sourceLetters s f)).mpr ?_
  intro u₁ u₂ w v₁ v₂ w' d1 d2 d3 d4 d5 d6 h1 h2 h3 h4
  have K := known_of f H
  exact (mI_iff f w w').mpr
    (sem_a2 hsep f K u₁ ((mD_iff f u₁).mp d1) u₂ w v₁ v₂ w' ((mD_iff f u₁).mp d1)
      ((mD_iff f u₂).mp d2) ((mD_iff f w).mp d3) ((mD_iff f v₁).mp d4) ((mD_iff f v₂).mp d5)
      ((mD_iff f w').mp d6) ((mA_iff f u₁ u₂ w).mp h1) ((mA_iff f v₁ v₂ w').mp h2)
      ((mI_iff f u₁ v₁).mp h3) ((mI_iff f u₂ v₂).mp h4))

#print axioms add_zero_left
#print axioms sem_a2
end model

section supply
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] adjunctiveFullSepTheoryDelta

/-- Coherence of addition is internally provable in the source theory. -/
theorem a2_supply (K : TenFacts (V := V) adjunctiveFullSepTheory) :
    adjunctiveFullSepTheory.internalize V ⊢ (tHyp sA2 : Bootstrapping.Semiformula V SourceL 0) := by
  apply with_ten K
  apply source_supply
  intro N _ s _ _ hsep f
  exact valid_a2 hsep f

#print axioms a2_supply
end supply
end PA194SourceModel
