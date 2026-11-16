import PA194SourceAddCoherence
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Coherence of multiplication in the source theory

`sM2`: if `w` is a product of `u₁, u₂` and `w'` a product of `v₁, v₂`, with `u₁ ≅ v₁` and
`u₂ ≅ v₂`, then `w ≅ w'`.

In a structure, by induction on `u₁` (`letter_induction` for `psiM2`): a product with an
empty first factor is that factor (`mul_zero_left`); for a successor, the predecessor law of
multiplication gives `d, d'` with `x · u₂ = d`, `v₀ · v₂ = d'`, `d + u₂ = w`, `d' + v₂ = w'`,
the induction hypothesis gives `d ≅ d'`, and coherence of addition gives `w ≅ w'`.

`m2_supply`: `T ⊢ tHyp sM2` for the adjunctive source theory with full separation, from
`TenFacts` and `T ⊢ tHyp sA2`.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194Schematic

/-- The body of `sM2` with its first variable free. -/
def psiM2 : SF 1 :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ (sDom #5 🡒 sDom #4 🡒 sDom #3 🡒 sDom #2 🡒 sDom #1 🡒 sDom #0 🡒
    sMul #5 #4 #3 🡒 sMul #2 #1 #0 🡒 sIso #5 #2 🡒 sIso #4 #1 🡒 sIso #3 #0)

theorem ev_psiM2 {M : Type} [s : Structure NL M] (x : M) : ev ![x] psiM2 ↔
    ∀ u₂ w v₁ v₂ w' : M, mD x → mD u₂ → mD w → mD v₁ → mD v₂ → mD w' →
      mMu x u₂ w → mMu v₁ v₂ w' → mI x v₁ → mI u₂ v₂ → mI w w' := by
  simp [psiM2]

end PA194GuardedCompiler

namespace PA194SourceModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194Schematic PA194GuardedCompiler
open M6.PA.RelationalSource

attribute [local instance] PA194ModelLogic.sourceLanguageAdjTheory

section model
variable {N : Type} [s : Structure SourceL N] [Structure.Eq SourceL N]

/-- A product with an empty first factor is that factor. -/
theorem mul_zero_left {u c w : N} (hu : SZero u) (h : SMul u c w) : w = u := by
  obtain ⟨e, g, _, ⟨hgd, hf, _, hbase, _⟩, hedge⟩ := h
  have he : e = u := by
    rcases (hgd e).mp ⟨e, hbase⟩ with h | h
    · exact absurd h (hu e)
    · exact h
  rw [he] at hbase
  exact hf u w u ⟨hedge, hbase⟩

/-- Coherence of the products with first factor `x`. -/
def PM2 (x : N) : Prop :=
  ∀ u₂ w v₁ v₂ w' : N, SDom x → SDom u₂ → SDom w → SDom v₁ → SDom v₂ → SDom w' →
    SMul x u₂ w → SMul v₁ v₂ w' → SIso x v₁ → SIso u₂ v₂ → SIso w w'

theorem ev_psiM2_iff (f : ℕ → N) (x : N) :
    @ev N (sourceLetters s f) 1 ![x] psiM2 ↔ PM2 x := by
  rw [@ev_psiM2 N (sourceLetters s f) x]
  simp only [mD_iff, mMu_iff, mI_iff, PM2]

variable (hsep : ∀ (p : Semiproposition SourceL 1) (f : ℕ → N),
  FirstOrder.Semiformula.Evalf (s := s) f (separationFormula p))
include hsep

theorem sem_m2 (f : ℕ → N) (A2 : ∀ x : N, SDom x → PA2 x) : ∀ x : N, SDom x → PM2 x := by
  have key := letter_induction hsep f psiM2
    (by
      intro z _ zz
      refine (ev_psiM2_iff f z).mpr ?_
      intro u₂ w v₁ v₂ w' _ _ _ _ _ _ m1 m2 i1 _
      have e1 : w = z := mul_zero_left zz m1
      have e2 : w' = v₁ := mul_zero_left (iso_right_empty i1 zz) m2
      rw [e1, e2]
      exact i1)
    (by
      intro x y dx dy sxy ih
      have ih' := (ev_psiM2_iff f x).mp ih
      refine (ev_psiM2_iff f y).mpr ?_
      intro u₂ w v₁ v₂ w' _ du dw dv1 dv2 dw' m1 m2 i1 i2
      obtain ⟨d, dd, md, ad⟩ := mul_predecessor hsep dx sxy m1
      rcases dom_zero_or_succ dv1 with zv | ⟨v0, dv0, sv⟩
      · exact absurd ((sxy x).mpr (Or.inr rfl)) (iso_left_empty i1 zv x)
      · have i0 : SIso x v0 := iso_cancel hsep dy dv1 sxy sv i1
        obtain ⟨d', dd', md', ad'⟩ := mul_predecessor hsep dv0 sv m2
        have id : SIso d d' := ih' u₂ d v0 v₂ d' dx du dd dv0 dv2 dd' md md' i0 i2
        exact A2 d dd u₂ w d' v₂ w' dd du dw dd' dv2 dw' ad ad' id i2)
  intro x hx
  exact (ev_psiM2_iff f x).mp (key x hx)

/-- Coherence of multiplication in a structure, under the ten known facts and coherence of
addition. -/
theorem valid_m2 (f : ℕ → N) :
    @ev N (sourceLetters s f) 0 (![] : Fin 0 → N) (sWith10 (sA2 🡒 sM2)) := by
  refine (@ev_sWith10 N (sourceLetters s f) (sA2 🡒 sM2)).mpr fun _ => ?_
  refine (@ev_imp N (sourceLetters s f) 0 ![] sA2 sM2).mpr fun hA => ?_
  have hA' := (@ev_sA2 N (sourceLetters s f)).mp hA
  have A2 : ∀ x : N, SDom x → PA2 x := by
    intro x _ u₂ w v₁ v₂ w' d1 d2 d3 d4 d5 d6 h1 h2 h3 h4
    exact (mI_iff f w w').mp
      (hA' x u₂ w v₁ v₂ w' ((mD_iff f x).mpr d1) ((mD_iff f u₂).mpr d2) ((mD_iff f w).mpr d3)
        ((mD_iff f v₁).mpr d4) ((mD_iff f v₂).mpr d5) ((mD_iff f w').mpr d6)
        ((mA_iff f x u₂ w).mpr h1) ((mA_iff f v₁ v₂ w').mpr h2) ((mI_iff f x v₁).mpr h3)
        ((mI_iff f u₂ v₂).mpr h4))
  refine (@ev_sM2 N (sourceLetters s f)).mpr ?_
  intro u₁ u₂ w v₁ v₂ w' d1 d2 d3 d4 d5 d6 h1 h2 h3 h4
  exact (mI_iff f w w').mpr
    (sem_m2 hsep f A2 u₁ ((mD_iff f u₁).mp d1) u₂ w v₁ v₂ w' ((mD_iff f u₁).mp d1)
      ((mD_iff f u₂).mp d2) ((mD_iff f w).mp d3) ((mD_iff f v₁).mp d4) ((mD_iff f v₂).mp d5)
      ((mD_iff f w').mp d6) ((mMu_iff f u₁ u₂ w).mp h1) ((mMu_iff f v₁ v₂ w').mp h2)
      ((mI_iff f u₁ v₁).mp h3) ((mI_iff f u₂ v₂).mp h4))

#print axioms mul_zero_left
#print axioms sem_m2
end model

section supply
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] adjunctiveFullSepTheoryDelta

/-- Coherence of multiplication is internally provable in the source theory. -/
theorem m2_supply (K : TenFacts (V := V) adjunctiveFullSepTheory)
    (a2 : adjunctiveFullSepTheory.internalize V ⊢
      (tHyp sA2 : Bootstrapping.Semiformula V SourceL 0)) :
    adjunctiveFullSepTheory.internalize V ⊢ (tHyp sM2 : Bootstrapping.Semiformula V SourceL 0) := by
  have h : adjunctiveFullSepTheory.internalize V ⊢
      (tHyp (sA2 🡒 sM2) : Bootstrapping.Semiformula V SourceL 0) := by
    apply with_ten K
    apply source_supply
    intro N _ s _ _ hsep f
    exact valid_m2 hsep f
  have h' : adjunctiveFullSepTheory.internalize V ⊢
      instS (sig (fun _ => (⊤ : Bootstrapping.Semiformula V SourceL 1))) (sA2 🡒 sM2) := h
  rw [instS_imp] at h'
  exact tmp h' a2

#print axioms m2_supply
end supply
end PA194SourceModel
