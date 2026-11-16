import PA194ArithFacts
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The two successor facts from predecessor laws

`PA194ArithFacts` uses two facts about the source theory beyond the twelve of `SourceFacts`:
`sA3` (the sum with a successor on the left) and `sM3` (the product with a successor on the
left). Here they are reduced to three statements that follow the definition of the addition
and multiplication traces more closely:

* `sAP`: if `u` is a successor of `t` and `o` a sum of `u` and `b`, then some member `d` of
  the domain is a sum of `t` and `b` and has `o` as a successor. This is the shape of
  `addPredecessorResult` of the relational source development, with domain guards for all
  four variables.
* `sMP`: if `u` is a successor of `t` and `o` a product of `u` and `b`, then some member `d`
  of the domain is a product of `t` and `b`, and `o` is a sum of `d` and `b`
  (`mulPredecessorResult`).
* `sAC`: sums of `a, b` and of `b, a` are isomorphic.

`a3_of_predecessor`: `SourceFacts T` and `sAP` give `sA3`.
`m3_of_predecessor`: `SourceFacts T`, `sMP` and `sAC` give `sM3`.

Both are instances of sentences that hold in every structure under the twelve hypotheses.
The three statements themselves are not proved here.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher PA194Schematic

/-! ### The sentences -/

/-- The predecessor law of addition. The variables are `t, u, b, o = #3, #2, #1, #0`. -/
def sAP : SF 0 :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ (sDom #3 🡒 sDom #2 🡒 sDom #1 🡒 sDom #0 🡒 sSucc #3 #2 🡒 sAdd #2 #1 #0 🡒
    (∃⁰ (sDom #0 ⋏ (sAdd #4 #2 #0 ⋏ sSucc #0 #1))))
/-- The predecessor law of multiplication. The variables are `t, u, b, o = #3, #2, #1, #0`. -/
def sMP : SF 0 :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ (sDom #3 🡒 sDom #2 🡒 sDom #1 🡒 sDom #0 🡒 sSucc #3 #2 🡒 sMul #2 #1 #0 🡒
    (∃⁰ (sDom #0 ⋏ (sMul #4 #2 #0 ⋏ sAdd #0 #2 #1))))
/-- Sums in the two orders are isomorphic. The variables are `a, b, c, c' = #3, #2, #1, #0`. -/
def sAC : SF 0 :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ (sDom #3 🡒 sDom #2 🡒 sDom #1 🡒 sDom #0 🡒 sAdd #3 #2 #1 🡒 sAdd #2 #3 #0 🡒
    sIso #1 #0)
def fA3 : SF 0 := sAP 🡒 sA3
def fM3 : SF 0 := sMP 🡒 sAC 🡒 sM3

section semantics
variable {M : Type} [s : Structure NL M]

theorem ev_sAP : ev (![] : Fin 0 → M) sAP ↔
    ∀ t u b o : M, mD t → mD u → mD b → mD o → mS t u → mA u b o →
      ∃ d : M, mD d ∧ (mA t b d ∧ mS d o) := by
  simp [sAP]
theorem ev_sMP : ev (![] : Fin 0 → M) sMP ↔
    ∀ t u b o : M, mD t → mD u → mD b → mD o → mS t u → mMu u b o →
      ∃ d : M, mD d ∧ (mMu t b d ∧ mA d b o) := by
  simp [sMP]
theorem ev_sAC : ev (![] : Fin 0 → M) sAC ↔
    ∀ a b c c' : M, mD a → mD b → mD c → mD c' → mA a b c → mA b a c' → mI c c' := by
  simp [sAC]

theorem m_isoRefl (H : MTheta M) {a : M} (da : mD a) : mI a a :=
  H.ei a a a da da (H.e1 a) (H.e1 a)

theorem m_a3 (H : MTheta M)
    (HP : ∀ t u b o : M, mD t → mD u → mD b → mD o → mS t u → mA u b o →
      ∃ d : M, mD d ∧ (mA t b d ∧ mS d o)) :
    ∀ u u' v w w0 w1 : M, mD u → mD u' → mD v → mD w → mD w0 → mD w1 →
      mS u u' → mA u' v w → mA u v w0 → mS w0 w1 → mI w w1 := by
  intro u u' v w w0 w1 du du' dv dw dw0 dw1 su aw aw0 sw
  obtain ⟨d, dd, ad, sd⟩ := HP u u' v w du du' dv dw su aw
  have i1 : mI d w0 := H.a2 u v d u v w0 du dv dd du dv dw0 ad aw0 (m_isoRefl H du) (m_isoRefl H dv)
  exact H.s2 d w w0 w1 dd dw dw0 dw1 sd sw i1

theorem m_m3 (H : MTheta M)
    (HP : ∀ t u b o : M, mD t → mD u → mD b → mD o → mS t u → mMu u b o →
      ∃ d : M, mD d ∧ (mMu t b d ∧ mA d b o))
    (HC : ∀ a b c c' : M, mD a → mD b → mD c → mD c' → mA a b c → mA b a c' → mI c c') :
    ∀ u u' v w w0 w1 : M, mD u → mD u' → mD v → mD w → mD w0 → mD w1 →
      mS u u' → mMu u' v w → mMu u v w0 → mA v w0 w1 → mI w w1 := by
  intro u u' v w w0 w1 du du' dv dw dw0 dw1 su mw mw0 aw
  obtain ⟨d, dd, md, ad⟩ := HP u u' v w du du' dv dw su mw
  have i1 : mI d w0 := H.m2 u v d u v w0 du dv dd du dv dw0 md mw0 (m_isoRefl H du) (m_isoRefl H dv)
  obtain ⟨w2, dw2, aw2⟩ := H.a1 v d dv dd
  have i2 : mI w w2 := HC d v w w2 dd dv dw dw2 ad aw2
  have i3 : mI w2 w1 := H.a2 v d w2 v w0 w1 dv dd dw2 dv dw0 dw1 aw2 aw (m_isoRefl H dv) i1
  exact H.it w w2 w1 dw dw2 dw1 i2 i3

theorem valid_a3 (M : Type) [Nonempty M] [s : Structure NL M] : M↓[NL] ⊧ sWith fA3 := by
  show ev (![] : Fin 0 → M) (sWith fA3)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fA3, ev_imp]
  exact fun hP => ev_sA3.mpr (m_a3 H (ev_sAP.mp hP))
theorem valid_m3 (M : Type) [Nonempty M] [s : Structure NL M] : M↓[NL] ⊧ sWith fM3 := by
  show ev (![] : Fin 0 → M) (sWith fM3)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fM3, ev_imp]
  exact fun hP hC => ev_sM3.mpr (m_m3 H (ev_sMP.mp hP) (ev_sAC.mp hC))

end semantics

section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Theory SourceL} [T.Δ₁]

/-- The sum with a successor on the left, from the predecessor law of addition. -/
theorem a3_of_predecessor (S : SourceFacts (V := V) T)
    (hAP : T.internalize V ⊢ (tHyp sAP : Bootstrapping.Semiformula V SourceL 0)) :
    T.internalize V ⊢ (tHyp sA3 : Bootstrapping.Semiformula V SourceL 0) := by
  have h := with_facts (fun _ => (⊤ : Bootstrapping.Semiformula V SourceL 1)) S fA3 valid_a3
  unfold fA3 at h
  rw [instS_imp] at h
  exact tmp h hAP

/-- The product with a successor on the left, from the predecessor law of multiplication and
commutativity of addition. -/
theorem m3_of_predecessor (S : SourceFacts (V := V) T)
    (hMP : T.internalize V ⊢ (tHyp sMP : Bootstrapping.Semiformula V SourceL 0))
    (hAC : T.internalize V ⊢ (tHyp sAC : Bootstrapping.Semiformula V SourceL 0)) :
    T.internalize V ⊢ (tHyp sM3 : Bootstrapping.Semiformula V SourceL 0) := by
  have h := with_facts (fun _ => (⊤ : Bootstrapping.Semiformula V SourceL 1)) S fM3 valid_m3
  unfold fM3 at h
  rw [instS_imp, instS_imp] at h
  exact tmp (tmp h hMP) hAC

#print axioms a3_of_predecessor
#print axioms m3_of_predecessor
end generic

#print axioms m_a3
#print axioms m_m3
#print axioms valid_a3
#print axioms valid_m3
end PA194GuardedCompiler
