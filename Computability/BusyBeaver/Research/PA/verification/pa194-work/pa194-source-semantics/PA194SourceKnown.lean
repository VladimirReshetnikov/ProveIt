import PA194SourceInduction
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Using the ten source facts that already have internal proofs

Ten of the twelve `SourceFacts` have internal proofs in the source theory that do not depend
on the other two (`sA2`, `sM2`). A further fact may therefore be proved in a structure under
these ten as hypotheses:

* `sWith10 F`: the sentence `F` under the ten hypotheses; `ev_sWith10` is its meaning
  (`MTheta10`).
* `TenFacts T`: internal provability of the ten; `with_ten` discharges them.
* `Known N`: the consequences of the ten that the proofs in this directory use, as
  statements about membership in a structure `N` of the source language; `known_of`.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194Schematic

/-- A sentence under the ten hypotheses. -/
def sWith10 (F : SF 0) : SF 0 :=
  sE1 🡒 sEI 🡒 sIs 🡒 sIt 🡒 sZ1 🡒 sZ2 🡒 sS1 🡒 sS2 🡒 sA1 🡒 sM1 🡒 F

section semantics
variable {M : Type} [s : Structure NL M]

structure MTheta10 (M : Type) [s : Structure NL M] : Prop where
  e1 : ∀ x : M, mE x x
  ei : ∀ x a b : M, mD a → mD b → mE a x → mE b x → mI a b
  is : ∀ a b : M, mD a → mD b → mI a b → mI b a
  it : ∀ a b c : M, mD a → mD b → mD c → mI a b → mI b c → mI a c
  z1 : ∃ z : M, mD z ∧ mZ z
  z2 : ∀ a b : M, mD a → mZ a → mD b → mZ b → mI a b
  s1 : ∀ u : M, mD u → ∃ w : M, mD w ∧ mS u w
  s2 : ∀ u w u' w' : M, mD u → mD w → mD u' → mD w' → mS u w → mS u' w' → mI u u' → mI w w'
  a1 : ∀ u u' : M, mD u → mD u' → ∃ w : M, mD w ∧ mA u u' w
  m1 : ∀ u u' : M, mD u → mD u' → ∃ w : M, mD w ∧ mMu u u' w

theorem ev_sWith10 (F : SF 0) :
    ev (![] : Fin 0 → M) (sWith10 F) ↔ (MTheta10 M → ev (![] : Fin 0 → M) F) := by
  unfold sWith10
  simp only [ev_imp, ev_sE1, ev_sEI, ev_sIs, ev_sIt, ev_sZ1, ev_sZ2, ev_sS1, ev_sS2, ev_sA1,
    ev_sM1]
  constructor
  · intro h H
    exact h H.e1 H.ei H.is H.it H.z1 H.z2 H.s1 H.s2 H.a1 H.m1
  · intro h a b c d e f g i j k
    exact h ⟨a, b, c, d, e, f, g, i, j, k⟩

end semantics

section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Theory SourceL} [T.Δ₁]

/-- Internal provability of the ten facts. -/
structure TenFacts (T : Theory SourceL) [T.Δ₁] : Prop where
  e1 : T.internalize V ⊢ (tHyp sE1 : Bootstrapping.Semiformula V SourceL 0)
  ei : T.internalize V ⊢ (tHyp sEI : Bootstrapping.Semiformula V SourceL 0)
  is : T.internalize V ⊢ (tHyp sIs : Bootstrapping.Semiformula V SourceL 0)
  it : T.internalize V ⊢ (tHyp sIt : Bootstrapping.Semiformula V SourceL 0)
  z1 : T.internalize V ⊢ (tHyp sZ1 : Bootstrapping.Semiformula V SourceL 0)
  z2 : T.internalize V ⊢ (tHyp sZ2 : Bootstrapping.Semiformula V SourceL 0)
  s1 : T.internalize V ⊢ (tHyp sS1 : Bootstrapping.Semiformula V SourceL 0)
  s2 : T.internalize V ⊢ (tHyp sS2 : Bootstrapping.Semiformula V SourceL 0)
  a1 : T.internalize V ⊢ (tHyp sA1 : Bootstrapping.Semiformula V SourceL 0)
  m1 : T.internalize V ⊢ (tHyp sM1 : Bootstrapping.Semiformula V SourceL 0)

/-- A sentence proved under the ten hypotheses is proved. -/
theorem with_ten (K : TenFacts (V := V) T) (F : SF 0)
    (h : T.internalize V ⊢ (tHyp (sWith10 F) : Bootstrapping.Semiformula V SourceL 0)) :
    T.internalize V ⊢ (tHyp F : Bootstrapping.Semiformula V SourceL 0) := by
  have h' : T.internalize V ⊢
      instS (sig (fun _ => (⊤ : Bootstrapping.Semiformula V SourceL 1))) (sWith10 F) := h
  unfold sWith10 at h'
  simp only [instS_imp] at h'
  exact tmp (tmp (tmp (tmp (tmp (tmp (tmp (tmp (tmp (tmp h' K.e1) K.ei) K.is) K.it) K.z1) K.z2)
    K.s1) K.s2) K.a1) K.m1

#print axioms with_ten
end generic
end PA194GuardedCompiler

namespace PA194SourceModel
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194ModelLogic PA194BindSource PA194Schematic PA194GuardedCompiler

attribute [local instance] PA194ModelLogic.sourceLanguageAdjTheory

/-- The consequences of the ten facts used in this directory, about a structure. -/
structure Known (N : Type) [s : Structure SourceL N] : Prop where
  irefl : ∀ a : N, SDom a → SIso a a
  isym : ∀ a c : N, SDom a → SDom c → SIso a c → SIso c a
  itrans : ∀ a c d : N, SDom a → SDom c → SDom d → SIso a c → SIso c d → SIso a d
  z1 : ∃ z : N, SDom z ∧ SZero z
  z2 : ∀ a c : N, SDom a → SZero a → SDom c → SZero c → SIso a c
  s1 : ∀ u : N, SDom u → ∃ w : N, SDom w ∧ SSucc u w
  s2 : ∀ u w u' w' : N, SDom u → SDom w → SDom u' → SDom w' → SSucc u w → SSucc u' w' →
    SIso u u' → SIso w w'
  a1 : ∀ u u' : N, SDom u → SDom u' → ∃ w : N, SDom w ∧ SAdd u u' w
  m1 : ∀ u u' : N, SDom u → SDom u' → ∃ w : N, SDom w ∧ SMul u u' w

section model
variable {N : Type} [s : Structure SourceL N] [Structure.Eq SourceL N]

theorem known_of (f : ℕ → N) (H : @MTheta10 N (sourceLetters s f)) : Known N := by
  obtain ⟨e1, ei, is', it', z1, z2, s1, s2, a1, m1⟩ := H
  exact {
  irefl := fun a da => (mI_iff f a a).mp
    (ei a a a ((mD_iff f a).mpr da) ((mD_iff f a).mpr da) (e1 a) (e1 a))
  isym := fun a c da dc h => (mI_iff f c a).mp
    (is' a c ((mD_iff f a).mpr da) ((mD_iff f c).mpr dc) ((mI_iff f a c).mpr h))
  itrans := fun a c d da dc dd h h' => (mI_iff f a d).mp
    (it' a c d ((mD_iff f a).mpr da) ((mD_iff f c).mpr dc) ((mD_iff f d).mpr dd)
      ((mI_iff f a c).mpr h) ((mI_iff f c d).mpr h'))
  z1 := by
    obtain ⟨z, dz, zz⟩ := z1
    exact ⟨z, (mD_iff f z).mp dz, (mZ_iff f z).mp zz⟩
  z2 := fun a c da za dc zc => (mI_iff f a c).mp
    (z2 a c ((mD_iff f a).mpr da) ((mZ_iff f a).mpr za) ((mD_iff f c).mpr dc)
      ((mZ_iff f c).mpr zc))
  s1 := fun u du => by
    obtain ⟨w, dw, sw⟩ := s1 u ((mD_iff f u).mpr du)
    exact ⟨w, (mD_iff f w).mp dw, (mS_iff f u w).mp sw⟩
  s2 := fun u w u' w' du dw du' dw' h h' i => (mI_iff f w w').mp
    (s2 u w u' w' ((mD_iff f u).mpr du) ((mD_iff f w).mpr dw) ((mD_iff f u').mpr du')
      ((mD_iff f w').mpr dw') ((mS_iff f u w).mpr h) ((mS_iff f u' w').mpr h')
      ((mI_iff f u u').mpr i))
  a1 := fun u u' du du' => by
    obtain ⟨w, dw, aw⟩ := a1 u u' ((mD_iff f u).mpr du) ((mD_iff f u').mpr du')
    exact ⟨w, (mD_iff f w).mp dw, (mA_iff f u u' w).mp aw⟩
  m1 := fun u u' du du' => by
    obtain ⟨w, dw, mw⟩ := m1 u u' ((mD_iff f u).mpr du) ((mD_iff f u').mpr du')
    exact ⟨w, (mD_iff f w).mp dw, (mMu_iff f u u' w).mp mw⟩
  }

#print axioms known_of
end model
end PA194SourceModel
