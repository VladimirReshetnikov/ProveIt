import DiophantineConsistency.IPRAReferenceEqualityImages

/-! Preliminary syntactic image of equality-only successor-step open induction.
No native theory derivation is claimed in this module. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAReferenceInductionImage
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open IPRAOrderErasure IPRAReferenceRew IPRAReferenceImages
open PRAFiniteFunctionCodes

def nativeAtSucc {n : ℕ} (φ : Semisentenceᵢ PRALanguage.language (n+1)) :
    Semisentenceᵢ PRALanguage.language (n+1) :=
  Rew.subst (Fin.cases (.func Code.succ (fun _ => #0)) (fun i => #i.succ)) ▹ φ

def nativeSuccInduction {n : ℕ} (φ : Semisentenceᵢ PRALanguage.language (n+1)) :
    Sentenceᵢ PRALanguage.language :=
  ∀⁰* (IPRANativeInduction.atZero φ 🡒 (∀⁰ (φ 🡒 nativeAtSucc φ)) 🡒 ∀⁰ φ)

theorem embed_atZero {n : ℕ} (φ : Semisentenceᵢ IPRAEqualityOnlyReference.language (n+1)) :
    embed (IPRAEqualityOnlyReference.atZero φ) = IPRANativeInduction.atZero (embed φ) := by
  unfold IPRAEqualityOnlyReference.atZero IPRANativeInduction.atZero
  rw [embed_rew, embedRew_subst]
  congr 2
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [IPRAEqualityOnlyReference.applyCode, IPRANativeInduction.zeroTerm,
      Semiterm.lMap_func, toNative]
    funext k
    exact Fin.elim0 k
  · rfl

theorem embed_atSucc {n : ℕ} (φ : Semisentenceᵢ IPRAEqualityOnlyReference.language (n+1)) :
    embed (IPRAEqualityOnlyReference.atSucc φ) = nativeAtSucc (embed φ) := by
  unfold IPRAEqualityOnlyReference.atSucc nativeAtSucc
  rw [embed_rew, embedRew_subst]
  congr 2
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

theorem embed_inductionAxiom {n : ℕ}
    (φ : Semisentenceᵢ IPRAEqualityOnlyReference.language (n+1)) :
    embed (IPRAEqualityOnlyReference.inductionAxiom φ) =
      nativeSuccInduction (embed φ) := by
  simp only [IPRAEqualityOnlyReference.inductionAxiom, nativeSuccInduction,
    embed_allClosure, embed, embed_atZero, embed_atSucc]
  rfl

end DiophantineConsistency.IPRAReferenceInductionImage
