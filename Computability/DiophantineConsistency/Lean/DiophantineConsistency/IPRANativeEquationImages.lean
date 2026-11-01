import DiophantineConsistency.IPRANativeAxiomImage
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
set_option autoImplicit false
namespace DiophantineConsistency.IPRANativeEquationImages
variable {L : Language} {Λ : Hilbertᵢ L}
theorem allClosure_fixitr_imp {p q : Propositionᵢ L} (h : Λ ⊢ p 🡒 q) :
    (m : ℕ) → Λ ⊢ (∀⁰* (Rew.fixitr 0 m ▹ p)) 🡒 (∀⁰* (Rew.fixitr 0 m ▹ q))
  | 0 => by simpa using h
  | m + 1 => by
    simp only [LawfulSyntacticRewriting.allClosure_fixitr]
    obtain ⟨h⟩ := allClosure_fixitr_imp h m
    apply Nonempty.intro
    apply Entailment.mdp (HilbertProofᵢ.allImplyAllOfAllImply _ _)
    apply HilbertProofᵢ.gen
    exact Entailment.cast h (by simp)

def openAll : (n : ℕ) → Semipropositionᵢ L n → Propositionᵢ L
  | 0, φ => φ
  | n+1, φ => openAll n (Rewriting.free φ)

def bindAll (n : ℕ) (p : Propositionᵢ L) : Semipropositionᵢ L n := by
  simpa only [Nat.zero_add] using (Rew.fixitr 0 n ▹ p)
theorem fix_cast {n m : ℕ} (h : n = m) (φ : Semipropositionᵢ L n) :
    cast (congrArg (Semipropositionᵢ L) (congrArg Nat.succ h)) (Rewriting.fix φ) =
      Rewriting.fix (cast (congrArg (Semipropositionᵢ L) h) φ) := by
  cases h
  rfl
theorem openAll_inverse (n : ℕ) (φ : Semipropositionᵢ L n) :
    bindAll n (openAll n φ) = φ := by
  induction n with
  | zero => simp [bindAll, openAll, Rew.fixitr_zero]
  | succ n ih =>
    have h := congrArg Rewriting.fix (ih (Rewriting.free φ))
    simpa [bindAll, openAll, Rew.fixitr_succ, TransitiveRewriting.comp_app,
      LawfulSyntacticRewriting.fix_free, fix_cast] using h
theorem openAll_neg (n : ℕ) (φ : Semipropositionᵢ L n) :
    openAll n (∼φ) = ∼openAll n φ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [openAll, LogicalConnective.HomClass.map_neg, ih]

theorem allClosure_cast {n m : ℕ} (h : n = m) (φ : Semipropositionᵢ L n) :
    (∀⁰* cast (congrArg (Semipropositionᵢ L) h) φ) = (∀⁰* φ) := by
  cases h
  rfl

theorem allClosure_dni [L.DecidableEq] (n : ℕ) (φ : Semipropositionᵢ L n) :
    Λ ⊢ (∀⁰* φ) 🡒 (∀⁰* (∼∼φ)) := by
  have h : Λ ⊢ openAll n φ 🡒 ∼∼openAll n φ := ⟨Entailment.dni⟩
  have hh := allClosure_fixitr_imp h n
  have hi := congrArg (fun x : Semipropositionᵢ L n => ∀⁰* x) (openAll_inverse n φ)
  have hj := congrArg (fun x : Semipropositionᵢ L n => ∀⁰* x) (openAll_inverse n (∼∼φ))
  have hc1 := allClosure_cast (Nat.zero_add n) (Rew.fixitr 0 n ▹ openAll n φ)
  have hc2 := allClosure_cast (Nat.zero_add n) (Rew.fixitr 0 n ▹ openAll n (∼∼φ))
  have hi' : (∀⁰* (Rew.fixitr 0 n ▹ openAll n φ)) = ∀⁰* φ := hc1.symm.trans hi
  have hj' : (∀⁰* (Rew.fixitr 0 n ▹ openAll n (∼∼φ))) = ∀⁰* (∼∼φ) := hc2.symm.trans hj
  rw [←hi', ←hj']
  simpa only [openAll_neg] using hh
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRAQuantifierFree
open IPRANativeTheory IPRANativeAxiomImage

local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem equality_image {n : ℕ} (a b : TermN n) :
    nativeTheory ⊢ equalClosureI a b 🡒 (equalClosure a b)ᴺ := by
  have h := allClosure_dni (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language)) n
    (Rewriting.emb (Semiformulaᵢ.rel Language.ORing.Rel.eq ![a,b]))
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Theoryᵢ.ofHilbert
  simpa [equalClosureI, equalClosure, gg_allClosure] using h
theorem from_equality {n : ℕ} (a b : TermN n)
    (h : NativeAxiom (equalClosureI a b)) : nativeTheory ⊢ (equalClosure a b)ᴺ :=
  mdp! (equality_image a b) (native_axiom h)

theorem definingEquation_image {σ : Sentence language} (h : DefiningEquation σ) :
    nativeTheory ⊢ σᴺ := by
  cases h with
  | zero n =>
    simpa only [zeroEquation, zeroEquationI] using
      (from_equality _ _ (NativeAxiom.defining (DefiningEquationI.zero n)))
  | projection i =>
    simpa only [projectionEquation, projectionEquationI] using
      (from_equality _ _ (NativeAxiom.defining (DefiningEquationI.projection i)))
  | composition f g =>
    simpa only [compositionEquation, compositionEquationI] using
      (from_equality _ _ (NativeAxiom.defining (DefiningEquationI.composition f g)))
  | recursionBase f g =>
    simpa only [recursionBaseEquation, recursionBaseEquationI] using
      (from_equality _ _ (NativeAxiom.defining (DefiningEquationI.recursionBase f g)))
  | recursionStep f g =>
    simpa only [recursionStepEquation, recursionStepEquationI] using
      (from_equality _ _ (NativeAxiom.defining (DefiningEquationI.recursionStep f g)))
end DiophantineConsistency.IPRANativeEquationImages
