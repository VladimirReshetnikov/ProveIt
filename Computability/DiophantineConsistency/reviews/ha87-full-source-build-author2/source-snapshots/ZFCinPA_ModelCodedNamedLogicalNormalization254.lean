import ZFCinPA.ModelCodedDecoderRho1_254

set_option autoImplicit false

/-!
Finite logical normalization of the implication/Bottom conjunction and named
existential encodings used by Circuit.interpret. Matrices and labels remain
arbitrary internal values. Existential congruence exposes the exact target GEN
resource; propositional normalization uses no theory axiom. This module does
not prove the container or image-collection schemas.
-/
namespace LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def namedExists (a : V) (p : Formula V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  ∃⁰ namedBody a p

lemma namedExists_as_negAll (a : V) (p : Formula V ℒₛₑₜ) :
    ∼namedFormula a (∼p) = namedExists a p := by
  simp only [namedFormula,namedExists,namedBody_neg,
    Bootstrapping.Semiformula.neg_all,TildeInvolutive.neg_involutive]

theorem relativeConj_equiv (T : InternalTheory V ℒₛₑₜ)
    (p q : Formula V ℒₛₑₜ) : T ⊢ ((p 🡒 (q 🡒 ⊥)) 🡒 ⊥) 🡘 (p ⋏ q) := by
  classical
  exact E!_symm (E!_trans (show T ⊢ (p ⋏ q) 🡘 (((p ⋏ q) 🡒 ⊥) 🡒 ⊥) from ECCOO!)
    (ECC!_of_E!_of_E! (show T ⊢ ((p ⋏ q) 🡒 ⊥) 🡘 (p 🡒 (q 🡒 ⊥)) from ECKCC!) ⟨E_Id⟩))

theorem relativeConj_intro (T : InternalTheory V ℒₛₑₜ)
    {p q : Formula V ℒₛₑₜ} (hp : T ⊢ p) (hq : T ⊢ q) :
    T ⊢ ((p 🡒 (q 🡒 ⊥)) 🡒 ⊥) :=
  (iff_of_E! (relativeConj_equiv T p q)).mpr (K!_intro hp hq)

theorem relativeConj_left (T : InternalTheory V ℒₛₑₜ)
    {p q : Formula V ℒₛₑₜ} (h : T ⊢ ((p 🡒 (q 🡒 ⊥)) 🡒 ⊥)) : T ⊢ p :=
  K!_left ((iff_of_E! (relativeConj_equiv T p q)).mp h)

theorem relativeConj_right (T : InternalTheory V ℒₛₑₜ)
    {p q : Formula V ℒₛₑₜ} (h : T ⊢ ((p 🡒 (q 🡒 ⊥)) 🡒 ⊥)) : T ⊢ q :=
  K!_right ((iff_of_E! (relativeConj_equiv T p q)).mp h)

theorem namedExists_equiv (T : SetTheory) [T.Δ₁] (a : V)
    (hGen : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p))
    (p q : Formula V ℒₛₑₜ) (h : T.internalize V ⊢ p 🡘 q) :
    T.internalize V ⊢ namedExists a p 🡘 namedExists a q := by
  classical
  have he := ENN!_of_E! (namedFormula_equiv T a hGen (∼p) (∼q) (ENN!_of_E! h))
  simpa only [namedExists_as_negAll] using he

theorem relativeExists_equiv (T : SetTheory) [T.Δ₁] (a : V)
    (hGen : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p))
    (p : Formula V ℒₛₑₜ) :
    T.internalize V ⊢ (namedFormula a (p 🡒 ⊥) 🡒 ⊥) 🡘 namedExists a p := by
  classical
  have hi : T.internalize V ⊢ namedFormula a (p 🡒 ⊥) 🡘 namedFormula a (∼p) :=
    namedFormula_equiv T a hGen _ _ (E!_symm neg_equiv!)
  have he := E!_trans (show T.internalize V ⊢
      (namedFormula a (p 🡒 ⊥) 🡒 ⊥) 🡘 ∼namedFormula a (p 🡒 ⊥)
        from E!_symm neg_equiv!) (ENN!_of_E! hi)
  simpa only [namedExists_as_negAll] using he

end LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254
