import ZFCinPA.ModelCodedNamedLogicalNormalization254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedProofRenaming
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254.namedExists_as_negAll
#print axioms LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254.relativeConj_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254.relativeConj_intro
#print axioms LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254.relativeConj_left
#print axioms LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254.relativeConj_right
#print axioms LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254.namedExists_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254.relativeExists_equiv
example (a : V) (p : Formula V ℒₛₑₜ) : ∼namedFormula a (∼p) = namedExists a p := namedExists_as_negAll a p
example (T : InternalTheory V ℒₛₑₜ) (p q : Formula V ℒₛₑₜ) :
    T ⊢ ((p 🡒 (q 🡒 ⊥)) 🡒 ⊥) 🡘 (p ⋏ q) := relativeConj_equiv T p q
example (T : InternalTheory V ℒₛₑₜ) (p q : Formula V ℒₛₑₜ) (hp : T ⊢ p) (hq : T ⊢ q) :
    T ⊢ ((p 🡒 (q 🡒 ⊥)) 🡒 ⊥) := relativeConj_intro T hp hq
example (T : InternalTheory V ℒₛₑₜ) (p q : Formula V ℒₛₑₜ)
    (h : T ⊢ ((p 🡒 (q 🡒 ⊥)) 🡒 ⊥)) : T ⊢ p := relativeConj_left T h
example (T : InternalTheory V ℒₛₑₜ) (p q : Formula V ℒₛₑₜ)
    (h : T ⊢ ((p 🡒 (q 🡒 ⊥)) 🡒 ⊥)) : T ⊢ q := relativeConj_right T h
example (T : SetTheory) [T.Δ₁] (a : V)
    (hg : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p))
    (p q : Formula V ℒₛₑₜ) (h : T.internalize V ⊢ p 🡘 q) :
    T.internalize V ⊢ namedExists a p 🡘 namedExists a q := namedExists_equiv T a hg p q h
example (T : SetTheory) [T.Δ₁] (a : V)
    (hg : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p))
    (p : Formula V ℒₛₑₜ) :
    T.internalize V ⊢ (namedFormula a (p 🡒 ⊥) 🡒 ⊥) 🡘 namedExists a p := relativeExists_equiv T a hg p
example (a : V) (p : Formula V ℒₛₑₜ) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ (namedFormula a (p 🡒 ⊥) 🡒 ⊥) 🡘 namedExists a p :=
  relativeExists_equiv 𝗭𝗙 a (fun _ hp => zf_provable_namedAll a hp) p
example (p : Formula V ℒₛₑₜ) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢ (namedFormula (0 : V) (p 🡒 ⊥) 🡒 ⊥) 🡘 namedExists (0 : V) p :=
  relativeExists_equiv 𝗭𝗙𝗖 0 (fun _ hp => zfc_provable_namedAll 0 hp) p
example (T : InternalTheory V ℒₛₑₜ) (p q r : Formula V ℒₛₑₜ)
    (hp : T ⊢ p) (hq : T ⊢ q) (hr : T ⊢ r) :
    T ⊢ ((((p 🡒 (q 🡒 ⊥)) 🡒 ⊥) 🡒 (r 🡒 ⊥)) 🡒 ⊥) :=
  relativeConj_intro T (relativeConj_intro T hp hq) hr
