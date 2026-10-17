import ZFCinPA.ModelCodedDecoderRho1_254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedBindOne
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254.termBindOneVecAt_pair
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254.namedBody_eqAtom
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254.namedBody_neg
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254.negEquality_open_at_other
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254.equality_reflexive
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254.existsNamedEquality
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254.decoded_rho1_equiv
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254.decoded_rho1_provable_of_resources
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254.zf_decoded_rho1_provable
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254.zfc_decoded_rho1_provable
example (a depth t u : V) (ht : IsUTerm ℒₛₑₜ t) (hu : IsUTerm ℒₛₑₜ u) :
    termBindOneVecAt ℒₛₑₜ a depth 2 ?[t,u] =
      ?[termBindOneAt ℒₛₑₜ a depth t,termBindOneAt ℒₛₑₜ a depth u] := termBindOneVecAt_pair a depth t u ht hu
example (a b c : V) :
    namedBody a (eqAtom (Semiterm.fvar b) (Semiterm.fvar c)) =
      eqAtom (namedVar a b) (namedVar a c) := namedBody_eqAtom a b c
example (a : V) (p : Formula V ℒₛₑₜ) :
    namedBody a (∼p) = ∼namedBody a p := namedBody_neg a p
example (a b : V) :
    (namedBody a (∼eqAtom (Semiterm.fvar a) (Semiterm.fvar b))).subst ![Semiterm.fvar b] =
      (∼eqAtom (Semiterm.fvar b) (Semiterm.fvar b) : Formula V ℒₛₑₜ) := negEquality_open_at_other a b
example (T : SetTheory) [T.Δ₁] [𝗘𝗤 ℒₛₑₜ ⪯ T] (b : V) :
    T.internalize V ⊢ eqAtom (Semiterm.fvar b) (Semiterm.fvar b) := equality_reflexive T b
example (T : SetTheory) [T.Δ₁] [𝗘𝗤 ℒₛₑₜ ⪯ T] (a b : V) :
    T.internalize V ⊢ ∼namedFormula a (∼eqAtom (Semiterm.fvar a) (Semiterm.fvar b)) :=
  existsNamedEquality T a b
example (T : SetTheory) [T.Δ₁] (a b : V)
    (hf : T.internalize V ⊢ ∼decoded (1 : V))
    (hg : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p)) :
    T.internalize V ⊢ decoded (ArithmeticCode254.rho1 a b) 🡘
      ∼namedFormula a (∼eqAtom (Semiterm.fvar a) (Semiterm.fvar b)) := decoded_rho1_equiv T a b hf hg
example (T : SetTheory) [T.Δ₁] [𝗘𝗤 ℒₛₑₜ ⪯ T] (a b : V)
    (hf : T.internalize V ⊢ ∼decoded (1 : V))
    (hg : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p)) :
    Provable T (decode (ArithmeticCode254.rho1 a b)) := decoded_rho1_provable_of_resources T a b hf hg
example (a b : V) : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticCode254.rho1 a b)) := zf_decoded_rho1_provable a b
example (a b : V) : Provable (𝗭𝗙𝗖 : SetTheory)
    (decode (ArithmeticCode254.rho1 a b)) := zfc_decoded_rho1_provable a b
example (a : V) : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticCode254.rho1 a a)) := zf_decoded_rho1_provable a a
example (a : V) : Provable (𝗭𝗙𝗖 : SetTheory)
    (decode (ArithmeticCode254.rho1 a a)) := zfc_decoded_rho1_provable a a
example : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticCode254.rho1 (0 : V) 0)) := zf_decoded_rho1_provable 0 0
example (b : V) : Provable (𝗭𝗙 : SetTheory)
    (decode (ArithmeticCode254.rho1 (0 : V) b)) := zf_decoded_rho1_provable 0 b
example : Provable (𝗭𝗙𝗖 : SetTheory)
    (decode (ArithmeticCode254.rho1 (0 : V) 0)) := zfc_decoded_rho1_provable 0 0
example (a b : V) : ∃ d : V, Proof (𝗭𝗙 : SetTheory) d
    (decode (ArithmeticCode254.rho1 a b)) := zf_decoded_rho1_provable a b
