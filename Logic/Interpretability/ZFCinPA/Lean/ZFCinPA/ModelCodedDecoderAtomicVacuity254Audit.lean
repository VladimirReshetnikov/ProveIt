import ZFCinPA.ModelCodedDecoderAtomicVacuity254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedBindOne
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254.namedBody_memAtom
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254.namedBody_free_of_bindOne
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254.namedFormula_vacuous_of_bindOne
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254.bindOneAt_eqAtom_of_ne
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254.bindOneAt_memAtom_of_ne
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254.namedFormula_eq_vacuous
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254.namedFormula_mem_vacuous
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254.decoded_vacuity_of_bindOne
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254.decoded_weq_vacuity
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254.decoded_wel_vacuity
example (a b c : V) :
    namedBody a (memAtom (Semiterm.fvar b) (Semiterm.fvar c)) =
      memAtom (namedVar a b) (namedVar a c) := namedBody_memAtom a b c
example (a : V) (p : Formula V ℒₛₑₜ) (h : bindOneAt ℒₛₑₜ a 0 p.val = p.val) :
    (namedBody a p).free = p.shift := namedBody_free_of_bindOne a p h
example (T : InternalTheory V ℒₛₑₜ) (a : V) (p : Formula V ℒₛₑₜ)
    (h : bindOneAt ℒₛₑₜ a 0 p.val = p.val) :
    T ⊢! p 🡒 namedFormula a p := namedFormula_vacuous_of_bindOne T a p h
example (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    bindOneAt ℒₛₑₜ c 0 (eqAtom (Semiterm.fvar a) (Semiterm.fvar b) : Formula V ℒₛₑₜ).val =
      (eqAtom (Semiterm.fvar a) (Semiterm.fvar b) : Formula V ℒₛₑₜ).val := bindOneAt_eqAtom_of_ne a b c hca hcb
example (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    bindOneAt ℒₛₑₜ c 0 (memAtom (Semiterm.fvar a) (Semiterm.fvar b) : Formula V ℒₛₑₜ).val =
      (memAtom (Semiterm.fvar a) (Semiterm.fvar b) : Formula V ℒₛₑₜ).val := bindOneAt_memAtom_of_ne a b c hca hcb
example (T : InternalTheory V ℒₛₑₜ) (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    T ⊢! eqAtom (Semiterm.fvar a) (Semiterm.fvar b) 🡒
      namedFormula c (eqAtom (Semiterm.fvar a) (Semiterm.fvar b)) := namedFormula_eq_vacuous T a b c hca hcb
example (T : InternalTheory V ℒₛₑₜ) (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    T ⊢! memAtom (Semiterm.fvar a) (Semiterm.fvar b) 🡒
      namedFormula c (memAtom (Semiterm.fvar a) (Semiterm.fvar b)) := namedFormula_mem_vacuous T a b c hca hcb
example (T : SetTheory) [T.Δ₁] (a n : V)
    (h : bindOneAt ℒₛₑₜ a 0 (decode n) = decode n) :
    Provable T (decode (ArithmeticCode254.wim n (ArithmeticCode254.wal a n))) :=
  decoded_vacuity_of_bindOne T a n h
example (T : SetTheory) [T.Δ₁] (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    Provable T (decode (ArithmeticCode254.wim (ArithmeticCode254.weq a b)
      (ArithmeticCode254.wal c (ArithmeticCode254.weq a b)))) := decoded_weq_vacuity T a b c hca hcb
example (T : SetTheory) [T.Δ₁] (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    Provable T (decode (ArithmeticCode254.wim (ArithmeticCode254.wel a b)
      (ArithmeticCode254.wal c (ArithmeticCode254.wel a b)))) := decoded_wel_vacuity T a b c hca hcb
example (c : V) (hc : c ≠ 0) :
    Provable (𝗭𝗙 : SetTheory) (decode (ArithmeticCode254.wim (ArithmeticCode254.weq (0 : V) 0)
      (ArithmeticCode254.wal c (ArithmeticCode254.weq (0 : V) 0)))) := decoded_weq_vacuity 𝗭𝗙 0 0 c hc hc
example : Provable (𝗭𝗙𝗖 : SetTheory) (decode (ArithmeticCode254.wim (ArithmeticCode254.wel (1 : V) 1)
      (ArithmeticCode254.wal (0 : V) (ArithmeticCode254.wel (1 : V) 1)))) :=
  decoded_wel_vacuity 𝗭𝗙𝗖 1 1 0 (by simp) (by simp)
