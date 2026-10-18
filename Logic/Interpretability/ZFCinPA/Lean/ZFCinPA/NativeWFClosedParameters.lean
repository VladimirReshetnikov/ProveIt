import ZFCinPA.InternalInterpretation
import ZFCinPA.RawFormQuotation
import BusyBeaver.ZFC.WellFoundedPart

set_option autoImplicit false
noncomputable section

/-!
Closed syntax parameters for the native well-founded quotient interpretation.
The raw formulas are the existing attributed quotient formulas. Closure is
explicit, following NativeInterp; this is a distinct parameter from the earlier
unclosed NativeWFParameters draft. No equality between those codes is asserted.
Only syntactic Good is proved here, not domain nonemptiness or axiom transport.
-/

namespace LeanProofs.ZFCinPA.NativeWFClosedParameters

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic

def domainRaw : _root_.SetTheory.Form :=
  QuotientModel.translate (WellFoundedPart.wfForm 0)
def equalityRaw : _root_.SetTheory.Form := ProfileSyntax.eqvForm 0 1
def membershipRaw : _root_.SetTheory.Form := QuotientModel.memberForm 0 1

def domainFormula : Semisentence ℒₛₑₜ 1 := RawFormQuotation.closed 0 domainRaw
def equalityFormula : Semisentence ℒₛₑₜ 2 := RawFormQuotation.closed 1 equalityRaw
def membershipFormula : Semisentence ℒₛₑₜ 2 := RawFormQuotation.closed 1 membershipRaw

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def domainCode : V := ⌜domainFormula⌝
def equalityCode : V := ⌜equalityFormula⌝
def membershipCode : V := ⌜membershipFormula⌝
def parameter : V := ⟪domainCode, ⟪equalityCode, membershipCode⟫⟫

theorem isSemiformula_domainCode : IsSemiformula ℒₛₑₜ 1 (domainCode (V := V)) := by
  simpa only [Nat.cast_one, domainCode] using
    (RawFormQuotation.isSemiformula_quote_sen (V := V) domainFormula)

theorem isSemiformula_equalityCode : IsSemiformula ℒₛₑₜ 2 (equalityCode (V := V)) :=
  RawFormQuotation.isSemiformula_quote_sen equalityFormula

theorem isSemiformula_membershipCode : IsSemiformula ℒₛₑₜ 2 (membershipCode (V := V)) :=
  RawFormQuotation.isSemiformula_quote_sen membershipFormula

theorem shift_domainCode : shift ℒₛₑₜ (domainCode (V := V)) = domainCode :=
  RawFormQuotation.shift_quote_sen domainFormula

theorem shift_equalityCode : shift ℒₛₑₜ (equalityCode (V := V)) = equalityCode :=
  RawFormQuotation.shift_quote_sen equalityFormula

theorem shift_membershipCode : shift ℒₛₑₜ (membershipCode (V := V)) = membershipCode :=
  RawFormQuotation.shift_quote_sen membershipFormula

theorem dom_parameter : InternalInterpretation.dom (parameter (V := V)) = domainCode := by
  simp [InternalInterpretation.dom, parameter]

theorem atom_parameter_zero :
    InternalInterpretation.atomOf (parameter (V := V)) 0 = equalityCode := by
  simp [InternalInterpretation.atomOf, parameter]

theorem atom_parameter_ne (R : V) (hR : R ≠ 0) :
    InternalInterpretation.atomOf (parameter (V := V)) R = membershipCode := by
  simp [InternalInterpretation.atomOf, parameter, hR]

theorem good_parameter : InternalInterpretation.Good (parameter (V := V)) := by
  constructor
  · rw [dom_parameter]
    exact isSemiformula_domainCode
  · rw [dom_parameter]
    exact shift_domainCode
  · intro R
    by_cases hR : R = 0
    · subst R
      rw [atom_parameter_zero]
      exact isSemiformula_equalityCode
    · rw [atom_parameter_ne R hR]
      exact isSemiformula_membershipCode
  · intro R
    by_cases hR : R = 0
    · subst R
      rw [atom_parameter_zero]
      exact shift_equalityCode
    · rw [atom_parameter_ne R hR]
      exact shift_membershipCode

end LeanProofs.ZFCinPA.NativeWFClosedParameters
