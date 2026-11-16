module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceSuccessorSyntax
public import PA196.Arithmetic.Transport.NumericPAeqVariableCoherenceCalibration
public import PA196.Arithmetic.Transport.NumericPAeqSubstitutionVariableSupply
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
noncomputable def rightTransportTyped (E R : SF (V:=V) 2) : SF (V:=V) 0 :=
  ∀¹ ∀¹ ∀¹ ((binary R (Semiterm.bvar 2) (Semiterm.bvar 1) ⋏
    binary E (Semiterm.bvar 0) (Semiterm.bvar 1)) 🡒 binary R (Semiterm.bvar 2) (Semiterm.bvar 0))
@[simp] theorem rightTransportTyped_shift (E R : SF (V:=V) 2) :
    (rightTransportTyped E R).shift=rightTransportTyped E.shift R.shift := by simp [rightTransportTyped]
noncomputable def variablePredicate (D : SF (V:=V) 1) (E : SF (V:=V) 2) (a : ST (V:=V) 0) : SF (V:=V) 1 :=
  unary D (Semiterm.bvar 0) ⋏ binary E (Semiterm.bvar 0) a.bShift
@[simp] theorem variablePredicate_shift (D : SF (V:=V) 1) (E : SF (V:=V) 2) (a : ST (V:=V) 0) :
    (variablePredicate D E a).shift=variablePredicate D.shift E.shift a.shift := by
  simp [variablePredicate, Bootstrapping.Semiterm.bShift_shift_comm]
@[simp] theorem unary_variablePredicate (D : SF (V:=V) 1) (E : SF (V:=V) 2) (a r : ST (V:=V) 0) :
    unary (variablePredicate D E a) r=unary D r ⋏ binary E r a := by
  simp [variablePredicate,unary,Bootstrapping.Semiformula.substs_and,
    Bootstrapping.Semiformula.substs_substs,Matrix.comp_vecCons'']
variable {T : InternalTheory V L}
noncomputable def rightTransportAt {Γ : ND.Seq (V:=V)} (E R : SF (V:=V) 2) (r a s : ST (V:=V) 0)
    (h : ND.Proof (T:=T) Γ (rightTransportTyped E R))
    (hi : ND.Proof (T:=T) Γ (binary R r a)) (he : ND.Proof (T:=T) Γ (binary E s a)) :
    ND.Proof (T:=T) Γ (binary R r s) := by
  have h1 : ND.Proof (T:=T) Γ (∀¹ ∀¹ ((binary R r.bShift.bShift (Semiterm.bvar 1) ⋏
      binary E (Semiterm.bvar 0) (Semiterm.bvar 1)) 🡒 binary R r.bShift.bShift (Semiterm.bvar 0))) := by
    simpa [rightTransportTyped,SemitermVec.q] using ND.allElim h r
  have h2 : ND.Proof (T:=T) Γ (∀¹ ((binary R r.bShift a.bShift ⋏
      binary E (Semiterm.bvar 0) a.bShift) 🡒 binary R r.bShift (Semiterm.bvar 0))) := by
    have hh := ND.allElim h1 a
    simp only [Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
      Bootstrapping.Semiformula.substs_and,binary_subst,Bootstrapping.Semiterm.bShift_substs_q,
      Bootstrapping.Semiterm.bShift_substs_sing,Bootstrapping.Semiterm.substs_bvar] at hh
    simpa [SemitermVec.q] using hh
  have hh : ND.Proof (T:=T) Γ ((binary R r a ⋏ binary E s a) 🡒 binary R r s) := by
    simpa using ND.allElim h2 s
  exact ND.mp (ND.andIntro hi he) hh

theorem rightTransportTyped_quote : rightTransportTyped (equalityPredicate (V:=V)) isoPredicate =
    ⌜RelationalClosedCertificate.isoRightTransportClosed⌝ := by
  rw [RelationalClosedCertificate.isoRightTransportClosed_eq]
  simp [rightTransportTyped,←FFL.FirstOrder.Semiterm.typed_quote_bvar]
#print axioms rightTransportAt
#print axioms rightTransportTyped_quote
#print axioms unary_variablePredicate
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
