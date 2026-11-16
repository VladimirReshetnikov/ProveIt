module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceSuccessorSyntax
public import M6PA.Calibration.NumericPAeqVariableCoherenceCalibration
public import M6PA.Calibration.NumericPAeqFormulaConstructors
public import M6PA.Calibration.RelationalClosedCertificateCoherenceSupply
@[expose] public section
namespace M6.PA.NumericPAeqFormulaEqualityTransport
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def symmetry (D : SF (V:=V) 1) (R : SF (V:=V) 2) : SF (V:=V) 0 :=
  ∀¹ ∀¹ ((unary D (Semiterm.bvar 1) ⋏ binary R (Semiterm.bvar 1) (Semiterm.bvar 0)) 🡒
    binary R (Semiterm.bvar 0) (Semiterm.bvar 1))
noncomputable def transitivity (D : SF (V:=V) 1) (R : SF (V:=V) 2) : SF (V:=V) 0 :=
  ∀¹ ∀¹ ∀¹ ((unary D (Semiterm.bvar 2) ⋏
    (binary R (Semiterm.bvar 2) (Semiterm.bvar 1) ⋏ binary R (Semiterm.bvar 1) (Semiterm.bvar 0))) 🡒
    binary R (Semiterm.bvar 2) (Semiterm.bvar 0))
noncomputable def equalityAtom (A B : SF (V:=V) 1) (R : SF (V:=V) 2) : SF (V:=V) 0 :=
  ∃¹ ∃¹ (unary A (Semiterm.bvar 1) ⋏ (unary B (Semiterm.bvar 0) ⋏ binary R (Semiterm.bvar 1) (Semiterm.bvar 0)))
noncomputable def equalityRemainder (A B : SF (V:=V) 1) (R : SF (V:=V) 2) (x : ST (V:=V) 0) : SF (V:=V) 0 :=
  ∃¹ (unary A x.bShift ⋏ (unary B (Semiterm.bvar 0) ⋏ binary R x.bShift (Semiterm.bvar 0)))
@[simp] theorem symmetry_shift (D : SF (V:=V) 1) (R : SF (V:=V) 2) :
    (symmetry D R).shift=symmetry D.shift R.shift := by simp [symmetry]
@[simp] theorem transitivity_shift (D : SF (V:=V) 1) (R : SF (V:=V) 2) :
    (transitivity D R).shift=transitivity D.shift R.shift := by simp [transitivity]
@[simp] theorem equalityAtom_shift (A B : SF (V:=V) 1) (R : SF (V:=V) 2) :
    (equalityAtom A B R).shift=equalityAtom A.shift B.shift R.shift := by simp [equalityAtom]
@[simp] theorem equalityRemainder_shift (A B : SF (V:=V) 1) (R : SF (V:=V) 2) (x : ST (V:=V) 0) :
    (equalityRemainder A B R x).shift=equalityRemainder A.shift B.shift R.shift x.shift := by
  simp [equalityRemainder,Bootstrapping.Semiterm.bShift_shift_comm]
variable {T : InternalTheory V L}
noncomputable def symmetryAt {Γ : ND.Seq (V:=V)} (D : SF (V:=V) 1) (R : SF (V:=V) 2)
    (a b : ST (V:=V) 0) (h : ND.Proof (T:=T) Γ (symmetry D R))
    (ha : ND.Proof (T:=T) Γ (unary D a)) (hr : ND.Proof (T:=T) Γ (binary R a b)) :
    ND.Proof (T:=T) Γ (binary R b a) := by
  have h1 : ND.Proof (T:=T) Γ (∀¹ ((unary D a.bShift ⋏ binary R a.bShift (Semiterm.bvar 0)) 🡒
      binary R (Semiterm.bvar 0) a.bShift)) := by simpa [symmetry,SemitermVec.q] using ND.allElim h a
  have h2 : ND.Proof (T:=T) Γ ((unary D a ⋏ binary R a b) 🡒 binary R b a) := by
    simpa using ND.allElim h1 b
  exact ND.mp (ND.andIntro ha hr) h2
noncomputable def transitivityAt {Γ : ND.Seq (V:=V)} (D : SF (V:=V) 1) (R : SF (V:=V) 2)
    (a b c : ST (V:=V) 0) (h : ND.Proof (T:=T) Γ (transitivity D R))
    (ha : ND.Proof (T:=T) Γ (unary D a)) (hab : ND.Proof (T:=T) Γ (binary R a b))
    (hbc : ND.Proof (T:=T) Γ (binary R b c)) : ND.Proof (T:=T) Γ (binary R a c) := by
  have h1 : ND.Proof (T:=T) Γ (∀¹ ∀¹ ((unary D a.bShift.bShift ⋏
      (binary R a.bShift.bShift (Semiterm.bvar 1) ⋏ binary R (Semiterm.bvar 1) (Semiterm.bvar 0))) 🡒
        binary R a.bShift.bShift (Semiterm.bvar 0))) := by simpa [transitivity,SemitermVec.q] using ND.allElim h a
  have h2 : ND.Proof (T:=T) Γ (∀¹ ((unary D a.bShift ⋏
      (binary R a.bShift b.bShift ⋏ binary R b.bShift (Semiterm.bvar 0))) 🡒 binary R a.bShift (Semiterm.bvar 0))) := by
    have hh := ND.allElim h1 b
    simp only [Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
      Bootstrapping.Semiformula.substs_and,binary_subst,unary_subst,Bootstrapping.Semiterm.bShift_substs_q,
      Bootstrapping.Semiterm.bShift_substs_sing,Bootstrapping.Semiterm.substs_bvar] at hh
    simpa [SemitermVec.q] using hh
  have h3 : ND.Proof (T:=T) Γ ((unary D a ⋏ (binary R a b ⋏ binary R b c)) 🡒 binary R a c) := by
    simpa using ND.allElim h2 c
  exact ND.mp (ND.andIntro ha (ND.andIntro hab hbc)) h3
noncomputable def equalityAtomIntro {Γ : ND.Seq (V:=V)} (A B : SF (V:=V) 1) (R : SF (V:=V) 2)
    (a b : ST (V:=V) 0) (ha : ND.Proof (T:=T) Γ (unary A a))
    (hb : ND.Proof (T:=T) Γ (unary B b)) (hr : ND.Proof (T:=T) Γ (binary R a b)) :
    ND.Proof (T:=T) Γ (equalityAtom A B R) := by
  apply ND.exsIntro _ a
  simp only [Bootstrapping.Semiformula.substs_ex, Bootstrapping.Semiformula.substs_and,unary_subst,binary_subst]
  apply ND.exsIntro _ b
  simpa [SemitermVec.q] using ND.andIntro ha (ND.andIntro hb hr)
#print axioms symmetry_shift
#print axioms transitivity_shift
#print axioms equalityAtom_shift
#print axioms equalityRemainder_shift
#print axioms symmetryAt
#print axioms transitivityAt
#print axioms equalityAtomIntro
end M6.PA.NumericPAeqFormulaEqualityTransport

