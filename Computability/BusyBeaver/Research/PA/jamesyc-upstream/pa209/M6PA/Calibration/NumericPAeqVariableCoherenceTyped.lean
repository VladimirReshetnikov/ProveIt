module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceTyped
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def transportTyped (E R : SF (V:=V) 2) : SF (V:=V) 0 :=
  ∀¹ ∀¹ ∀¹ ∀¹ ((binary R (Semiterm.bvar 3) (Semiterm.bvar 2) ⋏
    (binary E (Semiterm.bvar 1) (Semiterm.bvar 3) ⋏ binary E (Semiterm.bvar 0) (Semiterm.bvar 2))) 🡒
      binary R (Semiterm.bvar 1) (Semiterm.bvar 0))
@[simp] theorem transportTyped_shift (E R : SF (V:=V) 2) :
    (transportTyped E R).shift=transportTyped E.shift R.shift := by simp [transportTyped]
noncomputable def variableComparisonTyped (D : SF (V:=V) 1) (E R : SF (V:=V) 2)
    (x y : ST (V:=V) 0) : SF (V:=V) 0 :=
  ∀¹ ∀¹ (((unary D (Semiterm.bvar 1) ⋏ binary E (Semiterm.bvar 1) x.bShift.bShift) ⋏
    (unary D (Semiterm.bvar 0) ⋏ binary E (Semiterm.bvar 0) y.bShift.bShift)) 🡒
      binary R (Semiterm.bvar 1) (Semiterm.bvar 0))
variable {T : InternalTheory V L}
noncomputable def transportAt {Γ : ND.Seq (V:=V)} (E R : SF (V:=V) 2) (a b r s : ST (V:=V) 0)
    (h : ND.Proof (T:=T) Γ (transportTyped E R))
    (hi : ND.Proof (T:=T) Γ (binary R a b))
    (hr : ND.Proof (T:=T) Γ (binary E r a)) (hs : ND.Proof (T:=T) Γ (binary E s b)) :
    ND.Proof (T:=T) Γ (binary R r s) := by
  have h1 : ND.Proof (T:=T) Γ (∀¹ ∀¹ ∀¹
      ((binary R a.bShift.bShift.bShift (Semiterm.bvar 2) ⋏
        (binary E (Semiterm.bvar 1) a.bShift.bShift.bShift ⋏ binary E (Semiterm.bvar 0) (Semiterm.bvar 2))) 🡒
          binary R (Semiterm.bvar 1) (Semiterm.bvar 0))) := by
    simpa [transportTyped,SemitermVec.q] using ND.allElim h a
  have h2 : ND.Proof (T:=T) Γ (∀¹ ∀¹
      ((binary R a.bShift.bShift b.bShift.bShift ⋏
        (binary E (Semiterm.bvar 1) a.bShift.bShift ⋏ binary E (Semiterm.bvar 0) b.bShift.bShift)) 🡒
          binary R (Semiterm.bvar 1) (Semiterm.bvar 0))) := by
    have hh := ND.allElim h1 b
    simp only [Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
      Bootstrapping.Semiformula.substs_and,binary_subst,Bootstrapping.Semiterm.bShift_substs_q,
      Bootstrapping.Semiterm.bShift_substs_sing,Bootstrapping.Semiterm.substs_bvar] at hh
    simpa [SemitermVec.q] using hh
  have h3 : ND.Proof (T:=T) Γ (∀¹
      ((binary R a.bShift b.bShift ⋏ (binary E r.bShift a.bShift ⋏ binary E (Semiterm.bvar 0) b.bShift)) 🡒
        binary R r.bShift (Semiterm.bvar 0))) := by
    have hh := ND.allElim h2 r
    simp only [Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
      Bootstrapping.Semiformula.substs_and,binary_subst,Bootstrapping.Semiterm.bShift_substs_q,
      Bootstrapping.Semiterm.bShift_substs_sing,Bootstrapping.Semiterm.substs_bvar] at hh
    simpa [SemitermVec.q] using hh
  have hh : ND.Proof (T:=T) Γ ((binary R a b ⋏ (binary E r a ⋏ binary E s b)) 🡒 binary R r s) := by
    simpa using ND.allElim h3 s
  exact ND.mp (ND.andIntro hi (ND.andIntro hr hs)) hh
#print axioms transportTyped_shift
#print axioms transportAt
end M6.PA.NumericPAeqValueCoherence
