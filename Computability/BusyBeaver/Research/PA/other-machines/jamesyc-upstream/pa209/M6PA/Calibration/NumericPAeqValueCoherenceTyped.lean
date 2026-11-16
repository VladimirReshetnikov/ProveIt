module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateBinaryRewriting
public import M6PA.Calibration.NumericPAeqValueIsoCode
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def binary (R:SF (V:=V) 2) (x y:ST (V:=V) n) : SF (V:=V) n := R.subst ![x,y]
@[simp] theorem binary_shift (R:SF (V:=V) 2) (x y:ST (V:=V) n) :
    (binary R x y).shift=binary R.shift x.shift y.shift := by
  simp [binary,Bootstrapping.Semiformula.shift_substs,Matrix.comp_vecCons'']
@[simp] theorem binary_subst (R:SF (V:=V) 2) (x y:ST (V:=V) n) (w:Bootstrapping.SemitermVec V L n m) :
    (binary R x y).subst w=binary R (x.subst w) (y.subst w) := by
  simp [binary,Bootstrapping.Semiformula.substs_substs,Matrix.comp_vecCons'']
noncomputable def zeroPairwise (Z:SF (V:=V) 1) (R:SF (V:=V) 2) : SF (V:=V) 0 :=
  ∀¹ ∀¹ (unary Z (Semiterm.bvar 1) 🡒 unary Z (Semiterm.bvar 0) 🡒 binary R (Semiterm.bvar 1) (Semiterm.bvar 0))
noncomputable def zeroComparisonTyped (D Z:SF (V:=V) 1) (R:SF (V:=V) 2) : SF (V:=V) 0 :=
  ∀¹ ∀¹ (( (unary D (Semiterm.bvar 1) ⋏ unary Z (Semiterm.bvar 1)) ⋏
    (unary D (Semiterm.bvar 0) ⋏ unary Z (Semiterm.bvar 0))) 🡒 binary R (Semiterm.bvar 1) (Semiterm.bvar 0))
@[simp] theorem zeroPairwise_shift (Z:SF (V:=V) 1) (R:SF (V:=V) 2) :
    (zeroPairwise Z R).shift=zeroPairwise Z.shift R.shift := by simp [zeroPairwise]
variable {T : InternalTheory V L}
noncomputable def zeroAt {Γ:ND.Seq (V:=V)} (Z:SF (V:=V) 1) (R:SF (V:=V) 2) (x y:ST (V:=V) 0)
    (h:ND.Proof (T:=T) Γ (zeroPairwise Z R)) (hx:ND.Proof (T:=T) Γ (unary Z x))
    (hy:ND.Proof (T:=T) Γ (unary Z y)) : ND.Proof (T:=T) Γ (binary R x y) := by
  have first : ND.Proof (T:=T) Γ (∀¹ (unary Z x.bShift 🡒 unary Z (Semiterm.bvar 0) 🡒
      binary R x.bShift (Semiterm.bvar 0))) := by
    simpa [zeroPairwise,Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
      SemitermVec.q] using ND.allElim h x
  have he := ND.allElim first y
  have hh : ND.Proof (T:=T) Γ (unary Z x 🡒 unary Z y 🡒 binary R x y) := by
    simpa [zeroPairwise,Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
      SemitermVec.q] using he
  exact ND.mp hy (ND.mp hx hh)

noncomputable def zeroComparisonProof (D Z:SF (V:=V) 1) (R:SF (V:=V) 2) :
    ND.Proof (T:=T) (insert (∼zeroPairwise Z R) ∅) (zeroComparisonTyped D Z R) := by
  apply ND.allIntro
  simp only [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_all, Bootstrapping.Semiformula.substs_all]
  apply ND.allIntro
  simp only [zeroComparisonTyped,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_all,
    Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_and,
    Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
    Bootstrapping.Semiformula.substs_and,unary_shift,binary_shift,unary_subst,binary_subst]
  apply ND.impIntro
  let x : ST (V:=V) 0 := Semiterm.fvar 1
  let y : ST (V:=V) 0 := Semiterm.fvar 0
  let A := (unary D.shift.shift x ⋏ unary Z.shift.shift x) ⋏ (unary D.shift.shift y ⋏ unary Z.shift.shift y)
  let C : ND.Seq (V:=V) := insert (∼A) ((insert (∼zeroPairwise Z R) ∅ : ND.Seq (V:=V)).shift.shift)
  have hp : ND.Proof (T:=T) C A := ND.assumption _ (by simp [C])
  have hq : ND.Proof (T:=T) C (zeroPairwise Z.shift.shift R.shift.shift) := by
    apply ND.assumption
    simp [C]
  have result := zeroAt Z.shift.shift R.shift.shift x y hq
    (ND.andRight (ND.andLeft hp)) (ND.andRight (ND.andRight hp))
  simpa [C,A,x,y,SemitermVec.q] using result

#print axioms zeroComparisonProof
#print axioms binary_shift
#print axioms binary_subst
#print axioms zeroAt
end M6.PA.NumericPAeqValueCoherence

