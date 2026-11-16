module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateBinaryEmptyRequested
@[expose] public section
namespace M6.PA.NumericPAeqFormulaLogical
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def bi (p q:SF (V:=V) 0):SF (V:=V) 0 := (p 🡒 q) ⋏ (q 🡒 p)
noncomputable def andDirection {T:InternalTheory V L} {Γ:ND.Seq (V:=V)}
    {p q r s:SF (V:=V) 0} (hp:ND.Proof (T:=T) Γ (p 🡒 q)) (hr:ND.Proof (T:=T) Γ (r 🡒 s)):
    ND.Proof (T:=T) Γ ((p ⋏ r) 🡒 (q ⋏ s)) := by
  apply ND.impIntro
  have h := ND.assumption (T:=T) (p ⋏ r) (by simp : ∼(p ⋏ r)∈insert (∼(p ⋏ r)) Γ)
  exact ND.andIntro (ND.mp (ND.andLeft h) (ND.up hp _)) (ND.mp (ND.andRight h) (ND.up hr _))
noncomputable def andBi (p q r s:SF (V:=V) 0):
    ND.Proof (T:=(∅:Theory L).internalize V) ∅
      ((bi p q ⋏ bi r s) 🡒 bi (p ⋏ r) (q ⋏ s)) := by
  apply ND.impIntro
  have h := ND.assumption (T:=(∅:Theory L).internalize V) (bi p q ⋏ bi r s)
    (by simp : ∼(bi p q ⋏ bi r s)∈insert (∼(bi p q ⋏ bi r s)) ∅)
  exact ND.andIntro (andDirection (ND.andLeft (ND.andLeft h)) (ND.andLeft (ND.andRight h)))
    (andDirection (ND.andRight (ND.andLeft h)) (ND.andRight (ND.andRight h)))
noncomputable def orLeft {T:InternalTheory V L} {Γ:ND.Seq (V:=V)} {p q:SF (V:=V) 0}
    (d:ND.Proof (T:=T) Γ p):ND.Proof (T:=T) Γ (p ⋎ q) :=
  TDerivation.or (d.wk (by intro x hx; simp at hx ⊢; tauto))
noncomputable def orRight {T:InternalTheory V L} {Γ:ND.Seq (V:=V)} {p q:SF (V:=V) 0}
    (d:ND.Proof (T:=T) Γ q):ND.Proof (T:=T) Γ (p ⋎ q) :=
  TDerivation.or (d.wk (by intro x hx; simp at hx ⊢; tauto))
noncomputable def orCases {T:InternalTheory V L} {Γ:ND.Seq (V:=V)} {p q r:SF (V:=V) 0}
    (d:ND.Proof (T:=T) Γ (p ⋎ q))
    (e:ND.Proof (T:=T) (insert (∼p) Γ) r) (f:ND.Proof (T:=T) (insert (∼q) Γ) r):
    ND.Proof (T:=T) Γ r := by
  apply TDerivation.cut (φ:=p ⋎ q)
  · exact d.wk (by intro x hx; simp at hx ⊢; tauto)
  · rw [LogicalConnective.DeMorgan.or]
    exact TDerivation.and (e.ofEq (by ext x; simp; tauto)) (f.ofEq (by ext x; simp; tauto))
noncomputable def orDirection {T:InternalTheory V L} {Γ:ND.Seq (V:=V)}
    {p q r s:SF (V:=V) 0} (hp:ND.Proof (T:=T) Γ (p 🡒 q)) (hr:ND.Proof (T:=T) Γ (r 🡒 s)):
    ND.Proof (T:=T) Γ ((p ⋎ r) 🡒 (q ⋎ s)) := by
  apply ND.impIntro
  have h := ND.assumption (T:=T) (p ⋎ r) (by simp : ∼(p ⋎ r)∈insert (∼(p ⋎ r)) Γ)
  apply orCases h
  · exact orLeft (ND.mp (ND.assumption p (by simp)) (ND.up (ND.up hp _) _))
  · exact orRight (ND.mp (ND.assumption r (by simp)) (ND.up (ND.up hr _) _))
noncomputable def orBi (p q r s:SF (V:=V) 0):
    ND.Proof (T:=(∅:Theory L).internalize V) ∅
      ((bi p q ⋏ bi r s) 🡒 bi (p ⋎ r) (q ⋎ s)) := by
  apply ND.impIntro
  have h := ND.assumption (T:=(∅:Theory L).internalize V) (bi p q ⋏ bi r s)
    (by simp : ∼(bi p q ⋏ bi r s)∈insert (∼(bi p q ⋏ bi r s)) ∅)
  exact ND.andIntro (orDirection (ND.andLeft (ND.andLeft h)) (ND.andLeft (ND.andRight h)))
    (orDirection (ND.andRight (ND.andLeft h)) (ND.andRight (ND.andRight h)))
#print axioms orBi
#print axioms andDirection
#print axioms andBi
end M6.PA.NumericPAeqFormulaLogical

