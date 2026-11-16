module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryEmptyRequested
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqBottomDomain
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
variable {T:InternalTheory V L}
noncomputable def domainContradiction (D Z:SF (V:=V) 1):
    ND.Proof (T:=T) ∅ ((∀¹ (D 🡒 ⊥)) 🡒 ((∃¹ (D ⋏ Z)) 🡒 ⊥)) :=by
  apply ND.impIntro
  apply ND.impIntro
  let Γ:ND.Seq (V:=V):=insert (∼(∃¹ (D ⋏ Z))) (insert (∼(∀¹ (D 🡒 ⊥))) ∅)
  have he:ND.Proof (T:=T) Γ (∃¹ (D ⋏ Z)):=ND.assumption _ (by simp [Γ])
  have hu:ND.Proof (T:=T) Γ (∀¹ (D 🡒 ⊥)):=ND.assumption _ (by simp [Γ])
  apply ND.exsElim he
  let C:ND.Seq (V:=V):=insert (∼(D ⋏ Z).free) Γ.shift
  have hw:ND.Proof (T:=T) C (D.free ⋏ Z.free):=by
    simpa [Bootstrapping.Semiformula.free] using
      ND.assumption (T:=T) (Γ:=C) (D ⋏ Z).free (by simp [C])
  have hu':ND.Proof (T:=T) C (∀¹ (D.shift 🡒 ⊥)):=by
    simpa [C] using ND.up (ND.shift hu) (D ⋏ Z).free
  have ha:=ND.allElim hu' (Bootstrapping.Semiterm.fvar 0)
  have ha':ND.Proof (T:=T) C (D.free 🡒 ⊥):=by
    simpa [Bootstrapping.Semiformula.free] using ha
  simpa using ND.mp (ND.andLeft hw) ha'
#print axioms domainContradiction
end PA196.Arithmetic.Transport.NumericPAeqBottomDomain

