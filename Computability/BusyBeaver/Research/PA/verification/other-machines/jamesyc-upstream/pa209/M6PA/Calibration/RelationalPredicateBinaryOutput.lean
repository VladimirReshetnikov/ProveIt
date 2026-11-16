module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateBinaryPacking
@[expose] public section
namespace M6.PA.RelationalPredicateBinary
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
variable {T : InternalTheory V L}

noncomputable def fromOutput {Γ : ND.Seq (V:=V)}
    (D : SF (V:=V) 1) (R : SF (V:=V) 3) (P Q : SF (V:=V) 1) (x y : ST (V:=V) 0)
    (hp : ND.Proof (T:=T) Γ (unary P x)) (hq : ND.Proof (T:=T) Γ (unary Q y))
    (ho : ND.Proof (T:=T) Γ (outputAt D R x y)) : ND.Proof (T:=T) Γ (result D R P Q) := by
  let body : SF (V:=V) 1 := unary D (Semiterm.bvar 0) ⋏ ternary R x.bShift y.bShift (Semiterm.bvar 0)
  apply ND.exsElim (p:=body) ho
  let C : ND.Seq (V:=V) := insert (∼body.free) Γ.shift
  have hpair : ND.Proof (T:=T) C
      (unary D.shift (Semiterm.fvar 0) ⋏ ternary R.shift x.shift y.shift (Semiterm.fvar 0)) := by
    simpa [body] using ND.assumption (T:=T) (Γ:=C) body.free (by simp [C])
  have hp' : ND.Proof (T:=T) C (unary P.shift x.shift) := by
    simpa [C] using ND.up (ND.shift hp) body.free
  have hq' : ND.Proof (T:=T) C (unary Q.shift y.shift) := by
    simpa [C] using ND.up (ND.shift hq) body.free
  simpa using pack D.shift R.shift P.shift Q.shift x.shift y.shift (Semiterm.fvar 0)
    (ND.andLeft hpair) hp' hq' (ND.andRight hpair)

noncomputable def totalityAt {Γ : ND.Seq (V:=V)}
    (D : SF (V:=V) 1) (R : SF (V:=V) 3) (x y : ST (V:=V) 0)
    (ht : ND.Proof (T:=T) Γ (totality D R))
    (hx : ND.Proof (T:=T) Γ (unary D x)) (hy : ND.Proof (T:=T) Γ (unary D y)) :
    ND.Proof (T:=T) Γ (outputAt D R x y) := by
  have hxall : ND.Proof (T:=T) Γ
      (unary D x 🡒 ∀¹ (unary D (Semiterm.bvar 0) 🡒 outputAt D R x.bShift (Semiterm.bvar 0))) := by
    simpa [totality,SemitermVec.q] using ND.allElim ht x
  have hall := ND.mp hx hxall
  have hlast : ND.Proof (T:=T) Γ (unary D y 🡒 outputAt D R x y) := by
    simpa using ND.allElim hall y
  exact ND.mp hy hlast

#print axioms fromOutput
#print axioms totalityAt
end M6.PA.RelationalPredicateBinary

