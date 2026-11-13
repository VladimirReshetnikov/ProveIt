module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateBinaryOutput
@[expose] public section
namespace M6.PA.RelationalPredicateBinary
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
variable {T : InternalTheory V L}

noncomputable def rightWitness {Γ : ND.Seq (V:=V)}
    (D : SF (V:=V) 1) (R : SF (V:=V) 3) (P Q : SF (V:=V) 1) (x : ST (V:=V) 0)
    (hx : ND.Proof (T:=T) Γ (unary D x)) (hp : ND.Proof (T:=T) Γ (unary P x))
    (hq : ND.Proof (T:=T) Γ (witness D Q)) (ht : ND.Proof (T:=T) Γ (totality D R)) :
    ND.Proof (T:=T) Γ (result D R P Q) := by
  apply ND.exsElim (p:=D ⋏ Q) hq
  let C : ND.Seq (V:=V) := insert (∼(D ⋏ Q).free) Γ.shift
  have hpair : ND.Proof (T:=T) C
      (unary D.shift (Semiterm.fvar 0) ⋏ unary Q.shift (Semiterm.fvar 0)) := by
    simpa [unary,Bootstrapping.Semiformula.free] using
      ND.assumption (T:=T) (Γ:=C) (D ⋏ Q).free (by simp [C])
  have hx' : ND.Proof (T:=T) C (unary D.shift x.shift) := by simpa [C] using ND.up (ND.shift hx) (D ⋏ Q).free
  have hp' : ND.Proof (T:=T) C (unary P.shift x.shift) := by simpa [C] using ND.up (ND.shift hp) (D ⋏ Q).free
  have ht' : ND.Proof (T:=T) C (totality D.shift R.shift) := by simpa [C] using ND.up (ND.shift ht) (D ⋏ Q).free
  have ho := totalityAt D.shift R.shift x.shift (Semiterm.fvar 0) ht' hx' (ND.andLeft hpair)
  simpa using fromOutput D.shift R.shift P.shift Q.shift x.shift (Semiterm.fvar 0) hp' (ND.andRight hpair) ho

noncomputable def bothWitnesses {Γ : ND.Seq (V:=V)}
    (D : SF (V:=V) 1) (R : SF (V:=V) 3) (P Q : SF (V:=V) 1)
    (hp : ND.Proof (T:=T) Γ (witness D P)) (hq : ND.Proof (T:=T) Γ (witness D Q))
    (ht : ND.Proof (T:=T) Γ (totality D R)) : ND.Proof (T:=T) Γ (result D R P Q) := by
  apply ND.exsElim (p:=D ⋏ P) hp
  let C : ND.Seq (V:=V) := insert (∼(D ⋏ P).free) Γ.shift
  have hpair : ND.Proof (T:=T) C
      (unary D.shift (Semiterm.fvar 0) ⋏ unary P.shift (Semiterm.fvar 0)) := by
    simpa [unary,Bootstrapping.Semiformula.free] using
      ND.assumption (T:=T) (Γ:=C) (D ⋏ P).free (by simp [C])
  have hq' : ND.Proof (T:=T) C (witness D.shift Q.shift) := by simpa [C] using ND.up (ND.shift hq) (D ⋏ P).free
  have ht' : ND.Proof (T:=T) C (totality D.shift R.shift) := by simpa [C] using ND.up (ND.shift ht) (D ⋏ P).free
  simpa using rightWitness D.shift R.shift P.shift Q.shift (Semiterm.fvar 0)
    (ND.andLeft hpair) (ND.andRight hpair) hq' ht'

noncomputable def composition (D : SF (V:=V) 1) (R : SF (V:=V) 3) (P Q : SF (V:=V) 1) :
    ND.Proof (T:=T) (insert (∼totality D R) ∅) (statement D R P Q) := by
  apply ND.impIntro
  let C : ND.Seq (V:=V) := insert (∼(witness D P ⋏ witness D Q)) (insert (∼totality D R) ∅)
  have hpair : ND.Proof (T:=T) C (witness D P ⋏ witness D Q) := ND.assumption _ (by simp [C])
  have ht : ND.Proof (T:=T) C (totality D R) := ND.assumption _ (by simp [C])
  exact bothWitnesses D R P Q (ND.andLeft hpair) (ND.andRight hpair) ht

#print axioms rightWitness
#print axioms bothWitnesses
#print axioms composition
end M6.PA.RelationalPredicateBinary

