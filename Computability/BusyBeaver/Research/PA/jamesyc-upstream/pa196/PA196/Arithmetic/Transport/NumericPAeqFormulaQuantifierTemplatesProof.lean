module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaQuantifierTemplatesSyntax
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqFormulaQuantifierTemplates
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqFormulaLogical
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
variable {T:InternalTheory V L}
noncomputable def uniformAt {Γ:ND.Seq (V:=V)} (H:SF (V:=V) 0) (D P Q:SF (V:=V) 1)
    (t:ST (V:=V) 0) (h:ND.Proof (T:=T) Γ (uniformPremise H D P Q))
    (hh:ND.Proof (T:=T) Γ H) (hd:ND.Proof (T:=T) Γ (D.subst ![t])) :
    ND.Proof (T:=T) Γ (bi (P.subst ![t]) (Q.subst ![t])) := by
  have ht := ND.allElim h t
  simp only [uniformPremise,Bootstrapping.Semiformula.substs_imp,Bootstrapping.Semiformula.substs_and,liftClosed_subst] at ht
  exact ND.mp hd (ND.mp hh ht)
noncomputable def allDirection {Γ:ND.Seq (V:=V)} (H:SF (V:=V) 0) (D P Q:SF (V:=V) 1)
    (h:ND.Proof (T:=T) Γ (uniformPremise H D P Q)) (hh:ND.Proof (T:=T) Γ H)
    (hp:ND.Proof (T:=T) Γ (guardedAll D P)) : ND.Proof (T:=T) Γ (guardedAll D Q) := by
  apply ND.allIntro
  simp only [guardedAll,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.substs_imp]
  apply ND.impIntro
  let t:ST (V:=V) 0 := Semiterm.fvar 0
  let C:ND.Seq (V:=V) := insert (∼D.free) Γ.shift
  have hd:ND.Proof (T:=T) C D.free := ND.assumption _ (by simp [C])
  have hbi := uniformAt H.shift D.shift P.shift Q.shift t
    (ND.up (by simpa using ND.shift h) _) (ND.up (ND.shift hh) _) hd
  have hp' : ND.Proof (T:=T) C (D.free 🡒 P.free) := by
    simpa [C,guardedAll,Bootstrapping.Semiformula.free,t] using ND.up (ND.allElim (show ND.Proof (T:=T) Γ.shift (∀¹ (D.shift 🡒 P.shift)) from by simpa [guardedAll] using ND.shift hp) t) D.free
  exact ND.mp (ND.mp hd hp') (ND.andLeft hbi)
noncomputable def exsDirection {Γ:ND.Seq (V:=V)} (H:SF (V:=V) 0) (D P Q:SF (V:=V) 1)
    (h:ND.Proof (T:=T) Γ (uniformPremise H D P Q)) (hh:ND.Proof (T:=T) Γ H)
    (hp:ND.Proof (T:=T) Γ (guardedExs D P)) : ND.Proof (T:=T) Γ (guardedExs D Q) := by
  apply ND.exsElim hp
  let C:ND.Seq (V:=V) := insert (∼(D ⋏ P).free) Γ.shift
  let t:ST (V:=V) 0 := Semiterm.fvar 0
  have hd:ND.Proof (T:=T) C (D.free ⋏ P.free) := by
    simpa [Bootstrapping.Semiformula.free] using ND.assumption (T:=T) (D ⋏ P).free (by simp [C])
  have hbi := uniformAt H.shift D.shift P.shift Q.shift t
    (ND.up (by simpa using ND.shift h) _) (ND.up (ND.shift hh) _) (ND.andLeft hd)
  have hq := ND.mp (ND.andRight hd) (ND.andLeft hbi)
  have out : ND.Proof (T:=T) C (∃¹ (D.shift ⋏ Q.shift)) := ND.exsIntro (D.shift ⋏ Q.shift) t (by simpa [Bootstrapping.Semiformula.free,t] using ND.andIntro (ND.andLeft hd) hq)
  simpa [guardedExs,C] using out
noncomputable def uniformSwap {Γ:ND.Seq (V:=V)} (H:SF (V:=V) 0) (D P Q:SF (V:=V) 1)
    (h:ND.Proof (T:=T) Γ (uniformPremise H D P Q)) :
    ND.Proof (T:=T) Γ (uniformPremise H D Q P) := by
  apply ND.allIntro
  simp only [uniformPremise,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_and,
    Bootstrapping.Semiformula.substs_imp,Bootstrapping.Semiformula.substs_and,liftClosed_shift,liftClosed_subst]
  apply ND.impIntro
  apply ND.impIntro
  let C:ND.Seq (V:=V) := insert (∼D.free) (insert (∼H.shift) Γ.shift)
  have hd:ND.Proof (T:=T) C D.free := ND.assumption _ (by simp [C])
  have hh:ND.Proof (T:=T) C H.shift := ND.assumption _ (by simp [C])
  have hbi := uniformAt H.shift D.shift P.shift Q.shift (Semiterm.fvar 0)
    (ND.up (ND.up (by simpa using ND.shift h) _) _) hh hd
  exact ND.andIntro (ND.andRight hbi) (ND.andLeft hbi)
noncomputable def allTemplate (H:SF (V:=V) 0) (D P Q:SF (V:=V) 1) :
    ND.Proof (T:=T) ∅ (uniformPremise H D P Q 🡒 (H 🡒 bi (guardedAll D P) (guardedAll D Q))) := by
  apply ND.impIntro
  apply ND.impIntro
  let C:ND.Seq (V:=V) := insert (∼H) (insert (∼uniformPremise H D P Q) ∅)
  have h:ND.Proof (T:=T) C (uniformPremise H D P Q) := ND.assumption _ (by simp [C])
  have hh:ND.Proof (T:=T) C H := ND.assumption _ (by simp [C])
  apply ND.andIntro
  · apply ND.impIntro
    exact allDirection H D P Q (ND.up h _) (ND.up hh _) (ND.assumption _ (by simp))
  · apply ND.impIntro
    exact allDirection H D Q P (ND.up (uniformSwap H D P Q h) _) (ND.up hh _) (ND.assumption _ (by simp))
noncomputable def exsTemplate (H:SF (V:=V) 0) (D P Q:SF (V:=V) 1) :
    ND.Proof (T:=T) ∅ (uniformPremise H D P Q 🡒 (H 🡒 bi (guardedExs D P) (guardedExs D Q))) := by
  apply ND.impIntro
  apply ND.impIntro
  let C:ND.Seq (V:=V) := insert (∼H) (insert (∼uniformPremise H D P Q) ∅)
  have h:ND.Proof (T:=T) C (uniformPremise H D P Q) := ND.assumption _ (by simp [C])
  have hh:ND.Proof (T:=T) C H := ND.assumption _ (by simp [C])
  apply ND.andIntro
  · apply ND.impIntro
    exact exsDirection H D P Q (ND.up h _) (ND.up hh _) (ND.assumption _ (by simp))
  · apply ND.impIntro
    exact exsDirection H D Q P (ND.up (uniformSwap H D P Q h) _) (ND.up hh _) (ND.assumption _ (by simp))
#print axioms uniformAt
#print axioms allDirection
#print axioms exsDirection
#print axioms uniformSwap
#print axioms allTemplate
#print axioms exsTemplate
end PA196.Arithmetic.Transport.NumericPAeqFormulaQuantifierTemplates

