module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalCodeLanguage
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Typed
@[expose] public section

/-! Thin contextual operations on Foundation's existing model-valued typed
LK derivations. Contexts are actual finite HFS sequents of negative assumptions.
This introduces no syntax, proof datatype, or semantic-validity oracle. -/
namespace M6.PA.RelationalPredicateBinary.ND
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
abbrev Form := Bootstrapping.Formula V L
abbrev SForm (n : Nat) := Bootstrapping.Semiformula V L n
abbrev Seq := Bootstrapping.Sequent V L
abbrev Term := Bootstrapping.Term V L
variable {T : InternalTheory V L}
abbrev Proof (Γ : Seq (V:=V)) (p : Form (V:=V)) := T ⊢!ᵈᵉʳ insert p Γ

noncomputable def assumption {Γ : Seq (V:=V)} (p : Form (V:=V)) (h : ∼p∈Γ) : Proof (T:=T) Γ p :=
  TDerivation.em p (by simp) (by simp [h])
noncomputable def weaken {Γ Δ : Seq (V:=V)} {p : Form (V:=V)}
    (d : Proof (T:=T) Γ p) (h : Γ⊆Δ) : Proof (T:=T) Δ p :=
  d.wk (insert_subset_insert_of_subset _ h)
noncomputable def up {Γ : Seq (V:=V)} {p : Form (V:=V)}
    (d : Proof (T:=T) Γ p) (a : Form (V:=V)) : Proof (T:=T) (insert (∼a) Γ) p :=
  weaken d (by intro x hx; simp [hx])
noncomputable def impIntro {Γ : Seq (V:=V)} {p q : Form (V:=V)}
    (d : Proof (T:=T) (insert (∼p) Γ) q) : Proof (T:=T) Γ (p 🡒 q) := by
  rw [Bootstrapping.Semiformula.imp_def]
  exact TDerivation.or (d.ofEq (by ext x; simp; tauto))
noncomputable def mp {Γ : Seq (V:=V)} {p q : Form (V:=V)}
    (d : Proof (T:=T) Γ p) (e : Proof (T:=T) Γ (p 🡒 q)) : Proof (T:=T) Γ q :=
  TDerivation.modusPonens e d
noncomputable def andIntro {Γ : Seq (V:=V)} {p q : Form (V:=V)}
    (d : Proof (T:=T) Γ p) (e : Proof (T:=T) Γ q) : Proof (T:=T) Γ (p ⋏ q) := TDerivation.and d e
noncomputable def andLeft {Γ : Seq (V:=V)} {p q : Form (V:=V)}
    (d : Proof (T:=T) Γ (p ⋏ q)) : Proof (T:=T) Γ p := by
  apply TDerivation.cut (φ:=p ⋏ q)
  · exact d.wk (by intro x hx; simp at hx ⊢; tauto)
  · rw [LogicalConnective.DeMorgan.and]
    apply TDerivation.or
    exact TDerivation.em p
noncomputable def andRight {Γ : Seq (V:=V)} {p q : Form (V:=V)}
    (d : Proof (T:=T) Γ (p ⋏ q)) : Proof (T:=T) Γ q := by
  apply TDerivation.cut (φ:=p ⋏ q)
  · exact d.wk (by intro x hx; simp at hx ⊢; tauto)
  · rw [LogicalConnective.DeMorgan.and]
    apply TDerivation.or
    exact TDerivation.em q
noncomputable def shift {Γ : Seq (V:=V)} {p : Form (V:=V)}
    (d : Proof (T:=T) Γ p) : Proof (T:=T) Γ.shift p.shift := by
  simpa using d.shift
noncomputable def allIntro {Γ : Seq (V:=V)} {p : SForm (V:=V) 1}
    (d : Proof (T:=T) Γ.shift p.free) : Proof (T:=T) Γ (∀¹ p) := TDerivation.all d
noncomputable def allElim {Γ : Seq (V:=V)} {p : SForm (V:=V) 1}
    (d : Proof (T:=T) Γ (∀¹ p)) (t : Term (V:=V)) : Proof (T:=T) Γ (p.subst ![t]) :=
  TDerivation.specialize d t
noncomputable def exsIntro {Γ : Seq (V:=V)} (p : SForm (V:=V) 1) (t : Term (V:=V))
    (d : Proof (T:=T) Γ (p.subst ![t])) : Proof (T:=T) Γ (∃¹ p) := TDerivation.exs t d
noncomputable def exsElim {Γ : Seq (V:=V)} {p : SForm (V:=V) 1} {q : Form (V:=V)}
    (d : Proof (T:=T) Γ (∃¹ p))
    (e : Proof (T:=T) (insert (∼p.free) Γ.shift) q.shift) : Proof (T:=T) Γ q := by
  apply TDerivation.cut (φ:=∃¹ p)
  · exact d.wk (by intro x hx; simp at hx ⊢; tauto)
  · rw [Bootstrapping.Semiformula.neg_ex]
    apply TDerivation.all
    exact e.ofEq (by ext x; simp [Bootstrapping.Semiformula.free]; tauto)

#print axioms impIntro
#print axioms andLeft
#print axioms allElim
#print axioms exsElim
end M6.PA.RelationalPredicateBinary.ND

