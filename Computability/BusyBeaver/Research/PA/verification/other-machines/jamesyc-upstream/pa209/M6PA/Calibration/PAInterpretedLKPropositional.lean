module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedExistentialRule
public import M6PA.Calibration.PAPresentationND
@[expose] public section

/-! Constructive propositional sequent interpretation. The host environment
is explicitly domain-covered; this is not a coded internal proof transformer.
Quantifier and theory rules are separate. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def DomainEnvironment (C : List Form) (f : Nat → Term 0) :=
  ∀ i, ND.Proof C (Ordinal.domain (f i))

def DomainEnvironment.up {C : List Form} {f : Nat → Term 0}
    (H : DomainEnvironment C f) (q : Form) : DomainEnvironment (q::C) f :=
  fun i => ND.up (H i) q

/-- A real target LK/ND contradiction from the negations of the interpreted
source sequent. No semantic entailment or proof choice enters this interface. -/
def InterpretedRefutes (Γ : LK.Sequent Presentation.language) : Type :=
  ∀ (f : Nat → Term 0) {C : List Form}, SubstitutionPremises C → DomainEnvironment C f →
    (∀ p, p ∈ Γ → ND.Proof C (∼formula p Fin.elim0 f)) → ND.Proof C ⊥

def InterpretedRefutes.positive {Γ : LK.Sequent Presentation.language} {p : SourceFormula 0}
    (d : InterpretedRefutes (Γ+⦃p⦄)) (f : Nat → Term 0) {C : List Form}
    (A : SubstitutionPremises C) (H : DomainEnvironment C f)
    (h : ∀ q,q∈Γ→ND.Proof C (∼formula q Fin.elim0 f)) :
    ND.Proof C (formula p Fin.elim0 f) := by
  apply byContradiction
  let n := (formula p Fin.elim0 f).neg
  apply d f (A.up n) (H.up n)
  intro q hq
  by_cases he : q=p
  · subst q; exact assumption (by simp [n,Semiformula.neg_eq])
  · exact up (h q ((Multiset.mem_add.mp hq).resolve_right (by simpa using he))) n

def interpretedRefutesIdentity {k : Nat} (r : Presentation.language.Rel k)
    (ts : Fin k → SourceTerm 0) :
    InterpretedRefutes ⦃Semiformula.rel r ts,Semiformula.nrel r ts⦄ := by
  intro f C A H h
  cases r
  have hp := h (Semiformula.rel .eq ts) (by simp)
  have hn := h (Semiformula.nrel .eq ts) (by simp)
  exact contradiction (by simpa only [formula,Semiformula.neg_eq,Semiformula.neg_neg] using hn) hp

def interpretedRefutesVerum : InterpretedRefutes ⦃(⊤ : SourceFormula 0)⦄ := by
  intro f C A H h
  exact h ⊤ (by simp)

def interpretedRefutesCut {Γ Δ : LK.Sequent Presentation.language} {p : SourceFormula 0}
    (d : InterpretedRefutes (Γ+⦃p⦄)) (e : InterpretedRefutes (Δ+⦃∼p⦄)) :
    InterpretedRefutes (Γ+Δ) := by
  intro f C A H h
  have hp := d.positive f A H (fun q hq => h q (Multiset.mem_add.mpr (Or.inl hq)))
  apply e f A H
  intro q hq
  by_cases he : q=∼p
  · subst q; simpa only [Semiformula.neg_eq,formula_neg,Semiformula.neg_neg] using hp
  · exact h q (Multiset.mem_add.mpr (Or.inr
      ((Multiset.mem_add.mp hq).resolve_right (by simpa using he))))

def interpretedRefutesWeakening {Γ : LK.Sequent Presentation.language} {p : SourceFormula 0}
    (d : InterpretedRefutes Γ) : InterpretedRefutes (Γ+⦃p⦄) :=
  fun f _ A H h => d f A H (fun q hq => h q (Multiset.mem_add.mpr (Or.inl hq)))

def interpretedRefutesContraction {Γ : LK.Sequent Presentation.language} {p : SourceFormula 0}
    (d : InterpretedRefutes (Γ+⦃p,p⦄)) : InterpretedRefutes (Γ+⦃p⦄) :=
  fun f _ A H h => d f A H (fun q hq => h q (by simpa using hq))

#print axioms interpretedRefutesIdentity
#print axioms interpretedRefutesVerum
#print axioms interpretedRefutesCut
#print axioms interpretedRefutesContraction
end M6.PA.ForwardRelational
