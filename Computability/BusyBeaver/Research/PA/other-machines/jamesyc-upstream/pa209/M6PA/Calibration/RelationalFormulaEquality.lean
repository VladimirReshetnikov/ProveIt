module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrdinalSuccessorClosureLinear
@[expose] public section

/-! Literal ordinary equality proof data for generic relational substitution.
No new theory or extensionality axiom is introduced. -/
namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder ND
abbrev GroundTerm := Semiterm language Nat 0

structure FormulaEquality (Γ : List ND.Form) where
  core : Ordinal.EqualityProofs Γ
  transitive : ND.Proof Γ transitivityFormula

def FormulaEquality.weaken {Γ Δ} (E : FormulaEquality Γ)
    (inc : ∀ p, p ∈ Γ → p ∈ Δ) : FormulaEquality Δ where
  core := ⟨ND.weaken E.core.reflexive inc, ND.weaken E.core.symmetric inc, ND.weaken E.core.congruent inc⟩
  transitive := ND.weaken E.transitive inc

def FormulaEquality.shifted {Γ} (E : FormulaEquality Γ) : FormulaEquality (ND.shifted Γ) where
  core := E.core.shift
  transitive := Ordinal.equalityTransShift E.transitive

def FormulaEquality.reflexive {Γ} (E : FormulaEquality Γ) (a : GroundTerm) : ND.Proof Γ (eq a a) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar i => exact Ordinal.eqRefl E.core i

def FormulaEquality.symmetryOf {Γ} (E : FormulaEquality Γ) {a b : GroundTerm}
    (h : ND.Proof Γ (eq a b)) : ND.Proof Γ (eq b a) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar i =>
    cases b with
    | bvar j => nomatch j
    | func f _ => nomatch f
    | fvar j => exact Ordinal.eqSymm E.core i j h

def FormulaEquality.transitivityOf {Γ} (E : FormulaEquality Γ) {a b c : GroundTerm}
    (hab : ND.Proof Γ (eq a b)) (hbc : ND.Proof Γ (eq b c)) : ND.Proof Γ (eq a c) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar i =>
    cases b with
    | bvar j => nomatch j
    | func f _ => nomatch f
    | fvar j =>
      cases c with
      | bvar k => nomatch k
      | func f _ => nomatch f
      | fvar k => exact Ordinal.eqTrans E.transitive i j k hab hbc

def FormulaEquality.atomTransport {Γ} (E : FormulaEquality Γ) {a b c d : GroundTerm}
    (hab : ND.Proof Γ (eq a b)) (hcd : ND.Proof Γ (eq c d))
    (hac : ND.Proof Γ (eq a c)) : ND.Proof Γ (eq b d) :=
  E.transitivityOf (E.transitivityOf (E.symmetryOf hab) hac) hcd

def FormulaEquality.memberTransport {Γ} (E : FormulaEquality Γ) {a b c d : GroundTerm}
    (hab : ND.Proof Γ (eq a b)) (hcd : ND.Proof Γ (eq c d))
    (hac : ND.Proof Γ (mem a c)) : ND.Proof Γ (mem b d) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar i =>
    cases b with
    | bvar j => nomatch j
    | func f _ => nomatch f
    | fvar j =>
      cases c with
      | bvar k => nomatch k
      | func f _ => nomatch f
      | fvar k =>
        cases d with
        | bvar l => nomatch l
        | func f _ => nomatch f
        | fvar l => exact Ordinal.memCongr E.core i j k l hab hcd hac

def FormulaEquality.termCongruence {Γ} {n : Nat} (_E : FormulaEquality Γ)
    (ω τ : Rew language Nat n Nat 0)
    (hb : ∀ i : Fin n, ND.Proof Γ (eq (ω (.bvar i)) (τ (.bvar i))))
    (hf : ∀ i : Nat, ND.Proof Γ (eq (ω (.fvar i)) (τ (.fvar i))))
    (t : Semiterm language Nat n) : ND.Proof Γ (eq (ω t) (τ t)) :=
  match t with
  | .bvar i => hb i
  | .fvar i => hf i
  | .func f _ => nomatch f

#print axioms FormulaEquality.atomTransport
#print axioms FormulaEquality.memberTransport
end M6.PA.RelationalSource

