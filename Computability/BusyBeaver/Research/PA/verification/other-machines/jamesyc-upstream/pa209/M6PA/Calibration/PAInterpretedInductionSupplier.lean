module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedInductionContext
@[expose] public section

/-! Every finite source premise of guarded interpreted induction is supplied
by an actual numerical-basis derivation. Bounds are arithmetic inequalities;
the finite parameter-domain guard remains in the literal output formula. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

structure InterpretedInductionBudget (p : SourceFormula 1) (ρ : Nat → Term 0)
    (f : Nat → Nat) (lo z : Nat) : Prop where
  base : FunctionCongruenceBudgets f lo z
  room : lo+9 < z
  identitySep : lo+3+depth (∼identityProperty) ≤ z
  identityProof : lo+lkBudget identityDerivation ≤ z
  symmetrySep : lo+6+depth (∼inverseProperty 0 (1+1)) ≤ z
  adjunction : lo+5+lkBudget adjunctionDerivation ≤ z
  symmetryProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0) ≤ z
  transitivitySep : lo+8+depth (∼compositionProperty 1 0 (2+1+1)) ≤ z
  transitivityProof : lo+3+lkBudget (compositionTransitivityDerivation 2 1 0) ≤ z
  schemaSep : lo+3+depth (∼inductionPredicate p ρ) ≤ z

def interpretedInductionAxiomSupplier (p : SourceFormula 1) (ρ : Nat → Term 0)
    (f : Nat → Nat) (lo z : Nat) (B : InterpretedInductionBudget p ρ f lo z)
    (q : Form) (hq : q ∈ interpretedInductionAxioms p ρ) :
    NativeCalculus.ActualBasis.Proof (code q f lo z) := by
  classical
  by_cases h0 : q = separationFormula (∼inductionPredicate p ρ)
  · subst q; exact separationSupplier _ f lo z B.base.positive B.base.labels B.schemaSep
  by_cases h1 : q = Ordinal.intersectionFormula
  · subst q; exact Ordinal.intersectionAxiomSupplier f lo z B.base.positive (by have := B.room; omega)
  by_cases h2 : q = isoTransitivityClosed
  · subst q
    exact isoTransitivityClosedSupplier f lo z B.base.positive B.base.labels B.room
      B.transitivitySep B.adjunction B.transitivityProof
  have h : q ∈ interpretedAddSuccAxioms := by
    simpa [interpretedInductionAxioms,h0,h1,h2] using hq
  exact interpretedAddSuccAxiomSupplier f lo z B.base (by have := B.room; omega)
    B.identitySep B.identityProof B.symmetrySep (by have := B.adjunction; omega) B.symmetryProof q h

def interpretedInductionSupplier (p : SourceFormula 1) (ρ : Nat → Term 0)
    (f : Nat → Nat) (lo z : Nat) (B : InterpretedInductionBudget p ρ f lo z)
    (hbudget : lo+lkBudget (interpretedInductionDerivation p ρ) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (interpretedInductionGuarded p ρ) f lo z) :=
  compileContext (interpretedInductionAxioms p ρ) _ (interpretedInductionDerivation p ρ)
    f lo z B.base.positive B.base.labels hbudget
    (interpretedInductionAxiomSupplier p ρ f lo z B)

#print axioms interpretedInductionAxiomSupplier
#print axioms interpretedInductionSupplier
end M6.PA.ForwardRelational

