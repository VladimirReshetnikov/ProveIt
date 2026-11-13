module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedSuccessorCancellation
public import M6PA.Calibration.PAInterpretedUniversal
public import M6PA.Calibration.PAPresentationAxioms
@[expose] public section

/-! Literal typed PAeq successor injectivity, using a paid closed strict-cut
Separation instance rather than extensionality or raw successor uniqueness. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

def interpretedSuccInjective {Γ : List Form} (E : FormulaEquality Γ)
    (hsep : ND.Proof Γ PairGraph.closedStrictSeparation) (f : Nat → Term 0) :
    ND.Proof Γ (formula Presentation.succInjective Fin.elim0 f) := by
  apply interpretedAllIntro
  apply interpretedAllIntro
  let d : Form := Ordinal.domain (.fvar 0)
  let C1 := d::shifted Γ
  let C2 := d::shifted C1
  let E1 : FormulaEquality C1 := E.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  let E2 : FormulaEquality C2 := E1.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have hs1 : ND.Proof C1 PairGraph.closedStrictSeparation := up (PairGraph.predecessorClosedSeparationShift hsep) d
  have hs2 : ND.Proof C2 PairGraph.closedStrictSeparation := up (PairGraph.predecessorClosedSeparationShift hs1) d
  let b1 : Fin 1 → Term 0 := Fin.cases (.fvar 0) (fun i : Fin 0 => Rew.shift (Fin.elim0 i))
  let b : Fin 2 → Term 0 := Fin.cases (.fvar 0) (fun i => Rew.shift (b1 i))
  let fs : Nat → Term 0 := fun i => Rew.shift (Rew.shift (f i))
  let p : Form := equal (Presentation.succ (.bvar 1)) (Presentation.succ (.bvar 0)) b fs
  have out : ND.Proof C2 (p 🡒 equal (.bvar 1) (.bvar 0) b fs) := by
    apply impIntro
    exact successorEqualityCancel (E2.weaken (fun q hq => List.mem_cons_of_mem p hq))
      (.bvar 1) (.bvar 0) b fs (up hs2 p) (assumption (by simp [p]))
  convert out using 1 <;>
    (dsimp [C1,C2,d,p,b,b1,fs] <;>
      (try simp only [formula_neg,formula,Presentation.implies,Presentation.eq]) <;> rfl)

def interpretedSuccInjectiveAxioms : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,PairGraph.closedStrictSeparation]

def interpretedSuccInjectiveDerivation (ρ : Nat → Term 0) :
    ND.Proof interpretedSuccInjectiveAxioms (formula Presentation.succInjective Fin.elim0 ρ) :=
  interpretedSuccInjective
    ⟨⟨assumption (by simp [interpretedSuccInjectiveAxioms]),assumption (by simp [interpretedSuccInjectiveAxioms]),
      assumption (by simp [interpretedSuccInjectiveAxioms])⟩,assumption (by simp [interpretedSuccInjectiveAxioms])⟩
    (assumption (by simp [interpretedSuccInjectiveAxioms])) ρ

def interpretedSuccInjectiveSupplier (ρ : Nat → Term 0) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0<lo) (hf : ∀i,f i<lo) (hz : lo+4<z)
    (hsep : lo+4+depth (PairGraph.strictEntryProperty (n := 0) (.fvar 0))≤z)
    (hbudget : lo+lkBudget (interpretedSuccInjectiveDerivation ρ)≤z) :
    NativeCalculus.ActualBasis.Proof (code (formula Presentation.succInjective Fin.elim0 ρ) f lo z) := by
  apply compileContext interpretedSuccInjectiveAxioms _ (interpretedSuccInjectiveDerivation ρ) f lo z hlo hf hbudget
  intro p hp
  classical
  by_cases h0 : p=reflexivityFormula
  · subst p; exact reflexivitySupplier f lo z
  by_cases h1 : p=symmetryFormula
  · subst p; exact symmetrySupplier f lo z
  by_cases h2 : p=transitivityFormula
  · subst p; exact transitivitySupplier f lo z
  by_cases h3 : p=congruenceFormula
  · subst p; exact congruenceSupplier f lo z (by omega)
  have he : p=PairGraph.closedStrictSeparation := by
    simpa [interpretedSuccInjectiveAxioms,h0,h1,h2,h3] using hp
  subst p
  exact closedSeparationSupplier _ f lo z hlo hf hsep

#print axioms interpretedSuccInjective
#print axioms interpretedSuccInjectiveDerivation
#print axioms interpretedSuccInjectiveSupplier
end M6.PA.ForwardRelational

