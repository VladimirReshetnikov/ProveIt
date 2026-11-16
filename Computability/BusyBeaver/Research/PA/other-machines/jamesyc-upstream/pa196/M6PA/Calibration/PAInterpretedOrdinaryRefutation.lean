module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedOrdinaryImageSupplier
@[expose] public section

/-! Fully supplied external annotated ordinary PAeq refutation compiler.
This consumes an actual typed derivation and explicit numerical allocation
budgets; it is not an internal transformation of Foundation proof numbers. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

def imageListSupplier (ws : List OrdinaryAxiomWitness)
    (f : Nat → Nat) (lo z : Nat)
    (h : ∀w,w∈ws→NativeCalculus.ActualBasis.Proof (code (ordinarySentenceImage w.sentence) f lo z))
    (q : Form) (hq : q∈ordinaryImageContext ws) :
    NativeCalculus.ActualBasis.Proof (code q f lo z) := by
  classical
  cases ws with
  | nil => simp [ordinaryImageContext] at hq
  | cons w ws =>
    by_cases he : q=ordinarySentenceImage w.sentence
    · subst q
      exact h w (by simp)
    · apply imageListSupplier ws f lo z (fun v hv => h v (by simp [hv])) q
      exact (List.mem_cons.mp hq).resolve_left he

def ordinaryRefutationSupplier
    (d : OrdinaryAnnotatedProof (Semiformula.falsum : Sentence Presentation.language))
    (f : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets f lo z) (C : AdditionCommutativityBudget f lo z)
    (hcomm : lo+lkBudget addCommutativityDerivation≤z)
    (hsymSep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hsymProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z)
    (H : ∀w,w∈d.witnesses→OrdinaryImageBudget w f lo z)
    (hbudget : lo+lkBudget (ordinaryFullRefutationDerivation d)≤z) :
    NativeCalculus.ActualBasis.Proof 1 := by
  apply compileContext (ordinaryImageContext d.witnesses++interpretedFixedAxioms) ⊥
    (ordinaryFullRefutationDerivation d) f lo z B.positive B.labels hbudget
  intro q hq
  classical
  by_cases he : q∈ordinaryImageContext d.witnesses
  · exact imageListSupplier d.witnesses f lo z
      (fun w hw => ordinaryImageSupplier w f lo z B C hcomm hsymSep hsymProof (H w hw)) q he
  · exact interpretedFixedAxiomSupplier f lo z B C hcomm hsymSep hsymProof q
      ((List.mem_append.mp hq).resolve_left he)

#print axioms ordinaryRefutationSupplier
end M6.PA.ForwardRelational

