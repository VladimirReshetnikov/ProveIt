module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationResultSupplier
public import M6PA.Calibration.RelationalParameterFresh
@[expose] public section

/-! The first free multiplier is closed only after its finite actual-basis
proof has been supplied. The two Separation budgets remain separate. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

def mulClosedResult : Form := closeParameter (mulTotalStatement 0)

def mulClosedResultSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+7 < z)
    (hmulSep : lo+4+depth (∼mulPrefixProperty 0) ≤ z)
    (haddSep : lo+4+depth (∼prefixProperty 0) ≤ z)
    (hadj : lo+3+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+1+lkBudget (mulTotalDerivation 0) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code mulClosedResult f lo z) := by
  apply closeParameterSupplier
  apply mulTotalSupplier 0 (shiftedLabels f lo) (lo+1) z (by omega)
  · intro i
    cases i with
    | zero => simp [shiftedLabels]
    | succ i => simpa [shiftedLabels] using Nat.lt_trans (hf i) (Nat.lt_succ_self lo)
  · omega
  · omega
  · omega
  · omega
  · omega

def mulClosedResultShift {Γ : List Form}
    (h : ND.Proof Γ mulClosedResult) : ND.Proof (shifted Γ) mulClosedResult := by
  convert shiftProof h using 1 <;>
    (simp only [mulClosedResult,closeParameter,mulTotalStatement,mulOutputConclusion,mulOutput]; mulCompactSyntax)

def mulResultOutputAt {Γ : List Form} (base x : Nat)
    (h : ND.Proof Γ (mulOutputConclusion base))
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x))) :
    ND.Proof Γ (mulOutput (.fvar x) (.fvar base)) := by
  have hh : ND.Proof Γ (sourceImply (Ordinal.domain (.fvar x)) (mulOutput (.fvar x) (.fvar base))) := by
    convert allElim _ (.fvar x) h using 1 <;>
      (simp only [mulOutputConclusion,mulOutput]; mulCompactSyntax)
  exact mp hx hh

def mulClosedResultAt {Γ : List Form} (x y : Nat)
    (h : ND.Proof Γ mulClosedResult)
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x)))
    (hy : ND.Proof Γ (Ordinal.domain (.fvar y))) :
    ND.Proof Γ (mulOutput (.fvar x) (.fvar y)) := by
  have hh := specializeParameter (mulTotalStatement 0) (.fvar y) h
  have hp : ND.Proof Γ (mulTotalStatement y) := by
    convert hh using 1 <;>
      (simp only [mulTotalStatement,mulOutputConclusion,mulOutput]; mulCompactSyntax)
  exact mulResultOutputAt y x (mp hy hp) hx

#print axioms mulClosedResultSupplier
#print axioms mulClosedResultShift
#print axioms mulResultOutputAt
#print axioms mulClosedResultAt
end M6.PA.RelationalSource.PairGraph

