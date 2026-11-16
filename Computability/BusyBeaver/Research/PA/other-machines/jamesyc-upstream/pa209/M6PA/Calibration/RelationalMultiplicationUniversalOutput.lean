module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationClosedResult
@[expose] public section

/-! Exact input-first universal ordinal-valued multiplication-result totality. The premise
is a closed, actually supplied theorem, not an open ND parameter context. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

def mulResultTotalProperty (x : Ordinal.Term n) : Ordinal.Formula n :=
  ∀¹ sourceImply (Ordinal.domain (.bvar 0)) (mulOutput (Rew.bShift x) (.bvar 0))

def mulUniversalOutput : Form :=
  ∀¹ sourceImply (Ordinal.domain (.bvar 0)) (mulResultTotalProperty (.bvar 0))

def mulUniversalOutputFromClosed {Γ : List Form}
    (h : ND.Proof Γ mulClosedResult) : ND.Proof Γ mulUniversalOutput := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0)
  have hx : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have hc := up (mulClosedResultShift h) d
  have result : ND.Proof (d :: shifted Γ) (mulResultTotalProperty (.fvar 0)) := by
    apply allIntro
    have hxx := domainShift 0 hx
    have hcc := mulClosedResultShift hc
    let e : Form := Ordinal.domain (.fvar 0)
    have hy : ND.Proof (e :: shifted (d :: shifted Γ)) e := assumption (by simp)
    have inner := impIntro (mulClosedResultAt 1 0 (up hcc e) (up hxx e) hy)
    convert inner using 1 <;> (dsimp [e]; (try simp only [mulResultTotalProperty,mulOutput]); mulCompactSyntax)
  have out := impIntro result
  convert out using 1 <;> (dsimp [d]; (try simp only [mulResultTotalProperty,mulOutput]); mulCompactSyntax)

def mulUniversalOutputDerivation : ND.Proof [mulClosedResult] mulUniversalOutput :=
  mulUniversalOutputFromClosed (assumption (by simp))

def mulUniversalOutputSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+7 < z)
    (hmulSep : lo+4+depth (∼mulPrefixProperty 0) ≤ z)
    (haddSep : lo+4+depth (∼prefixProperty 0) ≤ z)
    (hadj : lo+3+lkBudget adjunctionDerivation ≤ z)
    (hresultBudget : lo+1+lkBudget (mulTotalDerivation 0) ≤ z)
    (hbudget : lo+lkBudget mulUniversalOutputDerivation ≤ z) :
    NativeCalculus.ActualBasis.Proof (code mulUniversalOutput f lo z) := by
  apply compileContext [mulClosedResult] _ mulUniversalOutputDerivation f lo z hlo hf hbudget
  intro p hp
  have he : p = mulClosedResult := by simpa using hp
  subst p
  exact mulClosedResultSupplier f lo z hlo hf hz hmulSep haddSep hadj hresultBudget

#print axioms mulUniversalOutputFromClosed
#print axioms mulUniversalOutputDerivation
#print axioms mulUniversalOutputSupplier
end M6.PA.RelationalSource.PairGraph

