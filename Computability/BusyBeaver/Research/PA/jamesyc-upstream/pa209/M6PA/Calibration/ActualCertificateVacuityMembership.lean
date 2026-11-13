module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateEquivalenceLogic
@[expose] public section

/-! Actual V1 numeric membership-vacuity certificates over arbitrary PA models.
The only atomic guards are the literal bundle's two label inequalities. -/
namespace M6.PA.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCheckerBlueprint ActualHeadGraphs
universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable abbrev wel (a b : V) : V := wim a b + 1

noncomputable def negatedImplicationLeft (a b : V) : Certificate (wim (wn (wim a b)) a) := by
  let hp : Context [a,wn a,wn (wim a b)] a := .assumption (by simp)
  let hn : Context [a,wn a,wn (wim a b)] (wn a) := .assumption (by simp)
  let hab : Context [wn a,wn (wim a b)] (wim a b) :=
    ((Context.mp hp hn).explosion b).deduction
  let hnot : Context [wn a,wn (wim a b)] (wn (wim a b)) := .assumption (by simp)
  exact (Context.mp hab hnot).deduction.dne.deduction.empty

noncomputable def membershipVacuity (a b c : V) (ha : c ≠ a) (hb : c ≠ b) :
    Certificate (wim (wel a b) (wal c (wel a b))) := by
  let raw : Certificate (ActualArithmeticGraph.eval bundleExpr a b c 0) :=
    ⟨leafCertificate 10 (pack3Value a b c),verify_bundle a b c ha hb⟩
  have hraw : ActualArithmeticGraph.eval bundleExpr a b c 0 =
      wn (wim (wim (wel a b) (wal c (wel a b)))
        (ActualArithmeticGraph.eval (al .c (im separationExpr (neg pointExpr))) a b c 0)) := by
    simp only [bundleExpr,memVacExpr,ActualArithmeticGraph.eval,neg,im,al,mem,
      wn,wim,wel,wal,implicationValue,universalValue,implicationExpr,universalExpr,Nat.cast_one]
  exact (hraw ▸ raw).mp (negatedImplicationLeft _ _)

#print axioms negatedImplicationLeft
#print axioms membershipVacuity
end M6.PA.ActualCertificateEquivalence

