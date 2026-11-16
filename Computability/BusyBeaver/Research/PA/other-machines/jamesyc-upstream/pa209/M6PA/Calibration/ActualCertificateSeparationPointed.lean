module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateNeighborhoodSpecialization
public import M6PA.Calibration.ActualCertificateEquivalenceRelation
@[expose] public section

/-! Literal numerical pointed-existential extraction from actual bundle10.
All formulas and witnesses are arbitrary PA-model values, with the original
two bundle guards retained. -/
namespace M6.PA.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCheckerBlueprint ActualHeadGraphs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def negatedImplicationRight (a b : V) : Certificate (wim (wn (wim a b)) (wn b)) := by
  let hb : Context [b,wn (wim a b)] b := .assumption (by simp)
  let hn : Context [b,wn (wim a b)] (wn (wim a b)) := .assumption (by simp)
  exact (Context.mp (hb.lift a) hn).deduction.deduction.empty

noncomputable def pointedExistential (a b c : V) (ha : c≠a) (hb : c≠b) :
    Certificate (wex c (wa (wal b (wa (wim (wel a b) (wim c (wel c b)))
      (wim (wel c b) c))) (wim c (wel c b)))) := by
  let s := wal b (wa (wim (wel a b) (wim c (wel c b))) (wim (wel c b) c))
  let p := wim c (wel c b)
  let m := wim (wel a b) (wal c (wel a b))
  let raw : Certificate (ActualArithmeticGraph.eval bundleExpr a b c 0) :=
    ⟨leafCertificate 10 (pack3Value a b c),verify_bundle a b c ha hb⟩
  have he : ActualArithmeticGraph.eval bundleExpr a b c 0=wn (wim m (wal c (wim s (wn p)))) := by
    simp only [bundleExpr,memVacExpr,separationExpr,pointExpr,ActualArithmeticGraph.eval,
      neg,im,al,mem,conj,wn,wim,wel,wal,wa,implicationValue,universalValue,
      implicationExpr,universalExpr,Nat.cast_one,s,p,m]
  let hn : Certificate (wn (wal c (wim s (wn p)))) :=
    (he ▸ raw).mp (negatedImplicationRight m _)
  let hforall := universalMap c (doubleNegationElimination (wim s (wn p)))
  exact hn.mp (contrapose hforall)

noncomputable def forallStrip (x a : V) (hv : Certificate (wim a (wal x a))) :
    Certificate (wim (wal x a) a) := by
  let h : Context [wal x a] (wal x a) := .assumption (by simp)
  let hi := h.forallMP x (.closed (.all x (Dominated.k a (weq x 0))))
  exact (Context.existsElim x hv hi (.closed (r1 x 0))).deduction.empty

noncomputable def rawPointedValue (a b c p : V) : V :=
  wex c (wa (wal b (wa (wim (wel a b) (wim p (wel c b))) (wim (wel c b) p)))
    (wim p (wel c b)))

noncomputable def rawPointedCongruence (a b c : V) {p q : V} (h : BiWitness p q) :
    BiWitness (rawPointedValue a b c p) (rawPointedValue a b c q) := by
  let left := (BiWitness.refl (wel a b)).imp (h.imp (BiWitness.refl (wel c b)))
  let right := (BiWitness.refl (wel c b)).imp h
  let both := (left.imp right.neg).neg
  let frame := ((BiWitness.all b both).imp (h.imp (BiWitness.refl (wel c b))).neg).neg
  exact (BiWitness.all c frame.neg).neg

/-- The witness label equals q, while the property is p. A real equivalence
certificate is required; no arbitrary-property substitution is asserted. -/
noncomputable def pointedAtEquivalentCode (a b p q : V) (ha : q≠a) (hb : q≠b)
    (h : BiWitness p q) : Certificate (rawPointedValue a b q p) :=
  (pointedExistential a b q ha hb).mp (rawPointedCongruence a b q h).backward

#print axioms negatedImplicationRight
#print axioms pointedExistential
#print axioms forallStrip
#print axioms rawPointedCongruence
#print axioms pointedAtEquivalentCode
end M6.PA.ActualCertificateEquivalence

