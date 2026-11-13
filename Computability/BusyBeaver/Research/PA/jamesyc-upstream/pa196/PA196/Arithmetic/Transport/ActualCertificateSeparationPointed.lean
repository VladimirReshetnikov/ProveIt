module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.CertificateInterface
public import PA196.Arithmetic.Transport.ActualCertificateEquivalenceRelation
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic


/-! Literal numerical pointed-existential extraction from the PA196 guarded gate.
All formulas and witnesses are arbitrary PA-model values, with the original
two bundle guards retained. -/
namespace PA196.Arithmetic.Transport.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open PA196.Arithmetic.Checker PA196.Arithmetic.HeadGraphs
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
  let raw : Certificate (oldGate a b c) := gateOld a b c ha hb
  have he : oldGate a b c=wn (wim m (wal c (wim s (wn p)))) := rfl
  let hn : Certificate (wn (wal c (wim s (wn p)))) :=
    (he ▸ raw).mp (negatedImplicationRight m _)
  let hforall := universalMap c (doubleNegationElimination (wim s (wn p)))
  exact hn.mp (contrapose hforall)

noncomputable def forallStrip (x a : V) (hv : Certificate (wim a (wal x a))) :
    Certificate (wim (wal x a) a) := by
  let h : Context [wal x a] (wal x a) := .assumption (by simp)
  let hi := h.forallMP x (.closed (.all x (Dominated.k a (weq 0 x))))
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
end PA196.Arithmetic.Transport.ActualCertificateEquivalence

