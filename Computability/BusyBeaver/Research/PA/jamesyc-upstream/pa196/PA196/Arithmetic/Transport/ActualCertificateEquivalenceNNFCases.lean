module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.ActualCertificateEquivalenceRelation
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic


/-! Exact numeric certificate suppliers for the target shapes occurring in
Foundation NNF negation. No induction on nonstandard syntax is asserted here. -/
namespace PA196.Arithmetic.Transport.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open PA196.Arithmetic.Checker PA196.Arithmetic.HeadGraphs

universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def truthCertificate : Certificate (0:V) := by
  have he : wim (0:V) 0=0 := by
    simp [wim,implicationValue,implicationExpr,im,ActualArithmeticGraph.eval,
      SourceCantorInternal.pairValue]
  exact he ▸ identity (0:V)

noncomputable def trueNegation : BiWitness (1:V) (wn 0) := by
  let h : Context [wn (0:V)] (wn 0) := .assumption (by simp)
  exact ⟨explosion (wn 0),(Context.mp (.closed truthCertificate) h).deduction.empty⟩

noncomputable def falseNegation : BiWitness (0:V) (wn 1) :=
  ⟨.mp (identity (1:V)) (Dominated.k (wn 1) 0),
    .mp truthCertificate (Dominated.k 0 (wn 1))⟩

noncomputable def andNegation {a b na nb : V}
    (ha : BiWitness na (wn a)) (hb : BiWitness nb (wn b)) :
    BiWitness (wim (wn na) nb) (wn (wn (wim a (wn b)))) :=
  ((ha.neg.trans (BiWitness.doubleNegation a).symm).imp hb).trans
    (BiWitness.doubleNegation (wim a (wn b)))

noncomputable def orNegation {a b na nb : V}
    (ha : BiWitness na (wn a)) (hb : BiWitness nb (wn b)) :
    BiWitness (wn (wim na (wn nb))) (wn (wim (wn a) b)) :=
  (ha.imp (hb.neg.trans (BiWitness.doubleNegation b).symm)).neg

noncomputable def allNegation (v : V) {a na : V} (ha : BiWitness na (wn a)) :
    BiWitness (wn (wal v (wn na))) (wn (wal v a)) :=
  ((ha.neg.trans (BiWitness.doubleNegation a).symm).all v).neg

noncomputable def exsNegation (v : V) {a na : V} (ha : BiWitness na (wn a)) :
    BiWitness (wal v na) (wn (wn (wal v (wn a)))) :=
  (ha.all v).trans (BiWitness.doubleNegation (wal v (wn a)))

#print axioms truthCertificate
#print axioms trueNegation
#print axioms falseNegation
#print axioms andNegation
#print axioms orNegation
#print axioms allNegation
#print axioms exsNegation
end PA196.Arithmetic.Transport.ActualCertificateEquivalence

