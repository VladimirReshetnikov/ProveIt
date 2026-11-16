module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateEquivalenceLogic
@[expose] public section

/-! Exact first-order paired-certificate relation and finite congruence recipes.
The existential relation is not a claimed graph of a unique proof recipe. -/
namespace M6.PA.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCheckerBlueprint ActualHeadGraphs

universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def BiCertificates (c d a b : V) : Prop :=
  verifyValue c=wim a b+1 ∧ verifyValue d=wim b a+1

attribute [local irreducible] ActualArithmeticGraph.graph
noncomputable def biGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “c d a b. ∃ ab ba, !(ActualArithmeticGraph.graph implicationExpr) ab a b 0 0 ∧
    !(ActualArithmeticGraph.graph implicationExpr) ba b a 0 0 ∧
    !verifyGraph (ab+1) c ∧ !verifyGraph (ba+1) d”

theorem bi_graph (c d a b : V) :
    biGraph.val.Evalb ![c,d,a,b] ↔ BiCertificates c d a b := by
  simp [biGraph,BiCertificates,wim,implicationValue,ActualArithmeticGraph.graph_correct,
    verify_graph,Matrix.comp_vecCons'',eq_comm]

structure BiWitness (a b : V) where
  forward : Certificate (wim a b)
  backward : Certificate (wim b a)

theorem BiWitness.accepted {a b : V} (h : BiWitness a b) :
    BiCertificates h.forward.code h.backward.code a b := ⟨h.forward.accepted,h.backward.accepted⟩

theorem BiWitness.witnesses {a b : V} (h : BiWitness a b) :
    ∃ c d, biGraph.val.Evalb ![c,d,a,b] :=
  ⟨h.forward.code,h.backward.code,(bi_graph _ _ _ _).mpr h.accepted⟩

variable [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def doubleNegationIntroduction (a : V) : Certificate (wim a (wn (wn a))) := by
  let p : Context [wn a,a] a := .assumption (by simp)
  let q : Context [wn a,a] (wn a) := .assumption (by simp)
  exact (Context.mp p q).deduction.deduction.empty

noncomputable def implicationMap {a a' b b' : V}
    (p : Certificate (wim a' a)) (q : Certificate (wim b b')) :
    Certificate (wim (wim a b) (wim a' b')) := by
  let x : Context [a',wim a b] a' := .assumption (by simp)
  let h : Context [a',wim a b] (wim a b) := .assumption (by simp)
  exact (Context.mp (.mp (.mp x (.closed p)) h) (.closed q)).deduction.deduction.empty

/-- GEN is applied only to an accepted closed certificate, never under a
hypothesis context. Thus this congruence needs no freshness side condition. -/
noncomputable def universalMap (v : V) {a b : V} (p : Certificate (wim a b)) :
    Certificate (wim (wal v a) (wal v b)) := .mp (.all v p) (r2 v a b)

noncomputable def BiWitness.refl (a : V) : BiWitness a a := ⟨identity a,identity a⟩
noncomputable def BiWitness.symm {a b : V} (h : BiWitness a b) : BiWitness b a :=
  ⟨h.backward,h.forward⟩
noncomputable def BiWitness.trans {a b c : V} (p : BiWitness a b) (q : BiWitness b c) :
    BiWitness a c := ⟨implicationCompose p.forward q.forward,implicationCompose q.backward p.backward⟩
noncomputable def BiWitness.neg {a b : V} (h : BiWitness a b) : BiWitness (wn a) (wn b) :=
  ⟨contrapose h.backward,contrapose h.forward⟩
noncomputable def BiWitness.imp {a a' b b' : V} (p : BiWitness a a') (q : BiWitness b b') :
    BiWitness (wim a b) (wim a' b') :=
  ⟨implicationMap p.backward q.forward,implicationMap p.forward q.backward⟩
noncomputable def BiWitness.all (v : V) {a b : V} (h : BiWitness a b) :
    BiWitness (wal v a) (wal v b) := ⟨universalMap v h.forward,universalMap v h.backward⟩
noncomputable def BiWitness.doubleNegation (a : V) : BiWitness a (wn (wn a)) :=
  ⟨doubleNegationIntroduction a,doubleNegationElimination a⟩

#print axioms bi_graph
#print axioms BiWitness.accepted
#print axioms BiWitness.witnesses
#print axioms doubleNegationIntroduction
#print axioms implicationMap
#print axioms universalMap
#print axioms BiWitness.refl
#print axioms BiWitness.symm
#print axioms BiWitness.trans
#print axioms BiWitness.neg
#print axioms BiWitness.imp
#print axioms BiWitness.all
#print axioms BiWitness.doubleNegation
end M6.PA.ActualCertificateEquivalence

