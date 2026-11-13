module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.ActualCertificateEquivalenceNNFCases
public import PA196.Arithmetic.Transport.FoundationRelationalCodeRecursion
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic


/-! The exact first-order certificate relation and course-of-values invariant
for subsequent full-PA NNF induction. This file does not prove that induction. -/
namespace PA196.Arithmetic.Transport.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open PA196.Arithmetic.Checker
open RelationalSource RelationalSource.Numeric

attribute [local irreducible] ActualArithmeticGraph.graph translateGraph negGraph biGraph

noncomputable def nnfGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “c d param p. ∃ np a b nb,
    !(negGraph language) np p ∧ !translateGraph a param np ∧
    !translateGraph b param p ∧ !(ActualArithmeticGraph.graph translationNeg) nb b 0 0 0 ∧
    !biGraph c d a nb”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem nnf_graph (c d param p : V) :
    nnfGraph.val.Evalb ![c,d,param,p] ↔
      BiCertificates c d (translate param (Bootstrapping.neg language p)) (wn (translate param p)) := by
  simp [nnfGraph,translate_graph,bi_graph,ActualArithmeticGraph.graph_correct,
    Matrix.comp_vecCons'']
  simp [translationNeg,PA196.Arithmetic.HeadGraphs.neg,wn,wim,implicationValue,
    PA196.Arithmetic.HeadGraphs.implicationExpr,PA196.Arithmetic.HeadGraphs.im,ActualArithmeticGraph.eval]

attribute [local irreducible] nnfGraph

/-- This is an unrestricted arithmetic formula, not asserted Sigma-one: the
arbitrary parameter quantifier precedes existential certificate witnesses. -/
noncomputable def nnfInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ p<n, !((isUFormula language).sigma) p → ∀ param, ∃ c d, !nnfGraph c d param p”

theorem nnf_invariant (n : V) :
    nnfInvariant.Evalb ![n] ↔
      ∀ p<n, IsUFormula language p → ∀ param,
        ∃ c d, BiCertificates c d (translate param (Bootstrapping.neg language p))
          (wn (translate param p)) := by
  simp [nnfInvariant,nnf_graph,Matrix.comp_vecCons'']

#print axioms nnf_graph
#print axioms nnf_invariant
end PA196.Arithmetic.Transport.ActualCertificateEquivalence

