module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentRenameLabels
public import PA196.Arithmetic.Transport.CertificateInterface
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Conditional accepted bicertificates for the pending source-renaming
induction. Universal congruence requires an actual antecedent-vacuity code. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence PA196.Arithmetic.Checker

universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ConditionalBiCertificates (forward backward e a b : V) : Prop :=
  verifyValue forward=wim e (wim a b)+1 ∧ verifyValue backward=wim e (wim b a)+1

attribute [local irreducible] acceptedArrowGraph ActualArithmeticGraph.graph
noncomputable def conditionalBiGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “forward backward e a b. ∃ ab ba,
    !(ActualArithmeticGraph.graph PA196.Arithmetic.HeadGraphs.implicationExpr) ab a b 0 0 ∧
    !(ActualArithmeticGraph.graph PA196.Arithmetic.HeadGraphs.implicationExpr) ba b a 0 0 ∧
    !acceptedArrowGraph forward e ab ∧ !acceptedArrowGraph backward e ba”

theorem conditionalBi_graph (forward backward e a b : V) :
    conditionalBiGraph.val.Evalb ![forward,backward,e,a,b] ↔
      ConditionalBiCertificates forward backward e a b := by
  simp [conditionalBiGraph,ConditionalBiCertificates,ActualArithmeticGraph.graph_correct,
    acceptedArrow_graph,wim,implicationValue,Matrix.comp_vecCons'']

structure ConditionalBiWitness (e a b : V) where
  forward : Certificate (wim e (wim a b))
  backward : Certificate (wim e (wim b a))

theorem ConditionalBiWitness.accepted {e a b : V} (h : ConditionalBiWitness e a b) :
    ConditionalBiCertificates h.forward.code h.backward.code e a b :=
  ⟨h.forward.accepted,h.backward.accepted⟩

variable [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def conditionalContrapose {e a b : V} (p : Certificate (wim e (wim a b))) :
    Certificate (wim e (wim (wn b) (wn a))) := by
  let h : Context [e] e := .assumption (by simp)
  exact (Context.mp (.mp h (.closed p)) (.closed (contraposition a b))).deduction.empty

noncomputable def contextImplicationCongruence {Γ : List V} {a aa b bb : V}
    (p : Context Γ (wim aa a)) (q : Context Γ (wim b bb)) :
    Context Γ (wim (wim a b) (wim aa bb)) := by
  let h : Context (aa :: wim a b :: Γ) aa := .assumption (by simp)
  let hab : Context (aa :: wim a b :: Γ) (wim a b) := .assumption (by simp)
  exact (Context.mp (.mp (.mp h ((p.up (wim a b)).up aa)) hab)
    ((q.up (wim a b)).up aa)).deduction.deduction

noncomputable def conditionalImplicationCongruence {e a aa b bb : V}
    (p : Certificate (wim e (wim aa a))) (q : Certificate (wim e (wim b bb))) :
    Certificate (wim e (wim (wim a b) (wim aa bb))) := by
  let h : Context [e] e := .assumption (by simp)
  exact (contextImplicationCongruence (.mp h (.closed p)) (.mp h (.closed q))).deduction.empty

noncomputable def conditionalUniversal {e a b : V} (x : V)
    (hv : Certificate (wim e (wal x e))) (p : Certificate (wim e (wim a b))) :
    Certificate (wim e (wim (wal x a) (wal x b))) := by
  let he : Context [wal x a,e] e := .assumption (by simp)
  let ha : Context [wal x a,e] (wal x a) := .assumption (by simp)
  let hwe : Context [wal x a,e] (wal x e) := .mp he (.closed hv)
  let hstep := hwe.forallMP x (.closed (.all x p))
  exact (ha.forallMP x hstep).deduction.deduction.empty

noncomputable def ConditionalBiWitness.refl (e a : V) : ConditionalBiWitness e a a :=
  ⟨(identity a).mp (Dominated.k (wim a a) e),(identity a).mp (Dominated.k (wim a a) e)⟩

noncomputable def ConditionalBiWitness.neg {e a b : V} (h : ConditionalBiWitness e a b) :
    ConditionalBiWitness e (wn a) (wn b) :=
  ⟨conditionalContrapose h.backward,conditionalContrapose h.forward⟩

noncomputable def ConditionalBiWitness.imp {e a aa b bb : V}
    (h : ConditionalBiWitness e a aa) (k : ConditionalBiWitness e b bb) :
    ConditionalBiWitness e (wim a b) (wim aa bb) :=
  ⟨conditionalImplicationCongruence h.backward k.forward,
    conditionalImplicationCongruence h.forward k.backward⟩

noncomputable def ConditionalBiWitness.all {e a b : V} (h : ConditionalBiWitness e a b)
    (x : V) (hv : Certificate (wim e (wal x e))) : ConditionalBiWitness e (wal x a) (wal x b) :=
  ⟨conditionalUniversal x hv h.forward,conditionalUniversal x hv h.backward⟩

#print axioms conditionalBi_graph
#print axioms ConditionalBiWitness.accepted
#print axioms conditionalContrapose
#print axioms contextImplicationCongruence
#print axioms conditionalImplicationCongruence
#print axioms conditionalUniversal
#print axioms ConditionalBiWitness.refl
#print axioms ConditionalBiWitness.neg
#print axioms ConditionalBiWitness.imp
#print axioms ConditionalBiWitness.all
end PA196.Arithmetic.Transport.RelationalSource.Numeric

