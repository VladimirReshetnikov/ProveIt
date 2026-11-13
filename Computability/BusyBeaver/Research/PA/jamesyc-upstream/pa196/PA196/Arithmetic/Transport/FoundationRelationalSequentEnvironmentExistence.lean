module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentZeroEnvironment
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Uniform finite proof environments from a model-length primitive recursion.
No host function or external finite list is encoded by assertion. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] zeroEnvironmentGraph
noncomputable def zeroEnvironmentInvariant : ArithmeticSemisentence 1 :=
  “n. ∃ f, !zeroEnvironmentGraph f n ∧ !lenDef n f ∧ ∀ i<n, !nthDef 0 f i”

theorem zeroEnvironment_invariant (n : V) : zeroEnvironmentInvariant.Evalb ![n] ↔
    len (zeroEnvironment n)=n ∧ ∀ i<n, nth (zeroEnvironment n) i=0 := by
  simp [zeroEnvironmentInvariant,zeroEnvironment_graph,Matrix.comp_vecCons'',eq_comm]

variable [V↓[ℒₒᵣ] ⊧* theory]

theorem zeroEnvironment_properties (n : V) :
    len (zeroEnvironment n)=n ∧ ∀ i<n, nth (zeroEnvironment n) i=0 := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
    len (zeroEnvironment n)=n ∧ ∀ i<n, nth (zeroEnvironment n) i=0) ?_ ?_ ?_ n
  · refine ⟨fun _ => 0,Rewriting.emb zeroEnvironmentInvariant,by trivial,?_⟩
    intro n
    simpa using (zeroEnvironment_invariant (V:=V) n).symm
  · simp
  · intro n ih
    constructor
    · simp [ih.1]
    · intro i hi
      rcases zero_or_succ i with he | ⟨j,rfl⟩
      · simp [he]
      · have hj : j<n := by simpa using hi
        simpa using ih.2 j hj

theorem proofEnvironment_exists (d : V) : ∃ f lo z : V, ProofEnvironment d f lo z := by
  refine ⟨zeroEnvironment d,1,1+d,?_,?_,le_rfl⟩
  · refine ⟨by simp,by simp,?_,?_⟩
    · intro i hi
      simp at hi
    · intro i hi
      have hd := zeroEnvironment_properties (V:=V) d
      rw [hd.1] at hi
      rw [hd.2 i hi]
      simp
  · exact (zeroEnvironment_properties d).1.ge

attribute [local irreducible] proofEnvironmentGraph
noncomputable def proofEnvironmentExistenceSentence : ArithmeticSentence :=
  “∀ d, ∃ f lo z, !proofEnvironmentGraph d f lo z”

theorem pa_proves_proofEnvironment_exists : theory ⊢ proofEnvironmentExistenceSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [proofEnvironmentExistenceSentence,models_iff,proofEnvironment_graph,Matrix.comp_vecCons'']
  exact proofEnvironment_exists

#print axioms zeroEnvironment_invariant
#print axioms zeroEnvironment_properties
#print axioms proofEnvironment_exists
#print axioms pa_proves_proofEnvironment_exists
end PA196.Arithmetic.Transport.RelationalSource.Numeric

