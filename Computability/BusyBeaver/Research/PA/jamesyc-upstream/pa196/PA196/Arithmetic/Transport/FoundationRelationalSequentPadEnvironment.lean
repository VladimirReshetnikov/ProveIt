module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentEnvironmentExistence
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Model-length right padding of finite label environments. Existing entries
retain their indices; this is not repeated head insertion. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] concatDef concat

noncomputable def padEnvironmentBlueprint : PR.Blueprint 1 where
  zero := .mkSigma “out f. out=f”
  succ := .mkSigma “out previous i f. ∃ zero, zero=0 ∧ !concatDef out previous zero”


noncomputable def padEnvironmentConstruction : PR.Construction V padEnvironmentBlueprint where
  zero := fun v => v 0
  succ := fun _ _ previous => concat previous 0
  zero_defined := .mk fun v => by simp [padEnvironmentBlueprint]
  succ_defined := .mk fun v => by simp [padEnvironmentBlueprint]


noncomputable def padEnvironment (f n : V) : V := padEnvironmentConstruction.result ![f] n
noncomputable def padEnvironmentGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out f n. !(padEnvironmentBlueprint.resultDef) out n f”

theorem padEnvironment_graph (out f n : V) :
    padEnvironmentGraph.val.Evalb ![out,f,n] ↔ out=padEnvironment f n := by
  simp only [padEnvironmentGraph,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
  rw [Semiformula.eval_substs]
  simpa [padEnvironment,Matrix.comp_vecCons''] using!
    padEnvironmentConstruction.result_defined_iff ![out,n,f]

@[simp] theorem padEnvironment_zero (f : V) : padEnvironment f 0=f := by
  simp [padEnvironment,padEnvironmentConstruction]
@[simp] theorem padEnvironment_succ (f n : V) :
    padEnvironment f (n+1)=concat (padEnvironment f n) 0 := by
  simp [padEnvironment,padEnvironmentConstruction]


attribute [local irreducible] padEnvironmentGraph
noncomputable def padEnvironmentInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ f, ∃ out k, !padEnvironmentGraph out f n ∧ !lenDef k f ∧
    !lenDef (k+n) out ∧
    (∀ i<k, ∃ a, !nthDef a f i ∧ !nthDef a out i) ∧
    (∀ i<k+n, k≤i → !nthDef 0 out i)”

theorem padEnvironment_invariant (n : V) :
    padEnvironmentInvariant.Evalb ![n] ↔ ∀ f : V,
      len (padEnvironment f n)=len f+n ∧
      (∀ i<len f, nth (padEnvironment f n) i=nth f i) ∧
      (∀ i<len f+n, len f≤i → nth (padEnvironment f n) i=0) := by
  simp [padEnvironmentInvariant,padEnvironment_graph,Matrix.comp_vecCons'',eq_comm]

variable [V↓[ℒₒᵣ] ⊧* theory]
theorem padEnvironment_properties (f n : V) :
    len (padEnvironment f n)=len f+n ∧
    (∀ i<len f, nth (padEnvironment f n) i=nth f i) ∧
    (∀ i<len f+n, len f≤i → nth (padEnvironment f n) i=0) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ n : V, ∀ f : V,
      len (padEnvironment f n)=len f+n ∧
      (∀ i<len f, nth (padEnvironment f n) i=nth f i) ∧
      (∀ i<len f+n, len f≤i → nth (padEnvironment f n) i=0) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V => ∀ f : V,
      len (padEnvironment f n)=len f+n ∧
      (∀ i<len f, nth (padEnvironment f n) i=nth f i) ∧
      (∀ i<len f+n, len f≤i → nth (padEnvironment f n) i=0)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb padEnvironmentInvariant,by trivial,?_⟩
      intro n
      simpa using (padEnvironment_invariant (V:=V) n).symm
    · intro f
      refine ⟨by simp,by simp,?_⟩
      intro i hi hlo
      have : i<len f := by simpa using hi
      exact (not_lt_of_ge hlo this).elim
    · intro n ih f
      obtain ⟨hlen,hprefix,hzero⟩ := ih f
      refine ⟨by simp [hlen,add_assoc],?_,?_⟩
      · intro i hi
        rw [padEnvironment_succ,concat_nth_lt _ _ (by rw [hlen]; exact lt_of_lt_of_le hi (by simp)),hprefix i hi]
      · intro i hi hlo
        rw [padEnvironment_succ]
        have hi' : i≤len f+n := by exact (Arithmetic.lt_succ_iff_le.mp (by simpa only [← add_assoc] using hi))
        rcases lt_or_eq_of_le hi' with hlt | heq
        · rw [concat_nth_lt _ _ (by simpa [hlen] using hlt)]
          exact hzero i hlt hlo
        · rw [heq,← hlen,concat_nth_len]
  exact all n f

#print axioms padEnvironment_graph
#print axioms padEnvironment_invariant
#print axioms padEnvironment_properties
end PA196.Arithmetic.Transport.RelationalSource.Numeric

