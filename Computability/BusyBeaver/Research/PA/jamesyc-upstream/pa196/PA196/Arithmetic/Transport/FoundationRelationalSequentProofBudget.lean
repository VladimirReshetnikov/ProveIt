module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentExsRule
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Definable finite environments budgeted by the actual source derivation
code. Child descent changes environments only by explicit HFS operations. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ProofEnvironment (d f lo z : V) : Prop :=
  EnvironmentsValid 0 f lo z ∧ d≤len f ∧ lo+d≤z

attribute [local irreducible] environmentsGraph
noncomputable def proofEnvironmentGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “d f lo z. !environmentsGraph 0 f lo z ∧ ∃ n, !lenDef n f ∧ d≤n ∧ lo+d≤z”

theorem proofEnvironment_graph (d f lo z : V) :
    proofEnvironmentGraph.val.Evalb ![d,f,lo,z] ↔ ProofEnvironment d f lo z := by
  simp [proofEnvironmentGraph,ProofEnvironment,environments_graph,Matrix.comp_vecCons'']

theorem ProofEnvironment.descend {d child f lo z : V} (h : ProofEnvironment d f lo z)
    (hc : child≤d) : ProofEnvironment child f lo z :=
  ⟨h.1,le_trans hc h.2.1,le_trans (add_le_add (le_refl lo) hc) h.2.2⟩

theorem ProofEnvironment.raise_child {d child f lo z : V} (h : ProofEnvironment d f lo z)
    (hc : child<d) : ProofEnvironment child f (lo+1) z := by
  have hb : lo+1+child≤z := by
    have hh := le_trans (add_le_add (le_refl lo) (succ_le_iff_lt.mpr hc)) h.2.2
    simpa only [add_assoc,add_comm,add_left_comm] using hh
  exact ⟨environments_raise h.1 (by simp) (le_trans (le_add_right (le_refl (lo+1))) hb),
    le_trans hc.le h.2.1,hb⟩

theorem ProofEnvironment.all_child {d child f lo z : V} (h : ProofEnvironment d f lo z)
    (hc : child<d) : ProofEnvironment child (lo∷f) (lo+1) z := by
  have hr := h.raise_child hc
  exact ⟨environments_prependFree hr.1 (lt_add_one lo),
    le_trans hr.2.1 (by simp),hr.2.2⟩

theorem ProofEnvironment.coverage {d f lo z p : V} (h : ProofEnvironment d f lo z)
    (hp : IsFormula language p) (hd : p≤d) : FormulaCovered 0 f lo z p := by
  exact ⟨⟨h.1,le_trans (add_le_add (le_refl lo) hd) h.2.2⟩,
    by simpa using hp,le_trans hd h.2.1⟩

theorem ProofEnvironment.raised_coverage {d f lo z p : V} (h : ProofEnvironment d f lo z)
    (hp : IsFormula language p) (hd : p<d) : FormulaCovered 0 f (lo+1) z p :=
  (h.raise_child hd).coverage hp le_rfl

theorem ProofEnvironment.term_covered {d f lo z t : V} (h : ProofEnvironment d f lo z)
    (ht : IsTerm language t) (hd : t≤d) : Covered t 0 f := by
  apply term_covered_of_code_bound
  · simpa using ht
  · exact le_trans hd h.2.1

theorem free_environment_reconstruct {f : V} (h : 0<len f) : nth f 0∷sndIdx f=f := by
  rcases nil_or_adjoin f with rfl | ⟨x,f,rfl⟩
  · simp at h
  · simp

theorem free_environment_tail_length {f : V} (h : 0<len f) : len (sndIdx f)+1=len f := by
  rw [← free_environment_reconstruct h]
  simp

theorem free_environment_tail_valid {f lo z : V} (h : EnvironmentsValid 0 f lo z) :
    EnvironmentsValid 0 (sndIdx f) lo z := by
  rcases nil_or_adjoin f with rfl | ⟨x,f,rfl⟩
  · simpa [sndIdx,pi₂_zero] using h
  · refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
    intro i hi
    have hh := h.2.2.2 (i+1) (by simpa using hi)
    simpa using hh

theorem ProofEnvironment.tail_child {d child f lo z : V} (h : ProofEnvironment d f lo z)
    (hc : child<d) : ProofEnvironment child (sndIdx f) lo z := by
  have hd : 0<d := lt_of_le_of_lt (by simp) hc
  have hf : 0<len f := lt_of_lt_of_le hd h.2.1
  have hlen : child+1≤len (sndIdx f)+1 := by
    rw [free_environment_tail_length hf]
    exact le_trans (succ_le_iff_lt.mpr hc) h.2.1
  exact ⟨free_environment_tail_valid h.1,(add_le_add_iff_right 1).mp hlen,
    le_trans (add_le_add (le_refl lo) hc.le) h.2.2⟩

theorem fstIdx_lt_of_positive {d : V} (hd : 0<d) : fstIdx d<d := by
  rcases nil_or_adjoin d with rfl | ⟨x,d,rfl⟩
  · simp at hd
  · simp

#print axioms proofEnvironment_graph
#print axioms ProofEnvironment.descend
#print axioms ProofEnvironment.raise_child
#print axioms ProofEnvironment.all_child
#print axioms ProofEnvironment.coverage
#print axioms ProofEnvironment.raised_coverage
#print axioms ProofEnvironment.term_covered
#print axioms free_environment_reconstruct
#print axioms free_environment_tail_length
#print axioms free_environment_tail_valid
#print axioms ProofEnvironment.tail_child
#print axioms fstIdx_lt_of_positive
end PA196.Arithmetic.Transport.RelationalSource.Numeric

