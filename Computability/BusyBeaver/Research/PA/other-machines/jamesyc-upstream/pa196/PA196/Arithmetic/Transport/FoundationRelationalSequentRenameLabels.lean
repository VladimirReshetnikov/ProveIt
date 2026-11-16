module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentVacuity
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Exact finite label-renaming relations. These supply source-environment
metadata for conditional native congruence, not a proof of that congruence. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def renameLabelValue (x y a : V) : V := by
  classical
  exact if a=x then y else a

noncomputable def renameLabelGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “out x y a. (a=x ∧ out=y) ∨ (a≠x ∧ out=a)”

theorem renameLabel_graph (out x y a : V) :
    renameLabelGraph.val.Evalb ![out,x,y,a] ↔ out=renameLabelValue x y a := by
  classical
  by_cases h : a=x <;> simp [renameLabelGraph,renameLabelValue,h]

@[simp] theorem renameLabel_self (x y : V) : renameLabelValue x y x=y := by
  simp [renameLabelValue]

theorem renameLabel_other {x y a : V} (h : a≠x) : renameLabelValue x y a=a := by
  simp [renameLabelValue,h]

theorem renameLabel_reserved {x y a z : V} (ha : z≠a) (hy : z≠y) :
    z≠renameLabelValue x y a := by
  classical
  by_cases h : a=x <;> simp [renameLabelValue,h,ha,hy]

def RenameEnvironment (x y old new : V) : Prop :=
  len old=len new ∧ ∀ i<len old, nth new i=renameLabelValue x y (nth old i)

attribute [local irreducible] renameLabelGraph
noncomputable def renameEnvironmentGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “x y old new. ∃ n, !lenDef n old ∧ !lenDef n new ∧
    ∀ i<n, ∃ a b, !nthDef a old i ∧ !nthDef b new i ∧ !renameLabelGraph b x y a”

theorem renameEnvironment_graph (x y old new : V) :
    renameEnvironmentGraph.val.Evalb ![x,y,old,new] ↔ RenameEnvironment x y old new := by
  simp [renameEnvironmentGraph,RenameEnvironment,renameLabel_graph,Matrix.comp_vecCons'']

theorem RenameEnvironment.adjoin {x y old new : V} (h : RenameEnvironment x y old new)
    (a : V) : RenameEnvironment x y (a∷old) (renameLabelValue x y a∷new) := by
  constructor
  · simp [h.1]
  · intro i hi
    rcases zero_or_succ i with rfl | ⟨i,rfl⟩
    · simp
    · have hi' : i<len old := by simpa using hi
      simpa using h.2 i hi'

theorem RenameEnvironment.adjoin_fixed {x y old new a : V}
    (h : RenameEnvironment x y old new) (ha : a≠x) :
    RenameEnvironment x y (a∷old) (a∷new) := by
  simpa only [renameLabel_other ha] using h.adjoin a

theorem renameEnvironment_fixed {x y env : V} (h : ∀ i<len env, x≠nth env i) :
    RenameEnvironment x y env env := by
  refine ⟨rfl,?_⟩
  intro i hi
  exact (renameLabel_other (Ne.symm (h i hi))).symm

theorem renameEnvironment_head {x y env : V} (h : ∀ i<len env, x≠nth env i) :
    RenameEnvironment x y (x∷env) (y∷env) := by
  simpa only [renameLabel_self] using (renameEnvironment_fixed (y:=y) h).adjoin x

theorem variableLabel_rename {x y b b' f f' a t : V}
    (hb : RenameEnvironment x y b b') (hf : RenameEnvironment x y f f')
    (ht : VariableLabel a t b f) :
    VariableLabel (renameLabelValue x y a) t b' f' := by
  rcases ht with ⟨i,hi,rfl,rfl⟩ | ⟨i,hi,rfl,rfl⟩
  · rw [← hb.2 i hi]
    exact label_bvar b' f' i (by simpa [← hb.1] using hi)
  · rw [← hf.2 i hi]
    exact label_fvar b' f' i (by simpa [← hf.1] using hi)

theorem covered_rename {x y b b' f f' t : V}
    (hb : RenameEnvironment x y b b') (hf : RenameEnvironment x y f f')
    (ht : Covered t b f) : Covered t b' f' := by
  obtain ⟨a,ha⟩ := (label_exists_iff _ _ _).mpr ht
  exact label_covered (variableLabel_rename hb hf ha)

theorem totalLabel_rename {x y b b' f f' t : V}
    (hb : RenameEnvironment x y b b') (hf : RenameEnvironment x y f f')
    (ht : Covered t b f) : totalLabel t b' f'=renameLabelValue x y (totalLabel t b f) := by
  obtain ⟨a,ha⟩ := (label_exists_iff _ _ _).mpr ht
  rw [← totalLabel_agrees ha]
  exact (totalLabel_agrees (variableLabel_rename hb hf ha)).symm

theorem RenameEnvironment.reserved {x y old new z : V}
    (h : RenameEnvironment x y old new) (ho : ∀ i<len old, z≠nth old i) (hy : z≠y) :
    ∀ i<len new, z≠nth new i := by
  intro i hi
  have hi' : i<len old := by simpa [h.1] using hi
  rw [h.2 i hi']
  exact renameLabel_reserved (ho i hi') hy

theorem renameLabel_lt {x y a lo : V} (ha : a<lo) (hy : y<lo) :
    renameLabelValue x y a<lo := by
  classical
  by_cases h : a=x <;> simp [renameLabelValue,h,ha,hy]

theorem environments_rename {x y b b' f f' lo z : V}
    (hb : RenameEnvironment x y b b') (hf : RenameEnvironment x y f f')
    (h : EnvironmentsValid b f lo z) (hy : y<lo) : EnvironmentsValid b' f' lo z := by
  refine ⟨h.1,h.2.1,?_,?_⟩
  · intro i hi
    have hi' : i<len b := by simpa [hb.1] using hi
    rw [hb.2 i hi']
    exact renameLabel_lt (h.2.2.1 i hi') hy
  · intro i hi
    have hi' : i<len f := by simpa [hf.1] using hi
    rw [hf.2 i hi']
    exact renameLabel_lt (h.2.2.2 i hi') hy

theorem coverage_rename {x y b b' f f' lo z p : V}
    (hb : RenameEnvironment x y b b') (hf : RenameEnvironment x y f f')
    (h : FormulaCovered b f lo z p) (hy : y<lo) : FormulaCovered b' f' lo z p := by
  refine ⟨⟨environments_rename hb hf h.1.1 hy,h.1.2⟩,?_,?_⟩
  · simpa [← hb.1] using h.2.1
  · simpa [← hf.1] using h.2.2

#print axioms renameLabel_lt
#print axioms environments_rename
#print axioms coverage_rename
#print axioms renameLabel_graph
#print axioms renameLabel_self
#print axioms renameLabel_other
#print axioms renameLabel_reserved
#print axioms renameEnvironment_graph
#print axioms RenameEnvironment.adjoin
#print axioms RenameEnvironment.adjoin_fixed
#print axioms renameEnvironment_fixed
#print axioms renameEnvironment_head
#print axioms variableLabel_rename
#print axioms covered_rename
#print axioms totalLabel_rename
#print axioms RenameEnvironment.reserved
end PA196.Arithmetic.Transport.RelationalSource.Numeric

