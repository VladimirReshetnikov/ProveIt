module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalCodeLabels
public import PA196.Arithmetic.HeadGraphs
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Exact guarded atomic translation. Source relation tags are not native formula
 tags. HFS environments and term vectors are not Source-Cantor pairs. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualArithmeticGraph PA196.Arithmetic.HeadGraphs

/-- The existing equality replacement, not native primitive equality. -/
def neighborhoodExpr : Expr :=
  let iffE x y := conj (im x y) (im y x)
  conj (al .c (iffE (mem .a .c) (mem .b .c)))
       (al .c (iffE (mem .c .a) (mem .c .b)))

/-- Source membership is (member, container); native membership reverses it. -/
def membershipExpr : Expr := mem .b .a

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def AtomHead (y r a d z : V) : Prop :=
  (r=0 ∧ y=eval neighborhoodExpr a d z 0) ∨
  (r=1 ∧ y=eval membershipExpr a d z 0)

noncomputable def atomHeadGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “y r a d z. (r=0 ∧ !(graph neighborhoodExpr) y a d z 0) ∨
    (r=1 ∧ !(graph membershipExpr) y a d z 0)”

attribute [local irreducible] ActualArithmeticGraph.graph neighborhoodExpr membershipExpr

theorem atomHead_graph (y r a d z : V) :
    atomHeadGraph.val.Evalb ![y,r,a,d,z] ↔ AtomHead y r a d z := by
  simp [atomHeadGraph,AtomHead,graph_correct,Matrix.comp_vecCons'']

theorem atomHead_unique {y y' r a d z : V}
    (h : AtomHead y r a d z) (h' : AtomHead y' r a d z) : y=y' := by
  rcases h with ⟨hr,hy⟩ | ⟨hr,hy⟩ <;>
    rcases h' with ⟨hr',hy'⟩ | ⟨hr',hy'⟩
  · exact hy.trans hy'.symm
  · have hbad := hr.symm.trans hr'
    simp at hbad
  · have hbad := hr'.symm.trans hr
    simp at hbad
  · exact hy.trans hy'.symm

/-- Arity and vector length are checked, and both term positions must be covered. -/
def AtomTranslation (y k r ts b f lo z : V) : Prop :=
  k=2 ∧ len ts=2 ∧ EnvironmentsValid b f lo z ∧
    ∃ a d, VariableLabel a (nth ts 0) b f ∧
      VariableLabel d (nth ts 1) b f ∧ AtomHead y r a d z

noncomputable def atomGraph : 𝚺ᴬ₁.Semisentence 8 := .mkSigma
  “y k r ts b f lo z. k=2 ∧ !lenDef 2 ts ∧ !environmentsGraph b f lo z ∧
    ∃ t s a d, !nthDef t ts 0 ∧ !nthDef s ts 1 ∧
      !variableLabelGraph a t b f ∧ !variableLabelGraph d s b f ∧
      !atomHeadGraph y r a d z”

theorem atom_graph (y k r ts b f lo z : V) :
    atomGraph.val.Evalb ![y,k,r,ts,b,f,lo,z] ↔
      AtomTranslation y k r ts b f lo z := by
  simp [atomGraph,AtomTranslation,environments_graph,variableLabel_graph,
    atomHead_graph,Matrix.comp_vecCons'',eq_comm]

theorem atom_unique {y y' k r ts b f lo z : V}
    (h : AtomTranslation y k r ts b f lo z)
    (h' : AtomTranslation y' k r ts b f lo z) : y=y' := by
  rcases h with ⟨_,_,_,a,d,ha,hd,hh⟩
  rcases h' with ⟨_,_,_,a',d',ha',hd',hh'⟩
  have ea := label_unique ha ha'
  have ed := label_unique hd hd'
  subst a'; subst d'
  exact atomHead_unique hh hh'

theorem atom_exists_iff (k r ts b f lo z : V) :
    (∃ y, AtomTranslation y k r ts b f lo z) ↔
      k=2 ∧ len ts=2 ∧ EnvironmentsValid b f lo z ∧
      Covered (nth ts 0) b f ∧ Covered (nth ts 1) b f ∧ (r=0 ∨ r=1) := by
  constructor
  · rintro ⟨y,hk,ht,he,a,d,ha,hd,hh⟩
    exact ⟨hk,ht,he,label_covered ha,label_covered hd,hh.elim
      (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩
  · rintro ⟨hk,ht,he,ha,hd,hr⟩
    obtain ⟨a,ha⟩ := (label_exists_iff _ _ _).mpr ha
    obtain ⟨d,hd⟩ := (label_exists_iff _ _ _).mpr hd
    rcases hr with hr | hr
    · exact ⟨_,hk,ht,he,a,d,ha,hd,Or.inl ⟨hr,rfl⟩⟩
    · exact ⟨_,hk,ht,he,a,d,ha,hd,Or.inr ⟨hr,rfl⟩⟩

/-- The two atom labels are fresh for the reserved equality binder. -/
theorem atom_labels_reserved {y k r ts b f lo z : V}
    (h : AtomTranslation y k r ts b f lo z) :
    ∃ a d, AtomHead y r a d z ∧ a<lo ∧ d<lo ∧ a≠z ∧ d≠z := by
  rcases h with ⟨_,_,he,a,d,ha,hd,hh⟩
  exact ⟨a,d,hh,label_below ha he,label_below hd he,
    label_reserved ha he,label_reserved hd he⟩


end PA196.Arithmetic.Transport.RelationalSource.Numeric
