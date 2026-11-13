module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentSeparationAtName
public import PA196.Arithmetic.Transport.FoundationRelationalSequentFree
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Total numeric source separation constructor. Context widening of the
one-bound-variable property preserves its literal numeric formula code. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def sourceMember (a b : V) : V := qqRel 2 1 (qqBvar b∷qqBvar a∷0)
noncomputable def sourceSeparation (p : V) : V :=
  qqAll (qqExs (qqAll (Bootstrapping.iff language (sourceMember 1 0)
    (qqAnd (sourceMember 2 0) p))))

noncomputable def sourceMemberGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out a b. ∃ ta tb tail ts, !qqBvarDef ta a ∧ !qqBvarDef tb b ∧
    !adjoinDef tail ta 0 ∧ !adjoinDef ts tb tail ∧ !qqRelDef out 2 1 ts”

theorem sourceMember_graph (out a b : V) : sourceMemberGraph.val.Evalb ![out,a,b] ↔ out=sourceMember a b := by
  simp [sourceMemberGraph,sourceMember,Matrix.comp_vecCons'']

attribute [local irreducible] sourceMemberGraph iffGraph
noncomputable def sourceSeparationGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “out p. ∃ left right prop body inner middle, !sourceMemberGraph left 1 0 ∧
    !sourceMemberGraph right 2 0 ∧ !qqAndDef prop right p ∧
    !(iffGraph language) body left prop ∧ !qqAllDef inner body ∧
    !qqExsDef middle inner ∧ !qqAllDef out middle”

theorem sourceSeparation_graph (out p : V) : sourceSeparationGraph.val.Evalb ![out,p] ↔ out=sourceSeparation p := by
  simp [sourceSeparationGraph,sourceSeparation,sourceMember_graph,Matrix.comp_vecCons'']

theorem sourceMember_valid {n a b : V} (ha : a<n) (hb : b<n) :
    IsSemiformula language n (sourceMember a b) := by
  simp [sourceMember,source_relations,ha,hb]

theorem source_identity_subst {p : V} (hp : IsSemiformula language 1 p) :
    subst language (qqBvar 0∷0) p=p :=
  subst_eq_self hp (by simp) (by simp)

theorem sourceSeparation_valid {p : V} (hp : IsSemiformula language 1 p) :
    IsFormula language (sourceSeparation p) := by
  have hwide : IsSemiformula language 3 p := by
    have hh := hp.subst (m:=(3:V)) (w:=qqBvar 0∷0) (by simp)
    simpa only [source_identity_subst hp] using hh
  have hleft := sourceMember_valid (V:=V) (n:=3) (a:=1) (b:=0) (by norm_num) (by norm_num)
  have hright := sourceMember_valid (V:=V) (n:=3) (a:=2) (b:=0) (by simpa only [show (3:V)=2+1 by norm_num] using lt_add_one (2:V)) (by norm_num)
  have hthree : (2:V)+1=3 := by norm_num
  simpa [sourceSeparation,IsFormula,one_add_one_eq_two,hthree] using
    (show IsSemiformula language 0 (sourceSeparation p) by
      simp [sourceSeparation,hleft,hright,hwide,one_add_one_eq_two,hthree])

variable [V↓[ℒₒᵣ] ⊧* theory]

theorem translate_property_widening (p member output ambient f lo z : V)
    (hp : IsSemiformula language 1 p) :
    translate (parameters (member∷output∷ambient∷0) f lo z) p=
      translate (parameters (member∷0) f lo z) p := by
  have hlabel : VariableLabel member (qqBvar 0) (member∷output∷ambient∷0) f := by
    simpa using label_bvar (member∷output∷ambient∷0) f 0 (by simp)
  have hh := translate_substs1 p (qqBvar 0) member (member∷output∷ambient∷0) f lo z hp hlabel
  simpa only [substs1,source_identity_subst hp] using hh

#print axioms sourceMember_graph
#print axioms sourceSeparation_graph
#print axioms sourceMember_valid
#print axioms sourceSeparation_valid
#print axioms translate_property_widening
end PA196.Arithmetic.Transport.RelationalSource.Numeric

