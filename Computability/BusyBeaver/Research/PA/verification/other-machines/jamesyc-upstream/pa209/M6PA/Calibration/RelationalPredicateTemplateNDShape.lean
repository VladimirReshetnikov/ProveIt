module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLKBounded
public import M6PA.Calibration.RelationalPredicateTemplateLiftND
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

theorem nd_premise_covered {Γ : List ND.Form} {q : ND.Form} (d : ND.Proof Γ q)
    {f : V} (hb : (proofFreeBound d:V)≤len f) (p : ND.Form) (hp : p∈Γ) :
    ∀i,p.FVar? i→(i:V)<len f := by
  have hc := sequentCovered_of_proofBound d hb
  have hm : (∼p)∈ND.negatives Γ+⦃q⦄ := by
    simp only [Multiset.mem_add,ND.negatives,Multiset.mem_coe,List.mem_map]
    exact Or.inl ⟨p,hp,rfl⟩
  simpa only [Semiformula.FVar?, Semiformula.freeVariables_not] using hc (∼p) hm

theorem nd_goal_covered {Γ : List ND.Form} {q : ND.Form} (d : ND.Proof Γ q)
    {f : V} (hb : (proofFreeBound d:V)≤len f) : ∀i,q.FVar? i→(i:V)<len f :=
  sequentCovered_of_proofBound d hb q (by simp)

theorem nd_sequent_shape {Γ : List ND.Form} {q : ND.Form} (d : ND.Proof Γ q)
    {P f : V} (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (hb : (proofFreeBound d:V)≤len f) :
    ∀r,r∈sequentValue (ND.negatives Γ+⦃q⦄) P f →
      r=formulaValue q P 0 f ∨ ∃a,a∈sequentValue (Γ:Multiset ND.Form) P f ∧
        r=Bootstrapping.neg L a := by
  intro r hr
  rcases (mem_sequentValue _ _ _ _).mp hr with ⟨p,hp,rfl⟩
  rcases Multiset.mem_add.mp hp with hp | hp
  · simp only [ND.negatives,Multiset.mem_coe,List.mem_map] at hp
    rcases hp with ⟨a,ha,rfl⟩
    refine Or.inr ⟨formulaValue a P 0 f,(mem_sequentValue _ _ _ _).mpr ⟨a,ha,rfl⟩,?_⟩
    exact formulaValue_neg a hP ⟨by simp,hf⟩ (nd_premise_covered d hb a ha)
  · have he : p=q := by simpa using hp
    subst p
    exact Or.inl rfl
#print axioms nd_premise_covered
#print axioms nd_sequent_shape
end M6.PA.RelationalPredicateTemplate

