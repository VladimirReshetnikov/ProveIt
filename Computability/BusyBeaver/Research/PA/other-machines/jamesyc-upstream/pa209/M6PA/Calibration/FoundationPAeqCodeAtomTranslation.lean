module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeAtoms
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def atomCode (_param _k r ts : V) : V :=
  if r=0 then equalityCode (termCode (nth ts 0)) (termCode (nth ts 1))
  else lessCode (termCode (nth ts 0)) (termCode (nth ts 1))
attribute [local irreducible] termCodeGraph equalityGraph lessGraph
noncomputable def atomGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “out param k r ts. ∃ s t ss tt,
    !nthDef s ts 0 ∧ !nthDef t ts 1 ∧ !termCodeGraph ss s ∧ !termCodeGraph tt t ∧
    ((r=0 ∧ !equalityGraph out ss tt) ∨ (r≠0 ∧ !lessGraph out ss tt))”
theorem atom_graph (out param k r ts : V) : atomGraph.val.Evalb ![out,param,k,r,ts] ↔
    out=atomCode param k r ts := by
  by_cases hr : r=0 <;> simp [atomGraph,atomCode,termCode_graph,equality_graph,less_graph,hr,Matrix.comp_vecCons'']
instance atom_defined : 𝚺ᴬ₁-Function₄ (atomCode : V→V→V→V→V) via atomGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3,v 4]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! atom_graph (v 0) (v 1) (v 2) (v 3) (v 4)

theorem original_relations (k r : V) : (ℒₒᵣ).IsRel k r ↔ k=2 ∧ (r=0 ∨ r=1) := by
  change (V ⊧/![k,r] “k r. (k=2 ∧ r=0) ∨ (k=2 ∧ r=1)”) ↔ _
  simp; tauto

theorem atom_valid {n k r ts : V} (param : V) (hr : (ℒₒᵣ).IsRel k r)
    (ht : IsSemitermVec ℒₒᵣ k n ts) : IsSemiformula Presentation.language n (atomCode param k r ts) := by
  obtain ⟨rfl,_⟩ := (original_relations _ _).mp hr
  have hs := termCode_valid (ht.nth (i:=0) (by simp))
  have ht' := termCode_valid (ht.nth (i:=1) (by simp))
  unfold atomCode
  split_ifs
  · exact equality_valid hs ht'
  · exact less_valid hs ht'

theorem atom_quote {n k : Nat} (param : V) (r : Language.ORing.Rel k)
    (ts : Fin k → ArithmeticSemiterm Nat n) :
    atomCode param (k:V) ⌜r⌝ (SemitermVec.val (fun i => (⌜ts i⌝ : Bootstrapping.Semiterm V ℒₒᵣ n)))=
      ⌜Presentation.atom r ts⌝ := by
  cases r with
  | eq =>
    have hr : (⌜Language.ORing.Rel.eq⌝ : V)=0 := rfl
    simp only [hr,atomCode,if_pos rfl,Presentation.atom]
    rw [←equality_quote]
    simp [SemitermVec.val]
    change equalityCode (termCode (⌜ts 0⌝:V)) (termCode ⌜ts 1⌝)=_
    rw [termCode_quote,termCode_quote]
  | lt =>
    have hr : (⌜Language.ORing.Rel.lt⌝ : V)=1 := by change ((1:Nat):V)=1; simp
    simp only [hr,atomCode,Arithmetic.one_ne_zero,if_false,Presentation.atom]
    rw [←less_quote]
    simp [SemitermVec.val]
    change lessCode (termCode (⌜ts 0⌝:V)) (termCode ⌜ts 1⌝)=_
    rw [termCode_quote,termCode_quote]

#print axioms atom_graph
#print axioms atom_defined
#print axioms original_relations
#print axioms atom_valid
#print axioms atom_quote
end M6.PA.FoundationPAeqCode

