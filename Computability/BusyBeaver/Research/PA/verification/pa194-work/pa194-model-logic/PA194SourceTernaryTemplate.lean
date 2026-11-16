import PA194SourceTemplates
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194SourceTemplates
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Simultaneously substitute model-valued term codes into a fixed typed template. -/
noncomputable def templateThree (p : Semiproposition SourceL 3) (x y z : V) : V :=
  subst SourceL (?[x,y,z] : V) ⌜p⌝
noncomputable def templateThreeGraph (p : Semiproposition SourceL 3) : 𝚺₁.Semisentence 4 :=
  .mkSigma “out x y z. ∃ zs ys xs, !adjoinDef zs z 0 ∧ !adjoinDef ys y zs ∧
    !adjoinDef xs x ys ∧ !(substsGraph SourceL) out xs ↑(⌜p⌝ : Nat)”
theorem templateThree_graph (p : Semiproposition SourceL 3) (out x y z : V) :
    (templateThreeGraph p).val.Evalb ![out,x,y,z] ↔ out = templateThree p x y z := by
  simp [templateThreeGraph,templateThree, Semiformula.quote_eq_encode, numeral_eq_natCast]
instance templateThree_defined (p : Semiproposition SourceL 3) :
    𝚺₁-Function₃ (templateThree p : V → V → V → V) via templateThreeGraph p := .mk fun v => by
  have hv : ![v 0,v 1,v 2,v 3] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  change (templateThreeGraph p).val.Evalb v ↔ v 0 = templateThree p (v 1) (v 2) (v 3)
  simpa only [hv] using templateThree_graph p (v 0) (v 1) (v 2) (v 3)
theorem templateThree_valid (p : Semiproposition SourceL 3) {n x y z : V}
    (hx : IsSemiterm SourceL n x) (hy : IsSemiterm SourceL n y) (hz : IsSemiterm SourceL n z) :
    IsSemiformula SourceL n (templateThree p x y z) := by
  apply IsSemiformula.subst (show IsSemiformula SourceL 3 (⌜p⌝ : V) by
    simpa using Semiformula.quote_isSemiformula (V := V) p)
  simp [hx,hy,hz,show (3:V)=2+1 from two_add_one_eq_three.symm]
theorem templateThree_quote {m : Nat} (p : Semiproposition SourceL 3)
    (x y z : Semiterm SourceL Nat m) :
    templateThree p (⌜x⌝ : V) ⌜y⌝ ⌜z⌝ = ⌜p ⇜ ![x,y,z]⌝ := by
  simp only [templateThree, Semiformula.quote_def, Semiformula.typed_quote_substs]
  rfl
#print axioms templateThree_graph
#print axioms templateThree_defined
#print axioms templateThree_valid
#print axioms templateThree_quote
end generic
end PA194SourceTemplates
