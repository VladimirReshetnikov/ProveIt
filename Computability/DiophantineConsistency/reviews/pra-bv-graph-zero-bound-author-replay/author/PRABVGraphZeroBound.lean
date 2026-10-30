import DiophantineConsistency.PRABVRecGraphBound
/-! A bounded zero-valued BV result from the bounded intermediate BV recursion graph. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRABVGraphZeroBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
open DiophantineConsistency.PRABVRecGraphBound
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] pair₃Def
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem bvGraph_zero_bound (p w : V)
  (hg : (bnd (((BV.blueprint L).graph L).val)).Evalb ![0,p,0,w]) :
  (bnd (bvGraph L).val).Evalb ![0,p,w] := by
  simp [bvGraph, UformulaRec1.Blueprint.result, bnd]
  constructor
  · right
    let ω₀ : Rew ℒₒᵣ Empty 3 Empty 2 := Rew.subst ![#0, Semiterm.numeral 0, #1]
    let ω₁ : Rew ℒₒᵣ Empty 3 Empty 3 := Rew.subst ![#1,#2,#0]
    let ω : Rew ℒₒᵣ Empty 3 Empty 2 := Rew.subst ![Semiterm.numeral 0,#1,#0]
    have hn := PRABndRewriting.natural (((BV.blueprint L).graph L).val) ω ![0,p] w
    have hv : (fun j => (ω #j).val ![0,p] Empty.elim) = ![0,p,0] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hs : Fin.snoc ![0,p] w = ![0,p,w] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    have hs' : Fin.snoc ![0,p,0] w = ![0,p,0,w] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    rw [hv,hs,hs'] at hn
    change (bnd (ω₀ ▹ (ω₁ ▹ (((BV.blueprint L).graph L).val)))).Evalb ![0,p,w]
    have heq : ω₀ ▹ (ω₁ ▹ (((BV.blueprint L).graph L).val)) = ω ▹ (((BV.blueprint L).graph L).val) := by
      simp [←TransitiveRewriting.comp_app, Rew.subst_comp_subst, ω₀,ω₁,ω]
    rw [heq]
    exact hn.mpr hg
  · right
    rfl

noncomputable def boundedBVGraph : ArithmeticSemisentence 3 := bnd (bvGraph L).val
noncomputable def bvGraphZeroBody : ArithmeticSemisentence 3 :=
  “p pr w. pr < w ∧ pr+1 ≤ w ∧ !pair₃Def pr 0 p 0 ∧
    !((boundedBVFix (L := L))) pr 0 p 0 w → !((boundedBVGraph (L := L))) 0 p w”
theorem bvGraphZeroBody_model (e : Fin 3 → V) : (bvGraphZeroBody (L := L)).Eval e Empty.elim := by
  simp [bvGraphZeroBody,boundedBVGraph,boundedBVFix,bvFixInside,Semiformula.eval_substs]
  intro hp hs hpair hfix
  apply bvGraph_zero_bound
  apply recGraph_bound_of_pair (L := L) (BV.blueprint L) 0 (e 0) 0 (e 1) (e 2) hp hs
  · simpa using hpair
  · have hv : (FirstOrder.Semiterm.val e Empty.elim ∘ (![ #1, Semiterm.numeral 0, #0, Semiterm.numeral 0, #2 ] : Fin 5 → Semiterm ℒₒᵣ Empty 3)) = ![e 1,0,e 0,0,e 2] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      refine Fin.cases rfl (fun k => ?_) k
      refine Fin.cases rfl (fun k => ?_) k
      refine Fin.cases rfl (fun k => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) k
    rw [hv] at hfix
    exact hfix
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def bvGraphZeroSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (bvGraphZeroBody (L := L))
theorem candidate_proves_bv_graph_zero_bound : PRA ⊢ bvGraphZeroSentence (L := L) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, bvGraphZeroSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact bvGraphZeroBody_model e
end DiophantineConsistency.PRABVGraphZeroBound
