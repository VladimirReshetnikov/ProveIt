import PA196PRAWitnessTower
import DiophantineConsistency.PRAWitnessBoundTerms

/-! Candidate-PRA transfer for a tower whose argument is any represented
bound term, including nested exponentials. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA196PRAWitnessNestedTower
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessTransfer PRAWitnessCalculus
  PRAWitnessBoundTerms PRAWitnessBoundTerms.BoundTerm PRAWitnessExpBounds
  PA196PRAQVecTower PA196PRAQVecTowerMonotone PA196PRAQVecTowerDomination
  PA196PASubstitutionTowerGraph PA196PAQVecTowerAlgebra

variable {n : ℕ}
noncomputable def nestedGraph (A : BoundTerm n) : ArithmeticSemisentence (n+1) :=
  “t. ∃ a, !(A.graph) a ⋯ ∧ !towerGraph t a”
noncomputable def nestedTerm (A : BoundTerm n) : TermN n :=
  .func towerCode ![.func addCode ![A.term, Semiterm.lMap embedding ‘2’],
    .func addCode ![.func mulCode ![Semiterm.lMap embedding ‘4’, A.term], Semiterm.lMap embedding ‘1’]]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero

theorem nestedTerm_val (A : BoundTerm n) (e : Fin n → M) :
    (nestedTerm A).val e Empty.elim = tower (A.term.val e Empty.elim+2) (4*A.term.val e Empty.elim+1) := by
  simp [nestedTerm, tower, Semiterm.val_func, val_lMap_std]
  rfl

theorem nestedTerm_mono (A : BoundTerm n) : Mono M (fun e => (nestedTerm A).val e Empty.elim) := by
  intro e e' h
  dsimp only
  rw [nestedTerm_val, nestedTerm_val]
  have ha := mono_term (M := M) A e e' h
  exact le_trans (tower_seed_mono _ _ _ (add_le_add (mul_le_mul' le_rfl ha) le_rfl))
    (tower_index_mono _ _ _ (add_le_add ha le_rfl))
end models

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem nestedGraph_eval (A : BoundTerm n) (t : V) (e : Fin n → V) :
    (nestedGraph A).Eval (t :> e) Empty.elim ↔
      t = iter (A.vval e+2) (4*A.vval e+1) := by
  have hm (x : V) : (Semiterm.val (L := ℒₒᵣ) (x :> t :> e) Empty.elim ∘
      ((#0 :> fun i => #i.succ.succ) : Fin (n+1) → ArithmeticSemiterm Empty (n+2))) = (x :> e) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp
  simp [nestedGraph, hm, eval_graph, towerGraph_eval]

theorem PRA_proves_nested_domination (A : BoundTerm n) : PRA ⊢ dominates (nestedGraph A) (nestedTerm A) := by
  apply PRAWitnessTransfer.dominates_of_val
  intro M _ _ _ _ t e h
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at h
  have hm (x : M) : (Semiterm.val (L := ℒₒᵣ) (x :> t :> e) Empty.elim ∘
      ((#0 :> fun i => #i.succ.succ) : Fin (n+1) → ArithmeticSemiterm Empty (n+2))) = (x :> e) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp
  simp [nestedGraph, hm] at h
  obtain ⟨a, ha, ht⟩ := h
  have ha' : a = A.term.val e Empty.elim := (eval_graph_model A a e).mp ha
  have ht' := towerGraph_candidate t a ht
  have hv := nestedTerm_val (M := M) A e
  rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  simp [Semiformula.Operator.val, Semiformula.Operator.LE.sentence_eq,
    Semiformula.Operator.Eq.eq, ht', ha', hv]

section finalModels
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_exs_nested {n : ℕ}
    (ψ : ArithmeticSemisentence (n+1)) (hψ : Hierarchy 𝚺 1 ψ) (A : BoundTerm n)
    (hI : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) (x : V),
      ψ.Eval (x :> e) Empty.elim → x ≤ iter (A.vval e+2) (4*A.vval e+1))
    (hWB : WB M ψ) : WB M (∃⁰ ψ) := by
  apply wb_exs_bound ψ hψ (nestedGraph A) (nestedTerm A)
    (PRA_proves_nested_domination A) (nestedTerm_mono A) ?_ hWB
  intro V _ _ e x hx
  exact ⟨_, (nestedGraph_eval A _ e).mpr rfl, x, hI V e x hx, hx⟩

end finalModels
#print axioms wb_exs_nested
end PA196PRAWitnessNestedTower
