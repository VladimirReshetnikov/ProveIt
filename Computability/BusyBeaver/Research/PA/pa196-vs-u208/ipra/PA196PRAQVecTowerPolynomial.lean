import PA196PRAQVecTowerDomination

/-! Reparameterize the candidate-PRA tower bound by an arithmetic polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA196PRAQVecTowerPolynomial
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessTransfer PRAWitnessCalculus
  PA196PRAQVecTower PA196PRAQVecTowerMonotone PA196PRAQVecTowerDomination
  PA196PASubstitutionTowerGraph

variable {n : ℕ}
noncomputable def polyTowerGraph (P : ArithmeticSemiterm Empty n) : ArithmeticSemisentence (n+1) :=
  Rewriting.subst towerGraph.val ![#0, Rew.bShift P]
noncomputable def polyTowerTerm (P : ArithmeticSemiterm Empty n) : TermN n :=
  .func towerCode ![
    .func addCode ![Semiterm.lMap embedding P, Semiterm.lMap embedding ‘2’],
    .func addCode ![.func mulCode ![Semiterm.lMap embedding ‘4’, Semiterm.lMap embedding P],
      Semiterm.lMap embedding ‘1’]]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero

set_option linter.unusedSectionVars false in
theorem polyTowerTerm_val (P : ArithmeticSemiterm Empty n) (e : Fin n → M) :
    (polyTowerTerm P).val e Empty.elim = tower (P.val e Empty.elim+2) (4*P.val e Empty.elim+1) := by
  simp [polyTowerTerm, tower, Semiterm.val_func, val_lMap_std]
  rfl

theorem polyTowerTerm_mono (P : ArithmeticSemiterm Empty n) :
    Mono M (fun e => (polyTowerTerm P).val e Empty.elim) := by
  intro e e' h
  change (polyTowerTerm P).val e Empty.elim ≤ (polyTowerTerm P).val e' Empty.elim
  rw [polyTowerTerm_val, polyTowerTerm_val]
  have hp := PRAWitnessCalculus.term_mono P e e' h
  exact le_trans (tower_seed_mono _ _ _ (add_le_add (mul_le_mul' le_rfl hp) le_rfl))
    (tower_index_mono _ _ _ (add_le_add hp le_rfl))
end models

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] in
theorem polyTowerGraph_eval (P : ArithmeticSemiterm Empty n) (t : V) (e : Fin n → V) :
    (polyTowerGraph P).Eval (t :> e) Empty.elim ↔
      towerGraph.val.Evalb ![t,P.val e Empty.elim] := by
  have hv : (fun i : Fin 2 => Semiterm.val (t :> e) Empty.elim (![ #0, Rew.bShift P] i)) =
      ![t,P.val e Empty.elim] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    simp
  simpa [polyTowerGraph, Function.comp_def] using
    congrArg (fun v => towerGraph.val.Eval v Empty.elim) hv

theorem PRA_proves_polyTower_domination (P : ArithmeticSemiterm Empty n) :
    PRA ⊢ dominates (polyTowerGraph P) (polyTowerTerm P) := by
  apply dominates_of_val
  intro M _ _ _ _ t e h
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  rw [Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard] at h
  have hg := (polyTowerGraph_eval P t e).mp h
  have ht := towerGraph_candidate t (P.val e Empty.elim) hg
  have hv := polyTowerTerm_val P e
  rw [Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]
  simp [Semiformula.Operator.val, Semiformula.Operator.LE.sentence_eq,
    Semiformula.Operator.Eq.sentence_eq, ht, hv]

#print axioms PRA_proves_polyTower_domination
#print axioms polyTowerTerm_mono
#print axioms polyTowerGraph_eval
end PA196PRAQVecTowerPolynomial
