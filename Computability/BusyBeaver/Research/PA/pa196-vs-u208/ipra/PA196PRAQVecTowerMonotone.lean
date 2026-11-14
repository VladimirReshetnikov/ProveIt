import PA196PRAQVecStepMonotone
import PA196PASubstitutionTowerGraph

/-! Candidate-PRA tower monotonicity via induction on open formulas. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PRAQVecTowerMonotone
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenInduction
  PA196PRAQVecTower PA196PRAQVecStepMonotone

noncomputable def seedBody : Semiformula language ℕ 1 :=
  ∼(Semiformula.rel Language.ORing.Rel.lt
    ![.func towerCode ![#0,&1], .func towerCode ![#0,&0]])
noncomputable def indexBody : Semiformula language ℕ 1 :=
  ∼(Semiformula.rel Language.ORing.Rel.lt
    ![.func towerCode ![.func addCode ![&0,#0],&1], .func towerCode ![&0,&1]])

theorem seedBody_open : seedBody.Open := by simp [seedBody, Semiformula.Open]
theorem indexBody_open : indexBody.Open := by simp [indexBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem seedBody_eval (n : M) (e : ℕ → M) :
    seedBody.Eval ![n] e ↔ ¬tower n (e 1) < tower n (e 0) := by
  simp [seedBody, Semiterm.val_func, tower]
  rfl

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem indexBody_eval (k : M) (e : ℕ → M) :
    indexBody.Eval ![k] e ↔ ¬tower (e 0+k) (e 1) < tower (e 0) (e 1) := by
  simp [indexBody, Semiterm.val_func, tower]
  rfl

theorem tower_seed_mono (a b n : M) (hab : a ≤ b) : tower n a ≤ tower n b := by
  let e : ℕ → M := fun i => if i = 0 then a else b
  apply le_of_not_gt
  apply (seedBody_eval n e).mp
  apply modelOpenInduction (M := M) seedBody seedBody_open e
  · apply (seedBody_eval 0 e).mpr
    simpa [e, tower_zero] using (not_lt_of_ge hab)
  · intro t ht
    apply (seedBody_eval (Structure.func (L := language) Code.succ (fun _ => t)) e).mpr
    have hprev : tower t a ≤ tower t b := by
      apply le_of_not_gt
      simpa [e] using (seedBody_eval t e).mp ht
    rw [show Structure.func (L := language) Code.succ (fun _ => t) = t+1 from (modelAddOne t).symm]
    simp only [e, if_pos]
    rw [tower_succ_majorant, tower_succ_majorant]
    exact not_lt_of_ge (majorant_mono hprev)

theorem tower_index_mono (m n seed : M) (hmn : m ≤ n) : tower m seed ≤ tower n seed := by
  obtain ⟨k,rfl⟩ := le_iff_exists_add.mp hmn
  let e : ℕ → M := fun i => if i = 0 then m else seed
  apply le_of_not_gt
  apply (indexBody_eval k e).mp
  apply modelOpenInduction (M := M) indexBody indexBody_open e
  · apply (indexBody_eval 0 e).mpr
    simp [e]
  · intro t ht
    apply (indexBody_eval (Structure.func (L := language) Code.succ (fun _ => t)) e).mpr
    have hprev : tower m seed ≤ tower (m+t) seed := by
      apply le_of_not_gt
      simpa [e] using (indexBody_eval t e).mp ht
    rw [show Structure.func (L := language) Code.succ (fun _ => t) = t+1 from (modelAddOne t).symm]
    simp only [e, if_pos]
    rw [show m+(t+1) = (m+t)+1 by ring, tower_succ_majorant]
    exact not_lt_of_ge (le_trans hprev (majorant_increases _))
set_option linter.unusedSectionVars false in
theorem towerTerm_val (e : Fin 1 → M) :
    PA196PASubstitutionTowerGraph.towerTerm.val e Empty.elim = tower (e 0+2) (4*e 0+1) := by
  simp [PA196PASubstitutionTowerGraph.towerTerm, tower, Semiterm.val_func,
    PRAWitnessTransfer.val_lMap_std]

theorem towerTerm_mono : PRAWitnessCalculus.Mono M
    (fun e : Fin 1 → M => PA196PASubstitutionTowerGraph.towerTerm.val e Empty.elim) := by
  intro e e' h
  change PA196PASubstitutionTowerGraph.towerTerm.val e Empty.elim ≤
    PA196PASubstitutionTowerGraph.towerTerm.val e' Empty.elim
  rw [towerTerm_val, towerTerm_val]
  exact le_trans (tower_seed_mono _ _ _ (add_le_add (mul_le_mul' le_rfl (h 0)) le_rfl))
    (tower_index_mono _ _ _ (add_le_add (h 0) le_rfl))
end models
#print axioms towerTerm_mono
#print axioms tower_seed_mono
#print axioms tower_index_mono
end PA196PRAQVecTowerMonotone
