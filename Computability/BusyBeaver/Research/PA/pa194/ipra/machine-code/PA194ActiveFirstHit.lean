import PA194ActivePrefix
import PA194ClockInvariantDefinable
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ActiveFirstHit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRASelectCode PRAModelIOpenPairing
open PA194CumulativeClock PA194ActivePrefix PA194ClockInvariantDefinable ConfigurationStep
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem prefixPredicateDef (a h : M → M) (ha : 𝚺₁-Function₁ a) (hh : 𝚺₁-Function₁ h) :
    𝚺₁-Predicate (fun n : M => a n = 1 ∨ ∃ i, i < n ∧ a i = 1 ∧ h i ≠ 0) := by
  haveI := ha
  haveI := hh
  definability

theorem prefixOrHit (run : Code 2) (hit : Code 1) (seed : M) :
    ∀ n : M, F (active run hit) ![n,seed] = 1 ∨
      ∃ i : M, i < n ∧ F (active run hit) ![i,seed] = 1 ∧ F hit ![F run ![i,seed]] ≠ 0 := by
  let a : M → M := fun n => F (active run hit) ![n,seed]
  let h : M → M := fun n => F hit ![F run ![n,seed]]
  have ha : 𝚺₁-Function₁ a := bindBinary _ seed (binaryCodeDef (M := M) (active run hit))
  have hr : 𝚺₁-Function₁ (fun n : M => F run ![n,seed]) := bindBinary _ seed (binaryCodeDef (M := M) run)
  have hh : 𝚺₁-Function₁ h := composeUnary _ _ (unaryCodeDef (M := M) hit) hr
  have hdef := prefixPredicateDef a h ha hh
  intro n
  change a n = 1 ∨ ∃ i, i < n ∧ a i = 1 ∧ h i ≠ 0
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact hdef
  | zero => left; exact activeZero run hit seed
  | succ n ih =>
    classical
    have hlt : n < n+1 := by exact lt_add_of_pos_right n (Arithmetic.zero_lt_one : (0 : M) < 1)
    by_cases hz : h n = 0
    · have hsame : a (n+1) = a n := by
        dsimp only [a,h] at hz ⊢
        rw [activeSucc,modelSelectAll]
        have hz' : F hit (fun _ => F run ![n,seed]) = F (Code.zero 0) Fin.elim0 := by
          have hv : (fun _ : Fin 1 => F run ![n,seed]) = ![F run ![n,seed]] := by
            funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
          rw [hv]
          exact hz
        simp only [hz',if_true]
      rcases ih with ha | ⟨i,hi,hactive,hithit⟩
      · left; exact hsame.trans ha
      · right; exact ⟨i,lt_trans hi hlt,hactive,hithit⟩
    · rcases ih with ha | ⟨i,hi,hactive,hithit⟩
      · right; exact ⟨n,hlt,ha,hz⟩
      · right; exact ⟨i,lt_trans hi hlt,hactive,hithit⟩

theorem boundedHit (run : Code 2) (hit : Code 1) (seed n : M)
    (ha : F (active run hit) ![n+1,seed] ≠ 1) :
    ∃ i : M, i ≤ n ∧ F (active run hit) ![i,seed] = 1 ∧ F hit ![F run ![i,seed]] ≠ 0 := by
  rcases prefixOrHit run hit seed (n+1) with heq | ⟨i,hi,hactive,hh⟩
  · exact False.elim (ha heq)
  · exact ⟨i,lt_succ_iff_le.mp hi,hactive,hh⟩
theorem hitHasActivePredecessor (run : Code 2) (hit : Code 1) (seed n : M)
    (hh : F hit ![F run ![n,seed]] ≠ 0) :
    ∃ i : M, i ≤ n ∧ F (active run hit) ![i,seed] = 1 ∧ F hit ![F run ![i,seed]] ≠ 0 := by
  rcases prefixOrHit run hit seed n with ha | ⟨i,hi,hactive,hithit⟩
  · exact ⟨n,le_rfl,ha,hh⟩
  · exact ⟨i,le_of_lt hi,hactive,hithit⟩
#print axioms hitHasActivePredecessor
#print axioms prefixPredicateDef
#print axioms prefixOrHit
#print axioms boundedHit
end models
end PA194ActiveFirstHit
