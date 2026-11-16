import PA194PausedSites

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

namespace PA194PausedFirstHit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourcePCBound PA194FiniteControls
open PA194IteratedSimulation PA194ClockInvariantDefinable PA194PausedReach

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

/-- A fixed point remains fixed for every model-valued iteration length. -/
theorem iterate_fixed (code : Code 1) (target : M) (fixed : F code ![target] = target) :
    ∀ n : M, F (iterate code) ![n,target] = target := by
  haveI : 𝚺₁-Function₁ (fun k : M => F (iterate code) ![k,target]) :=
    bindBinary _ _ (binaryCodeDef (iterate code))
  have hp : 𝚺₁-Predicate (fun n : M => F (iterate code) ![n,target] = target) := by
    definability
  intro n
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact hp
  | zero => exact iterateZero code target
  | succ n ih => rw [iterateSucc,ih,fixed]

/-- A reachable endpoint of a code frozen at its exit is exactly the first
actual exit, at some model-valued time. -/
theorem first_actual_exit (paused : Code 1) (exit : Nat) (start target : M)
    (pauseLaw : ∀ s : M, F paused ![s] =
      if F pc ![s] = modelNumeral M exit then s else F step ![s])
    (atExit : F pc ![target] = modelNumeral M exit)
    (reached : PA194PausedReach.Reaches paused start target) :
    ∃ n : M, F (iterate step) ![n,start] = target ∧
      ∀ j < n, F pc ![F (iterate step) ![j,start]] ≠ modelNumeral M exit := by
  obtain ⟨w,hw⟩ := reached
  let q : M → Prop := fun n => F pc ![F (iterate paused) ![n,start]] = modelNumeral M exit
  have he (s : M) : F pc ![s] = pi₁ s := by
    rw [PA194SourceControllerCode.pc]
    convert PackedDecoderModel.modelDecodeLeft s using 1
    apply congrArg (fun e : Fin 1 → M => F PackedClock.decodeLeft e)
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  haveI : 𝚺₁-Function₁ (fun k : M => F (iterate paused) ![k,start]) :=
    bindBinary _ _ (binaryCodeDef (iterate paused))
  haveI : 𝚺₁-Function₁ (fun k : M => F (iterate step) ![k,start]) :=
    bindBinary _ _ (binaryCodeDef (iterate step))
  have hq : 𝚺₁-Predicate q := by
    unfold q
    simp_rw [he]
    definability
  have qw : q w := by dsimp [q]; rw [hw]; exact atExit
  obtain ⟨n,hn,hprior⟩ := InductionOnHierarchy.least_number_sigma 𝚺 1 (P := q) hq qw
  have hnw : n ≤ w := by
    by_contra h
    exact hprior w (lt_of_not_ge h) qw
  have hp : 𝚺₁-Predicate (fun k : M => k ≤ n →
      F (iterate step) ![k,start] = F (iterate paused) ![k,start]) := by
    definability
  have same : ∀ k : M, k ≤ n → F (iterate step) ![k,start] = F (iterate paused) ![k,start] := by
    intro k
    induction k using ISigma1.sigma1_succ_induction with
    | hP => exact hp
    | zero => intro _; rw [iterateZero,iterateZero]
    | succ k ih =>
      intro hk
      have hklt : k < n := lt_of_lt_of_le (lt_add_one k) hk
      have hkle : k ≤ n := le_trans (le_add_of_nonneg_right (show (0:M) ≤ 1 from zero_le)) hk
      have hprev := ih hkle
      have hlive : F pc ![F (iterate paused) ![k,start]] ≠ modelNumeral M exit := hprior k hklt
      rw [iterateSucc,iterateSucc,pauseLaw,if_neg hlive,hprev]
  obtain ⟨d,hd⟩ := le_iff_exists_add.mp hnw
  have hfixed : F paused ![F (iterate paused) ![n,start]] = F (iterate paused) ![n,start] := by
    rw [pauseLaw,if_pos hn]
  have hnTarget : F (iterate paused) ![n,start] = target := by
    rw [hd,PA194ControllerRunAdd.iterateAdd,iterate_fixed paused _ hfixed] at hw
    exact hw
  refine ⟨n,?_,?_⟩
  · rw [same n le_rfl,hnTarget]
  · intro j hj
    rw [same j (le_of_lt hj)]
    exact hprior j hj

#print axioms iterate_fixed
#print axioms first_actual_exit
end models
end PA194PausedFirstHit
