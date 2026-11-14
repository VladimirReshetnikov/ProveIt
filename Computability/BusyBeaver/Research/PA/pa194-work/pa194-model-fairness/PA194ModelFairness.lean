import PA194SchedulerHaltCode
import ConPASchedulerHalts

/-!
# The modeled PA194 scheduler halts on every target proof of code 1

This file instantiates `ConPA.Words.derivation_halts` with the objects of the PA194
development, in every candidate-PRA model `M` whose arithmetic reduct satisfies `𝗜𝚺₁`:

* `semM`: the command semantics, with the store step given by one PRA code `cstepCode`
  assembled from the codes of `PA194MachineShiftMPCode` and `PA194MachineAXCode`;
* `step_eq`: the modeled scheduler step `PA194SchedulerIteration.step` is `ConPA.Words.sstep`;
* `G_of_provable`: `TargetProvable r` implies that some command word computes `r`, by
  `PA194TargetProofLeaf.targetProof_sound` and the closure lemmas of `ConPACommandClosure`;
* `provable_halts : TargetProvable 1 → ∃ k, F haltAfter ![k] = 1`.

Together with `PA194SchedulerIteration.initial_run_halt_provable` this gives
`halts_iff_provable`: the modeled scheduler halts at some model time exactly when the
numerical calculus has a target proof of the contradiction code.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelFairness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194NumeralCode PA194TargetCantor
 PA194TargetStep PA194TargetExtendedStep PA194MachineProjections PA194MachineStack PA194MachineAXCode
 PA194MachineShiftMPCode PA194SchedulerCode PA194StackCode PA194BranchSeed PA194TargetProofLeaf
 PA194TargetLeaves PA194TargetGate PA194SchedulerIteration PA194SchedulerHaltCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

/-! ## The store step as a code of a command and a store -/

noncomputable def cTag : Code 2 := fst (.proj 0)
noncomputable def cY : Code 2 := fst (snd (.proj 0))
noncomputable def cX : Code 2 := snd (snd (.proj 0))
noncomputable def sT : Code 2 := fst (.proj 1)
noncomputable def sW : Code 2 := fst (snd (.proj 1))
noncomputable def sD : Code 2 := fst (snd (snd (.proj 1)))
noncomputable def sH : Code 2 := snd (snd (snd (.proj 1)))
noncomputable def cA : Code 2 := unary predCode (unary predCode cTag)

noncomputable def cstepCode : Code 2 :=
  bin pairCode
    (choose0 cTag sH (choose1 cTag (mpTop sT sH sD cY) (axTopCode cA sD sH cY cX)))
    (bin pairCode
      (choose0 cTag (shiftStack sW)
        (choose1 cTag (mpStack sT sW sH sD cY) (axStackCode sT cA sD sH cY cX sW)))
      (bin pairCode
        (choose0 cTag sD (choose1 cTag (mpArg sD cY) (.zero 2)))
        (choose0 cTag (shiftCache sW) (.zero 2))))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem unary_bracket {n : Nat} (f : Code 1) (a : Code n) (e : Fin n → M) :
    F (unary f a) e = F f ![F a e] := by
  rw [modelUnary]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem cTag_model (c σ : M) : F cTag ![c, σ] = π₁ c := by
  rw [cTag, fst_model, modelProjection]
  rfl
theorem cY_model (c σ : M) : F cY ![c, σ] = π₁ (π₂ c) := by
  rw [cY, fst_model, snd_model, modelProjection]
  rfl
theorem cX_model (c σ : M) : F cX ![c, σ] = π₂ (π₂ c) := by
  rw [cX, snd_model, snd_model, modelProjection]
  rfl
theorem sT_model (c σ : M) : F sT ![c, σ] = π₁ σ := by
  rw [sT, fst_model, modelProjection]
  rfl
theorem sW_model (c σ : M) : F sW ![c, σ] = π₁ (π₂ σ) := by
  rw [sW, fst_model, snd_model, modelProjection]
  rfl
theorem sD_model (c σ : M) : F sD ![c, σ] = π₁ (π₂ (π₂ σ)) := by
  rw [sD, fst_model, snd_model, snd_model, modelProjection]
  rfl
theorem sH_model (c σ : M) : F sH ![c, σ] = π₂ (π₂ (π₂ σ)) := by
  rw [sH, snd_model, snd_model, snd_model, modelProjection]
  rfl

theorem cA_model (A y x σ : M) : F cA ![⟪A + 1 + 1, y, x⟫, σ] = A := by
  rw [cA, modelUnary, modelUnary, cTag_model, pi₁_pair, modelPredAddOne, modelPredAddOne]

theorem cstep_eval (c σ : M) :
    F cstepCode ![c, σ] =
      pair (if π₁ c = 0 then π₂ (π₂ (π₂ σ)) else if π₁ c = 1 then
          (if impValue (π₁ σ) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ c)) = π₂ (π₂ (π₂ σ)) then
            π₁ (π₂ (π₂ σ)) + π₁ (π₂ c) else 0)
        else axTop (π₂ (π₂ (π₂ σ)) + π₁ (π₂ c)) (π₁ (π₂ (π₂ σ)) + π₂ (π₂ c)) (F cA ![c, σ]))
      (pair (if π₁ c = 0 then second (π₁ (π₂ σ)) else if π₁ c = 1 then
          (if impValue (π₁ σ) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ c)) = π₂ (π₂ (π₂ σ)) then
            cantor 0 (π₁ (π₂ σ)) else π₁ (π₂ σ))
        else axStack (π₁ (π₂ (π₂ σ)) + π₂ (π₂ c)) (π₂ (π₂ (π₂ σ)) + π₁ (π₂ c)) (F cA ![c, σ])
          (π₁ (π₂ (π₂ σ))) (π₂ (π₂ (π₂ σ))) (π₁ σ) (π₁ (π₂ σ)))
      (pair (if π₁ c = 0 then π₁ (π₂ (π₂ σ)) else if π₁ c = 1 then
          π₁ (π₂ (π₂ σ)) + π₁ (π₂ c) else 0)
        (if π₁ c = 0 then first (π₁ (π₂ σ)) else 0))) := by
  simp only [cstepCode, modelBin, modelPairCode, choose0_model, choose1_model, mpTop_model,
    mpStack_model, axTop_model, axStack_model, mpArg, shiftStack, shiftCache, unary_bracket,
    fixedFirst_model, fixedSecond_model, cTag_model, cY_model, cX_model, sT_model,
    sW_model, sD_model, sH_model, PRAMultiplication.modelZero]
  rfl

theorem cstep_defined :
    𝚺₁-Function₂ (fun c σ : M => F cstepCode ![c, σ]) via (PA194CodeGraph.graph cstepCode) :=
  .mk fun v => by
    have h := PA194CodeGraph.modelGraph (M := M) cstepCode
    have he : (fun i : Fin 2 => v i.succ) = ![v 1, v 2] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
    rw [h.df v]
    show v 0 = F cstepCode (fun x => v x.succ) ↔ v 0 = F cstepCode ![v 1, v 2]
    rw [he]

/-! ## The command semantics -/

/-- The eight leaf formulas pushed by AX, top first. -/
noncomputable def leafM (i : ℕ) (D H A d : M) : M :=
  match i with
  | 0 => diagonalValue A
  | 1 => head6Value D A H
  | 2 => head5Value D H
  | 3 => head4Value D A H
  | 4 => head3Value D A H
  | 5 => head2Value D A H
  | 6 => head1Value D H
  | 7 => rho8Value D A H d
  | _ => 0

theorem four_mul_ne_one (x : M) : 4 * x ≠ 1 := by
  intro h
  rcases zero_or_succ x with (rfl | ⟨y, rfl⟩)
  · simp at h
  · have h4 : (4 : M) ≤ 4 * (y + 1) := by
      rw [mul_add, mul_one]
      exact le_add_of_nonneg_left (by simp)
    rw [h] at h4
    exact absurd h4 (by norm_num)

theorem axTop_ne_one (H D A : M) : axTop H D A ≠ 1 := by
  unfold axTop
  split
  · simp
  · exact four_mul_ne_one _

theorem leafM_ne_one (i : ℕ) (D H A d : M) : leafM i D H A d ≠ 1 := by
  unfold leafM
  split
  · exact four_mul_ne_one _
  · exact four_mul_ne_one _
  · exact four_mul_ne_one _
  · exact four_mul_ne_one _
  · exact four_mul_ne_one _
  · exact four_mul_ne_one _
  · exact four_mul_ne_one _
  · exact four_mul_ne_one _
  · simp

noncomputable def semM : ConPA.Words.Sem M where
  cstep := fun c σ => F cstepCode ![c, σ]
  cstepDef := PA194CodeGraph.graph cstepCode
  cstep_defined := cstep_defined
  axT := fun H D A => axTop H D A
  leaf := leafM
  shift_eq := by
    intro y x t w d h
    rw [cstep_eval]
    simp
  mp_eq := by
    intro y x t w d h
    rw [cstep_eval]
    by_cases hm : 4 * cantor t (d + y) = h
    · simp [impValue, hm]
    · simp [impValue, hm]
  ax_eq := by
    intro A y x t w d h
    rw [cstep_eval, cA_model]
    simp [axStack, ConPA.Words.stack10, leafM, allValue, impValue]
  axT_ne_one := axTop_ne_one
  leaf_ne_one := leafM_ne_one

/-! ## The scheduler step -/

theorem pred_of_ne_zero (l : M) (hl : l ≠ 0) : F predCode (fun _ => l) = l - 1 := by
  rcases zero_or_succ l with (rfl | ⟨k, rfl⟩)
  · exact absurd rfl hl
  · rw [modelPredAddOne]
    simp

theorem fN_model (s : M) : F fN ![s] = π₁ s := by
  rw [fN, fst_model, modelProjection]
  rfl
theorem fL_model (s : M) : F fL ![s] = π₁ (π₂ s) := by
  rw [fL, fst_model, snd_model, modelProjection]
  rfl
theorem fT_model (s : M) : F fT ![s] = π₁ (π₂ (π₂ s)) := by
  rw [fT, fst_model, snd_model, snd_model, modelProjection]
  rfl
theorem fW_model (s : M) : F fW ![s] = π₁ (π₂ (π₂ (π₂ s))) := by
  rw [fW, fst_model, snd_model, snd_model, snd_model, modelProjection]
  rfl
theorem fD_model (s : M) : F fD ![s] = π₁ (π₂ (π₂ (π₂ (π₂ s)))) := by
  rw [fD, fst_model, snd_model, snd_model, snd_model, snd_model, modelProjection]
  rfl
theorem fH_model (s : M) : F fH ![s] = π₂ (π₂ (π₂ (π₂ (π₂ s)))) := by
  rw [fH, snd_model, snd_model, snd_model, snd_model, snd_model, modelProjection]
  rfl

theorem fetchSeed_model (s : M) :
    F (fetchSeed fN fL) ![s] = ConPA.Words.seed (π₁ s) (π₁ (π₂ s)) := by
  rw [fetchSeed, choose0_model, fL_model, fN_model, ConPA.Words.seed]
  by_cases hl : π₁ (π₂ s) = 0
  · rw [if_pos hl, if_pos hl]
  · rw [if_neg hl, if_neg hl, modelUnary, fL_model, pred_of_ne_zero _ hl]

theorem head_model (s : M) :
    F (head fN fL) ![s] = first (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))) := by
  rw [head, unary_bracket, fetchSeed_model, fixedFirst_model]
theorem tail_model (s : M) :
    F (PA194SchedulerCode.tail fN fL) ![s] = second (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))) := by
  rw [PA194SchedulerCode.tail, unary_bracket, fetchSeed_model, fixedSecond_model]
theorem yArg_model (s : M) :
    F (yArg fN fL) ![s] = first (second (ConPA.Words.seed (π₁ s) (π₁ (π₂ s)))) := by
  rw [yArg, unary_bracket, tail_model, fixedFirst_model]
theorem tail2_model (s : M) :
    F (tail2 fN fL) ![s] = second (second (ConPA.Words.seed (π₁ s) (π₁ (π₂ s)))) := by
  rw [tail2, unary_bracket, tail_model, fixedSecond_model]
theorem xArg_model (s : M) :
    F (xArg fN fL) ![s] = first (second (second (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))) := by
  rw [xArg, unary_bracket, tail2_model, fixedFirst_model]
theorem tail3_model (s : M) :
    F (tail3 fN fL) ![s] =
      second (second (second (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))) := by
  rw [tail3, unary_bracket, tail2_model, fixedSecond_model]

theorem axArg_model (s : M) :
    F (axArg fN fL) ![s] =
      F cA ![ConPA.Words.cmd (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))), π₂ (π₂ s)] := by
  rw [axArg, modelUnary, modelUnary, head_model, cA, modelUnary, modelUnary, cTag_model,
    ConPA.Words.cmd, pi₁_pair]

/-- The modeled scheduler step is the step of `ConPA.Words`. -/
theorem step_eq (s : M) : F PA194SchedulerIteration.step ![s] = ConPA.Words.sstep semM s := by
  have hsucc : F (unary Code.succ fN) ![s] = π₁ s + 1 := by
    rw [modelUnary, fN_model, modelSucc]
  have hcmd1 : π₁ (ConPA.Words.cmd (ConPA.Words.seed (π₁ s) (π₁ (π₂ s)))) =
      first (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))) := by simp [ConPA.Words.cmd]
  have hcmd2 : π₁ (π₂ (ConPA.Words.cmd (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))) =
      first (second (ConPA.Words.seed (π₁ s) (π₁ (π₂ s)))) := by simp [ConPA.Words.cmd]
  have hcmd3 : π₂ (π₂ (ConPA.Words.cmd (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))) =
      first (second (second (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))) := by simp [ConPA.Words.cmd]
  unfold ConPA.Words.sstep
  change _ = pair _ (pair _ (F cstepCode ![_, _]))
  rw [cstep_eval, hcmd1, hcmd2, hcmd3]
  simp only [PA194SchedulerIteration.step, pack_model, PA194SchedulerCode.nextN, PA194SchedulerCode.nextL, nextTop, nextStack,
    nextD, nextCache, choose0_model, choose1_model, mpTop_model, mpStack_model, axTop_model,
    axStack_model, mpArg, shiftStack, shiftCache, unary_bracket, fixedFirst_model,
    fixedSecond_model, add_model, fN_model, fL_model, fT_model, fW_model, fD_model, fH_model,
    head_model, tail_model, yArg_model, tail2_model, xArg_model, tail3_model, axArg_model, hsucc,
    PRAMultiplication.modelZero, ConPA.Words.nextL]
  rfl

theorem haltAt_iff (s : M) : F haltAt ![s] = 1 ↔ ConPA.Words.shalt s := by
  rw [haltAt, halt, choose0_model, head_model]
  unfold ConPA.Words.shalt
  by_cases h0 : first (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))) = 0
  · rw [if_pos h0, shiftHalt_correct, fT_model, fH_model]
    exact ⟨fun h => ⟨h0, h⟩, fun h => h.2⟩
  · rw [if_neg h0, PRAMultiplication.modelZero]
    constructor
    · intro h
      exact absurd h (zero_ne_one (α := M))
    · intro h
      exact absurd h.1 h0

/-- The run of the modeled scheduler. -/
noncomputable def runM : ConPA.Words.Run M semM where
  run := fun k x => F run ![k, x]
  run_definable := by
    have h : 𝚺₁.DefinableFunction (fun e : Fin 2 → M => F run e) :=
      HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) run)
    convert h using 1
    funext e
    exact congrArg (fun e : Fin 2 → M => F run e) (Matrix.fun_eq_vec_two e).symm
  run_zero := fun x => run_base x
  run_succ := fun k x => by rw [PA194SchedulerIteration.run_succ, step_eq]

/-! ## Target proofs give command words -/

theorem G_of_provable (r : M) (hp : TargetProvable r) : ConPA.Words.G semM r := by
  obtain ⟨program, hprog⟩ := hp
  refine targetProof_sound (ConPA.Words.G semM) (ConPA.Words.G_definable semM) ?_ ?_ ?_ ?_
    program r hprog
  · intro a b
    rw [machineHead1_model]
    exact ConPA.Words.G_leaf semM 6 (by norm_num) a b 0 0 (by simp)
  · intro label a ha
    exact ConPA.Words.G_gen semM label a ha
  · intro a b ha hab
    exact ConPA.Words.G_mp semM a b ha hab
  · exact
      { head2 := fun a b c => ConPA.Words.G_leaf semM 5 (by norm_num) a c b 0 (by simp)
        head3 := fun a b c => ConPA.Words.G_leaf semM 4 (by norm_num) a c b 0 (by simp)
        head4 := fun a b c => ConPA.Words.G_leaf semM 3 (by norm_num) a c b 0 (by simp)
        head5 := fun a b => ConPA.Words.G_leaf semM 2 (by norm_num) a b 0 0 (by simp)
        head6 := fun a b c => ConPA.Words.G_leaf semM 1 (by norm_num) a c b 0 (by simp)
        rho8 := fun a b c u hu => ConPA.Words.G_leaf semM 7 (by norm_num) a c b u hu
        gate := fun a b c ha hb => by
          have h := ConPA.Words.G_axT semM a b c
          have he : semM.axT a b c = oldBundleValue a b c := by
            change axTop a b c = _
            unfold axTop
            rw [if_neg]
            rintro (h1 | h1)
            · exact hb h1.symm
            · exact ha h1.symm
          rw [he] at h
          exact h
        diagonal := fun a => ConPA.Words.G_leaf semM 0 (by norm_num) 0 0 a 0 (by simp) }

theorem initial_eq : F initial Fin.elim0 = (⟪2, 0, ⟪0, 0, 0, 0⟫⟫ : M) := by
  simp only [initial, pack_model, modelNumeralCode]
  norm_num
  rfl

/-- **A target proof of the contradiction code makes the modeled scheduler halt.** -/
theorem provable_halts (h : TargetProvable (1 : M)) : ∃ k : M, F haltAfter ![k] = 1 := by
  obtain ⟨k, hk⟩ := ConPA.Words.derivation_halts runM (⟪0, 0, 0, 0⟫ : M) (G_of_provable 1 h)
  refine ⟨k, ?_⟩
  rw [haltAfter_model, haltAt_iff, initial_eq]
  exact hk

/-- The modeled scheduler halts exactly when the calculus proves the contradiction code. -/
theorem halts_iff_provable : (∃ k : M, F haltAfter ![k] = 1) ↔ TargetProvable (1 : M) :=
  ⟨fun ⟨k, hk⟩ => modeled_halt_provable k hk, provable_halts⟩

#print axioms G_of_provable
#print axioms provable_halts
#print axioms halts_iff_provable
end models
end PA194ModelFairness
