import PA194ModelFairness
import ConPACtlSchedulerHalts

/-!
# The scheduler with the no-push modus ponens

The controller of PA194N differs from the controller of the primary PA194 table in one
command: on a store `⟪t, w, d, h⟫` with `b = d + y`, a successful MP returns `⟪b, w, b, 0⟫`
instead of `⟪b, cantor 0 w, b, 0⟫`. SHIFT, AX, the failing MP, the fetch and decoding of
commands, and the numerical calculus are unchanged.

This file defines that scheduler by PRA codes and proves, in every candidate-PRA model `M`
whose arithmetic reduct satisfies `𝗜𝚺₁`:

* `stepN_eq`: the step code `stepN` is `ConPA.Ctl.sstep semN`, where `semN` is the command
  semantics with `push = false`;
* `G_of_provable`: a target proof of `r` gives a command word that computes `r` under the
  no-push semantics (the modus ponens word reserves a zero below its premises);
* `runN_sound`: the invariant `SoundPacked` (top, cache and all stack entries are provable in
  the numerical calculus) holds along every run from a sound state;
* `haltsN_iff_provable`: the scheduler meets a halting SHIFT, at some time of `M`, exactly
  when the numerical calculus proves the contradiction code `1`;
* `haltsN_iff_primary`: this happens exactly when the modeled scheduler of the primary table
  halts.

The scheduler here is a definition at the level of commands. No connection with the literal
PA194N table or with its source program is proved or used.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194NScheduler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194NumeralCode PA194TargetCantor
 PA194TargetStep PA194TargetExtendedStep PA194MachineProjections PA194MachineStack PA194MachineAXCode
 PA194MachineShiftMPCode PA194SchedulerCode PA194StackCode PA194BranchSeed PA194TargetProofLeaf
 PA194TargetLeaves PA194TargetGate PA194SchedulerIteration PA194SchedulerHaltCode PA194ModelFairness
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

/-! ## Codes -/

/-- The store step: `cstepCode` of `PA194ModelFairness` with the stack kept by MP. -/
noncomputable def cstepCodeN : Code 2 :=
  bin pairCode
    (choose0 cTag sH (choose1 cTag (mpTop sT sH sD cY) (axTopCode cA sD sH cY cX)))
    (bin pairCode
      (choose0 cTag (shiftStack sW)
        (choose1 cTag sW (axStackCode sT cA sD sH cY cX sW)))
      (bin pairCode
        (choose0 cTag sD (choose1 cTag (mpArg sD cY) (.zero 2)))
        (choose0 cTag (shiftCache sW) (.zero 2))))

/-- The stack after one scheduler step: MP leaves it unchanged. -/
noncomputable def nextStackN {m : Nat} (n l t w d h : Code m) : Code m :=
  choose0 (head n l) (shiftStack w) (choose1 (head n l) w
    (axStackCode t (axArg n l) d h (yArg n l) (xArg n l) w))

/-- One scheduler step on the packed state `⟪n, l, t, w, d, h⟫`. -/
noncomputable def stepN : Code 1 :=
  pack (PA194SchedulerCode.nextN fN fL) (PA194SchedulerCode.nextL fN fL)
    (nextTop fN fL fT fW fD fH) (nextStackN fN fL fT fW fD fH) (nextD fN fL fD)
    (nextCache fN fL fW)

noncomputable def runN : Code 2 := dropCode stepN

/-- The halt bit after a number of steps from the initial state. -/
noncomputable def haltAfterN : Code 1 := unary haltAt (bin runN (.proj 0) initialConstant)

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

theorem cstepN_eval (c σ : M) :
    F cstepCodeN ![c, σ] =
      pair (if π₁ c = 0 then π₂ (π₂ (π₂ σ)) else if π₁ c = 1 then
          (if impValue (π₁ σ) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ c)) = π₂ (π₂ (π₂ σ)) then
            π₁ (π₂ (π₂ σ)) + π₁ (π₂ c) else 0)
        else axTop (π₂ (π₂ (π₂ σ)) + π₁ (π₂ c)) (π₁ (π₂ (π₂ σ)) + π₂ (π₂ c)) (F cA ![c, σ]))
      (pair (if π₁ c = 0 then second (π₁ (π₂ σ)) else if π₁ c = 1 then π₁ (π₂ σ)
        else axStack (π₁ (π₂ (π₂ σ)) + π₂ (π₂ c)) (π₂ (π₂ (π₂ σ)) + π₁ (π₂ c)) (F cA ![c, σ])
          (π₁ (π₂ (π₂ σ))) (π₂ (π₂ (π₂ σ))) (π₁ σ) (π₁ (π₂ σ)))
      (pair (if π₁ c = 0 then π₁ (π₂ (π₂ σ)) else if π₁ c = 1 then
          π₁ (π₂ (π₂ σ)) + π₁ (π₂ c) else 0)
        (if π₁ c = 0 then first (π₁ (π₂ σ)) else 0))) := by
  simp only [cstepCodeN, modelBin, modelPairCode, choose0_model, choose1_model, mpTop_model,
    axTop_model, axStack_model, mpArg, shiftStack, shiftCache, unary_bracket,
    fixedFirst_model, fixedSecond_model, cTag_model, cY_model, cX_model, sT_model,
    sW_model, sD_model, sH_model, PRAMultiplication.modelZero]
  rfl

theorem cstepN_defined :
    𝚺₁-Function₂ (fun c σ : M => F cstepCodeN ![c, σ]) via (PA194CodeGraph.graph cstepCodeN) :=
  .mk fun v => by
    have h := PA194CodeGraph.modelGraph (M := M) cstepCodeN
    have he : (fun i : Fin 2 => v i.succ) = ![v 1, v 2] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
    rw [h.df v]
    show v 0 = F cstepCodeN (fun x => v x.succ) ↔ v 0 = F cstepCodeN ![v 1, v 2]
    rw [he]

/-! ## The command semantics -/

noncomputable def semN : ConPA.Ctl.Sem M where
  cstep := fun c σ => F cstepCodeN ![c, σ]
  cstepDef := PA194CodeGraph.graph cstepCodeN
  cstep_defined := cstepN_defined
  push := false
  axT := fun H D A => axTop H D A
  leaf := leafM
  shift_eq := by
    intro y x t w d h
    rw [cstepN_eval]
    simp
  mp_eq := by
    intro y x t w d h
    rw [cstepN_eval]
    by_cases hm : 4 * cantor t (d + y) = h
    · simp [impValue, hm]
    · simp [impValue, hm]
  ax_eq := by
    intro A y x t w d h
    rw [cstepN_eval, cA_model]
    simp [axStack, ConPA.Ctl.stack10, leafM, allValue, impValue]
  axT_ne_one := axTop_ne_one
  leaf_ne_one := leafM_ne_one

/-! ## The scheduler step -/

/-- The step code is the scheduler step of `ConPA.Ctl` for the no-push semantics. -/
theorem stepN_eq (s : M) : F stepN ![s] = ConPA.Ctl.sstep semN s := by
  have hsucc : F (unary Code.succ fN) ![s] = π₁ s + 1 := by
    rw [modelUnary, fN_model, modelSucc]
  have hcmd1 : π₁ (ConPA.Words.cmd (ConPA.Words.seed (π₁ s) (π₁ (π₂ s)))) =
      first (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))) := by simp [ConPA.Words.cmd]
  have hcmd2 : π₁ (π₂ (ConPA.Words.cmd (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))) =
      first (second (ConPA.Words.seed (π₁ s) (π₁ (π₂ s)))) := by simp [ConPA.Words.cmd]
  have hcmd3 : π₂ (π₂ (ConPA.Words.cmd (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))) =
      first (second (second (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))) := by simp [ConPA.Words.cmd]
  have hstep : ConPA.Ctl.sstep semN s =
      pair (if π₁ (π₂ s) = 0 then π₁ s + 1 else π₁ s)
        (pair (ConPA.Words.nextL (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))
          (F cstepCodeN ![ConPA.Words.cmd (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))), π₂ (π₂ s)])) :=
    rfl
  rw [hstep, cstepN_eval, hcmd1, hcmd2, hcmd3]
  simp only [stepN, pack_model, PA194SchedulerCode.nextN, PA194SchedulerCode.nextL, nextTop,
    nextStackN, nextD, nextCache, choose0_model, choose1_model, mpTop_model, axTop_model,
    axStack_model, mpArg, shiftStack, shiftCache, unary_bracket, fixedFirst_model,
    fixedSecond_model, add_model, fN_model, fL_model, fT_model, fW_model, fD_model, fH_model,
    head_model, tail_model, yArg_model, tail2_model, xArg_model, tail3_model, axArg_model, hsucc,
    PRAMultiplication.modelZero, ConPA.Words.nextL]
  rfl

theorem haltAt_iffN (s : M) : F haltAt ![s] = 1 ↔ ConPA.Ctl.shalt s :=
  (haltAt_iff s).trans Iff.rfl

theorem runN_base (s : M) : F runN ![0, s] = s := modelDropBase stepN s

theorem runN_succ (k s : M) : F runN ![k + 1, s] = F stepN ![F runN ![k, s]] := by
  rw [runN, modelDropStep]
  have hv : (fun _ : Fin 1 => F (dropCode stepN) ![k, s]) = ![F (dropCode stepN) ![k, s]] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv]

theorem runN_definable : 𝚺₁-Function₂ (fun k x : M => F runN ![k, x]) := by
  have h : 𝚺₁.DefinableFunction (fun e : Fin 2 → M => F runN e) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) runN)
  convert h using 1
  funext e
  exact congrArg (fun e : Fin 2 → M => F runN e) (Matrix.fun_eq_vec_two e).symm

/-- The run of the no-push scheduler. -/
noncomputable def runNR : ConPA.Ctl.Run M semN where
  run := fun k x => F runN ![k, x]
  run_definable := runN_definable
  run_zero := fun x => runN_base x
  run_succ := fun k x => by rw [runN_succ, stepN_eq]

theorem haltAfterN_model (k : M) :
    F haltAfterN ![k] = F haltAt ![F runN ![k, F initial Fin.elim0]] := by
  rw [haltAfterN, modelUnary, modelBin, modelProjection, initialConstant_model]
  simp only [Matrix.cons_val_zero]
  have hv (v : M) : (fun _ : Fin 1 => v) = ![v] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv]

/-! ## Target proofs give command words -/

theorem G_of_provable (r : M) (hp : TargetProvable r) : ConPA.Ctl.G semN r := by
  obtain ⟨program, hprog⟩ := hp
  refine targetProof_sound (ConPA.Ctl.G semN) (ConPA.Ctl.G_definable semN) ?_ ?_ ?_ ?_
    program r hprog
  · intro a b
    rw [machineHead1_model]
    exact ConPA.Ctl.G_leaf semN 6 (by norm_num) a b 0 0 (by simp)
  · intro label a ha
    exact ConPA.Ctl.G_gen semN label a ha
  · intro a b ha hab
    exact ConPA.Ctl.G_mp semN a b ha hab
  · exact
      { head2 := fun a b c => ConPA.Ctl.G_leaf semN 5 (by norm_num) a c b 0 (by simp)
        head3 := fun a b c => ConPA.Ctl.G_leaf semN 4 (by norm_num) a c b 0 (by simp)
        head4 := fun a b c => ConPA.Ctl.G_leaf semN 3 (by norm_num) a c b 0 (by simp)
        head5 := fun a b => ConPA.Ctl.G_leaf semN 2 (by norm_num) a b 0 0 (by simp)
        head6 := fun a b c => ConPA.Ctl.G_leaf semN 1 (by norm_num) a c b 0 (by simp)
        rho8 := fun a b c u hu => ConPA.Ctl.G_leaf semN 7 (by norm_num) a c b u hu
        gate := fun a b c ha hb => by
          have h := ConPA.Ctl.G_axT semN a b c
          have he : semN.axT a b c = oldBundleValue a b c := by
            change axTop a b c = _
            unfold axTop
            rw [if_neg]
            rintro (h1 | h1)
            · exact hb h1.symm
            · exact ha h1.symm
          rw [he] at h
          exact h
        diagonal := fun a => ConPA.Ctl.G_leaf semN 0 (by norm_num) 0 0 a 0 (by simp) }

/-- A target proof of the contradiction code makes the no-push scheduler halt. -/
theorem provable_haltsN (h : TargetProvable (1 : M)) : ∃ k : M, F haltAfterN ![k] = 1 := by
  obtain ⟨k, hk⟩ := ConPA.Ctl.derivation_halts runNR (⟪0, 0, 0, 0⟫ : M) (G_of_provable 1 h)
  refine ⟨k, ?_⟩
  rw [haltAfterN_model, haltAt_iffN, initial_eq]
  exact hk

/-! ## Soundness -/

/-- The store step preserves provability of the top, the cache and the stack entries. -/
theorem cstepN_sound (c σ : M) (hs : SoundStore (π₁ σ) (π₁ (π₂ σ)) (π₂ (π₂ (π₂ σ)))) :
    SoundStore (π₁ (F cstepCodeN ![c, σ])) (π₁ (π₂ (F cstepCodeN ![c, σ])))
      (π₂ (π₂ (π₂ (F cstepCodeN ![c, σ])))) := by
  rw [cstepN_eval]
  simp only [pi₁_pair, pi₂_pair]
  by_cases h0 : π₁ c = 0
  · simp only [if_pos h0]
    have h := PA194MachineStack.shift_preserves _ _ _ hs
    rwa [fixedSecond_model, fixedFirst_model] at h
  · by_cases h1 : π₁ c = 1
    · simp only [if_neg h0, if_pos h1]
      by_cases hm : impValue (π₁ σ) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ c)) = π₂ (π₂ (π₂ σ))
      · simp only [if_pos hm]
        obtain ⟨ht, hh, hw⟩ := hs
        rw [← hm] at hh
        exact ⟨PA194TargetVectorJoin.mp_closed _ _ ht hh, zero_provable, hw⟩
      · simp only [if_neg hm]
        exact mp_failure_preserves _ _ _ hs
    · simp only [if_neg h0, if_neg h1]
      exact ax_preserves _ _ _ _ _ _ _ hs

theorem stepN_sound (s : M) (hs : SoundPacked s) : SoundPacked (F stepN ![s]) := by
  unfold SoundPacked at hs ⊢
  rw [fT_model, fW_model, fH_model] at hs ⊢
  rw [stepN_eq]
  have hstep : ConPA.Ctl.sstep semN s =
      pair (if π₁ (π₂ s) = 0 then π₁ s + 1 else π₁ s)
        (pair (ConPA.Words.nextL (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))
          (F cstepCodeN ![ConPA.Words.cmd (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))), π₂ (π₂ s)])) :=
    rfl
  rw [hstep]
  simp only [pi₂_pair]
  exact cstepN_sound _ _ hs

theorem runN_def (s : M) : 𝚺₁-Function₁ (fun n : M => F runN ![n, s]) :=
  unary_from_binary _ s runN_definable

theorem runN_sound (s k : M) (hs : SoundPacked s) : SoundPacked (F runN ![k, s]) := by
  haveI := soundPacked_def (M := M)
  haveI := runN_def s
  have hp : 𝚺₁-Predicate (fun k : M => SoundPacked (F runN ![k, s])) := by definability
  induction k using ISigma1.sigma1_succ_induction with
  | hP => exact hp
  | zero => rw [runN_base]; exact hs
  | succ k ih => rw [runN_succ]; exact stepN_sound _ ih

theorem one_of_add_eq_one {t h : M} (e : t + h = 1) : t = 1 ∨ h = 1 := by
  rcases zero_or_succ t with (rfl | ⟨u, rfl⟩)
  · right
    simpa using e
  · left
    have e' : u + h + 1 = 0 + 1 := by
      rw [zero_add]
      calc u + h + 1 = u + 1 + h := by ring
        _ = 1 := e
    have e0 : u + h = 0 := add_right_cancel e'
    have hu : u = 0 := (add_eq_zero.mp e0).1
    rw [hu, zero_add]

/-- A halting SHIFT in a sound state finds a proof of the contradiction code. -/
theorem halt_provable (s : M) (hs : SoundPacked s) (hh : ConPA.Ctl.shalt s) :
    TargetProvable (1 : M) := by
  unfold SoundPacked at hs
  rw [fT_model, fW_model, fH_model] at hs
  obtain ⟨ht, hc, _⟩ := hs
  rcases one_of_add_eq_one hh.2 with (h1 | h1)
  · rwa [h1] at ht
  · rwa [h1] at hc

/-- A halt of the no-push scheduler gives a target proof of the contradiction code. -/
theorem haltsN_provable (k : M) (hh : F haltAfterN ![k] = 1) : TargetProvable (1 : M) := by
  rw [haltAfterN_model, haltAt_iffN] at hh
  exact halt_provable _ (runN_sound _ k initial_sound) hh

/-- The no-push scheduler halts exactly when the calculus proves the contradiction code. -/
theorem haltsN_iff_provable : (∃ k : M, F haltAfterN ![k] = 1) ↔ TargetProvable (1 : M) :=
  ⟨fun ⟨k, hk⟩ => haltsN_provable k hk, provable_haltsN⟩

/-- The no-push scheduler halts exactly when the modeled scheduler of the primary table
halts. -/
theorem haltsN_iff_primary :
    (∃ k : M, F haltAfterN ![k] = 1) ↔ ∃ k : M, F haltAfter ![k] = 1 :=
  haltsN_iff_provable.trans halts_iff_provable.symm

#print axioms stepN_eq
#print axioms G_of_provable
#print axioms runN_sound
#print axioms haltsN_iff_provable
#print axioms haltsN_iff_primary
end models
end PA194NScheduler
