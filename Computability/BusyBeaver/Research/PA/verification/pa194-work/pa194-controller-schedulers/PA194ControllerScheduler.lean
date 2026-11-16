import PA194ModelFairness
import ConPACtlSchedulerHalts
import PA194ControllerSchedulerCore

/-!
# Schedulers for the command controllers

The candidates of the PA194 family use several command controllers. On a store
`⟪t, w, d, h⟫` with `b = d + y`:

| Protocol | Successful MP returns | SHIFT halts when |
| --- | --- | --- |
| primary PA194 | `⟪b, cantor 0 w, b, 0⟫` | `t + h = 1` |
| PA194N | `⟪b, w, b, 0⟫` | `t + h = 1` |
| PA194C, PA194CS | `⟪0, w, 0, b⟫` | `h = 1` |
| PA194H, PA194HS | `⟪b, w, b, 0⟫` | `h = 1` |

SHIFT without a halt, the failing MP (`⟪0, w, b, 0⟫`) and the numerical calculus are the same
in all four. AX has two layouts. In the ten-entry layout it leaves its gate on top, pushes the
eight leaves, the generalization and the old top, and clears `d`; a command of the stream has
three fields. In the eleven-entry layout of PA194AX11 it also pushes the gate, leaves the top
`0` and sets `d` to a fourth field `z` of the command:
`⟪0, [G, q₁, …, q₈, U(d, h), t; w], z, 0⟫`.

This file defines, for every kind `k` of successful MP, every choice `ct` of the halting test
and every AX layout `a` (`true` for eleven entries), a scheduler by PRA codes, and proves in
every candidate-PRA model `M` whose arithmetic reduct satisfies `𝗜𝚺₁`:

* `stepK_eq`: the step code is `ConPA.Ctl.sstep (semK k ct a)`;
* `G_of_provable`: a target proof of `r` gives a command word that computes `r`;
* `runK_sound`: top, cache and all stack entries stay provable in the numerical calculus
  along every run from a sound state;
* `halts_iff_provable`: the scheduler halts at some time of `M` exactly when the numerical
  calculus proves the contradiction code `1`;
* `halts_iff_primary`: exactly when the modeled scheduler of the primary table halts.

The schedulers are definitions at the level of commands. No connection with a literal table
or with a source program is proved or used.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194ControllerScheduler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194NumeralCode PA194TargetCantor
 PA194TargetStep PA194TargetExtendedStep PA194MachineProjections PA194MachineStack PA194MachineAXCode
 PA194MachineShiftMPCode PA194SchedulerCode PA194StackCode PA194BranchSeed PA194TargetProofLeaf
 PA194TargetLeaves PA194TargetGate PA194SchedulerIteration PA194SchedulerHaltCode PA194ModelFairness
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open ConPA.Ctl (MPKind mpStore)

/-- The third and fourth fields of a command `⟪tag, y, x, z⟫`. -/
noncomputable def cX4 : Code 2 := fst (snd (snd (.proj 0)))
noncomputable def cZ4 : Code 2 := snd (snd (snd (.proj 0)))

/-- The store step as a code of a command and a store. -/
noncomputable def cstepCodeK (k : MPKind) (a : Bool) : Code 2 :=
  bin pairCode
    (choose0 cTag sH (choose1 cTag (mpTopK k sT sH sD cY) (axTopA a cA sD sH cY cX4)))
    (bin pairCode
      (choose0 cTag (shiftStack sW)
        (choose1 cTag (mpStackK k sT sW sH sD cY) (axStackA a sT cA sD sH cY cX4 sW)))
      (bin pairCode
        (choose0 cTag sD (choose1 cTag (mpDK k sT sH sD cY) (axDA a cZ4)))
        (choose0 cTag (shiftCache sW) (choose1 cTag (mpHK k sT sH sD cY) (.zero 2)))))

/-- The halt bit after a number of steps from the initial state. -/
noncomputable def haltAfterK (k : MPKind) (ct a : Bool) : Code 1 :=
  unary (haltAtK ct) (bin (runK k a) (.proj 0) initialConstant)

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

theorem mpFail_model {n : Nat} (t h d x : Code n) (e : Fin n → M) :
    F (mpFail t h d x) e =
      if impValue (F t e) (F d e + F x e) = F h e then 0 else F d e + F x e := by
  simp only [mpFail, mpMatches, modelChooseEqual, machineImp_model, mpArg, add_model,
    PRAMultiplication.modelZero]
  by_cases he : impValue (F t e) (F d e + F x e) = F h e
  · simp [he]
    rfl
  · simp [he]

theorem shiftHaltC_correct {n : Nat} (h : Code n) (e : Fin n → M) :
    F (shiftHaltC h) e = 1 ↔ F h e = 1 := by
  rw [shiftHaltC, modelBin, modelNumeralCode]
  simp only [Nat.cast_one]
  change F equalityCode ![F h e, 1] = F oneCode Fin.elim0 ↔ _
  exact (modelEqualityCode (F h e) (1 : M)).2

theorem cX4_model (c σ : M) : F cX4 ![c, σ] = π₁ (π₂ (π₂ c)) := by
  rw [cX4, fst_model, snd_model, snd_model, modelProjection]
  rfl
theorem cZ4_model (c σ : M) : F cZ4 ![c, σ] = π₂ (π₂ (π₂ c)) := by
  rw [cZ4, snd_model, snd_model, snd_model, modelProjection]
  rfl
theorem zArg_model (s : M) :
    F (zArg fN fL) ![s] =
      first (second (second (second (ConPA.Words.seed (π₁ s) (π₁ (π₂ s)))))) := by
  rw [zArg, unary_bracket, tail3_model, fixedFirst_model]
theorem tail4_model (s : M) :
    F (tail4 fN fL) ![s] =
      second (second (second (second (ConPA.Words.seed (π₁ s) (π₁ (π₂ s)))))) := by
  rw [tail4, unary_bracket, tail3_model, fixedSecond_model]

/-- The AX label depends only on the tag of the command. -/
theorem cA_cmdL (a : Bool) (s σ : M) :
    F cA ![ConPA.Ctl.cmdL a s, σ] = F cA ![ConPA.Words.cmd s, σ] := by
  simp only [cA, modelUnary, cTag_model, ConPA.Ctl.cmdL, ConPA.Words.cmd, pi₁_pair]

/-- The store step, component by component. The command is `⟪tag, y, x, z⟫`. -/
theorem cstepK_eval (k : MPKind) (a : Bool) (c σ : M) :
    F (cstepCodeK k a) ![c, σ] =
      pair (if π₁ c = 0 then π₂ (π₂ (π₂ σ)) else if π₁ c = 1 then
          (match k with
            | .cache => 0
            | _ => if impValue (π₁ σ) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ c)) = π₂ (π₂ (π₂ σ)) then
                π₁ (π₂ (π₂ σ)) + π₁ (π₂ c) else 0)
        else
          (match a with
            | true => 0
            | false => axTop (π₂ (π₂ (π₂ σ)) + π₁ (π₂ c)) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ (π₂ c)))
                (F cA ![c, σ])))
      (pair (if π₁ c = 0 then second (π₁ (π₂ σ)) else if π₁ c = 1 then
          (match k with
            | .push => if impValue (π₁ σ) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ c)) = π₂ (π₂ (π₂ σ)) then
                cantor 0 (π₁ (π₂ σ)) else π₁ (π₂ σ)
            | _ => π₁ (π₂ σ))
        else
          (match a with
            | true => cantor
                (axTop (π₂ (π₂ (π₂ σ)) + π₁ (π₂ c)) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ (π₂ c)))
                  (F cA ![c, σ]))
                (axStack (π₁ (π₂ (π₂ σ)) + π₁ (π₂ (π₂ c))) (π₂ (π₂ (π₂ σ)) + π₁ (π₂ c))
                  (F cA ![c, σ]) (π₁ (π₂ (π₂ σ))) (π₂ (π₂ (π₂ σ))) (π₁ σ) (π₁ (π₂ σ)))
            | false => axStack (π₁ (π₂ (π₂ σ)) + π₁ (π₂ (π₂ c))) (π₂ (π₂ (π₂ σ)) + π₁ (π₂ c))
                (F cA ![c, σ]) (π₁ (π₂ (π₂ σ))) (π₂ (π₂ (π₂ σ))) (π₁ σ) (π₁ (π₂ σ))))
      (pair (if π₁ c = 0 then π₁ (π₂ (π₂ σ)) else if π₁ c = 1 then
          (match k with
            | .cache => if impValue (π₁ σ) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ c)) = π₂ (π₂ (π₂ σ)) then
                0 else π₁ (π₂ (π₂ σ)) + π₁ (π₂ c)
            | _ => π₁ (π₂ (π₂ σ)) + π₁ (π₂ c))
          else
            (match a with
              | true => π₂ (π₂ (π₂ c))
              | false => 0))
        (if π₁ c = 0 then first (π₁ (π₂ σ)) else if π₁ c = 1 then
          (match k with
            | .cache => if impValue (π₁ σ) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ c)) = π₂ (π₂ (π₂ σ)) then
                π₁ (π₂ (π₂ σ)) + π₁ (π₂ c) else 0
            | _ => 0)
          else 0))) := by
  cases k <;> cases a <;>
  · simp only [cstepCodeK, mpTopK, mpStackK, mpDK, mpHK, axTopA, axStackA, axDA, modelBin,
      modelPairCode, choose0_model, choose1_model, mpTop_model, mpStack_model, mpFail_model,
      axTop_model, axStack_model, pair_model, mpArg, shiftStack, shiftCache, unary_bracket,
      fixedFirst_model, fixedSecond_model, cTag_model, cY_model, cX4_model, cZ4_model,
      sT_model, sW_model, sD_model, sH_model, PRAMultiplication.modelZero]
    rfl

theorem cstepK_defined (k : MPKind) (a : Bool) :
    𝚺₁-Function₂ (fun c σ : M => F (cstepCodeK k a) ![c, σ]) via
      (PA194CodeGraph.graph (cstepCodeK k a)) :=
  .mk fun v => by
    have h := PA194CodeGraph.modelGraph (M := M) (cstepCodeK k a)
    have he : (fun i : Fin 2 => v i.succ) = ![v 1, v 2] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
    rw [h.df v]
    show v 0 = F (cstepCodeK k a) (fun x => v x.succ) ↔ v 0 = F (cstepCodeK k a) ![v 1, v 2]
    rw [he]

/-! ## The command semantics -/

noncomputable def semK (k : MPKind) (ct a : Bool) : ConPA.Ctl.Sem M where
  cstep := fun c σ => F (cstepCodeK k a) ![c, σ]
  cstepDef := PA194CodeGraph.graph (cstepCodeK k a)
  cstep_defined := cstepK_defined k a
  mp := k
  cacheTest := ct
  ax11 := a
  axT := fun H D A => axTop H D A
  leaf := leafM
  genL := fun _ d => d
  shift_eq := by
    intro y x t w d h
    rw [cstepK_eval]
    simp
  mp_eq := by
    intro y x t w d h
    rw [cstepK_eval]
    cases k <;> by_cases hm : 4 * cantor t (d + y) = h <;> simp [impValue, hm, mpStore]
  ax_eq := by
    intro A y x z t w d h
    rw [cstepK_eval, cA_model]
    cases a <;> simp [axStack, ConPA.Ctl.stack10, leafM, allValue, impValue]
  axT_ne_one := axTop_ne_one
  leaf_ne_one := leafM_ne_one
  genL_self := fun _ => rfl

/-! ## The scheduler step -/

theorem sstep_unfold (k : MPKind) (ct a : Bool) (s : M) :
    ConPA.Ctl.sstep (semK k ct a) s =
      pair (if π₁ (π₂ s) = 0 then π₁ s + 1 else π₁ s)
        (pair (ConPA.Ctl.nextLL a (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))
          (F (cstepCodeK k a)
            ![ConPA.Ctl.cmdL a (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))), π₂ (π₂ s)])) :=
  rfl

/-- The step code is the scheduler step of `ConPA.Ctl` for the semantics `semK k ct a`. -/
theorem stepK_eq (k : MPKind) (ct a : Bool) (s : M) :
    F (stepK k a) ![s] = ConPA.Ctl.sstep (semK k ct a) s := by
  have hsucc : F (unary Code.succ fN) ![s] = π₁ s + 1 := by
    rw [modelUnary, fN_model, modelSucc]
  have hcmd1 : π₁ (ConPA.Ctl.cmdL a (ConPA.Words.seed (π₁ s) (π₁ (π₂ s)))) =
      first (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))) := by simp [ConPA.Ctl.cmdL]
  have hcmd2 : π₁ (π₂ (ConPA.Ctl.cmdL a (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))) =
      first (second (ConPA.Words.seed (π₁ s) (π₁ (π₂ s)))) := by simp [ConPA.Ctl.cmdL]
  have hcmd3 : π₁ (π₂ (π₂ (ConPA.Ctl.cmdL a (ConPA.Words.seed (π₁ s) (π₁ (π₂ s)))))) =
      first (second (second (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))) := by
    simp [ConPA.Ctl.cmdL]
  have hcmd4 : π₂ (π₂ (π₂ (ConPA.Ctl.cmdL a (ConPA.Words.seed (π₁ s) (π₁ (π₂ s)))))) =
      if a then first (second (second (second (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))))
      else 0 := by
    simp [ConPA.Ctl.cmdL]
  rw [sstep_unfold, cstepK_eval, hcmd1, hcmd2, hcmd3, hcmd4, cA_cmdL]
  cases k <;> cases a <;>
  · simp only [stepK, pack_model, PA194SchedulerCode.nextN, nextLA, PA194SchedulerCode.nextL,
      nextTopK, nextStackK, nextDK, nextCacheK, zField, mpTopK, mpStackK, mpDK, mpHK, axTopA,
      axStackA, axDA, choose0_model, choose1_model, mpTop_model, mpStack_model, mpFail_model,
      axTop_model, axStack_model, pair_model, mpArg, shiftStack, shiftCache, unary_bracket,
      fixedFirst_model, fixedSecond_model, add_model, fN_model, fL_model, fT_model, fW_model,
      fD_model, fH_model, head_model, tail_model, yArg_model, tail2_model, xArg_model,
      tail3_model, zArg_model, tail4_model, axArg_model, hsucc, PRAMultiplication.modelZero,
      ConPA.Ctl.nextLL, Bool.false_eq_true, if_true, if_false]
    rfl

theorem haltAtK_iff (k : MPKind) (ct a : Bool) (s : M) :
    F (haltAtK ct) ![s] = 1 ↔ ConPA.Ctl.shalt (semK k ct a) s := by
  cases ct
  · have h := haltAt_iff s
    have e : ConPA.Ctl.shalt (semK k false a) s ↔ ConPA.Words.shalt s := by
      unfold ConPA.Ctl.shalt ConPA.Words.shalt ConPA.Ctl.Sem.Halts ConPA.Ctl.Sem.k
      simp only [semK, Bool.false_eq_true, if_false, Nat.cast_one, one_mul]
      exact Iff.rfl
    simpa only [haltAtK, Bool.false_eq_true, if_false] using h.trans e.symm
  · unfold ConPA.Ctl.shalt ConPA.Ctl.Sem.Halts ConPA.Ctl.Sem.k
    simp only [haltAtK, semK, if_true, Nat.cast_zero, zero_mul, zero_add]
    rw [choose0_model, head_model]
    by_cases h0 : first (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))) = 0
    · rw [if_pos h0, shiftHaltC_correct, fH_model]
      exact ⟨fun h => ⟨h0, h⟩, fun h => h.2⟩
    · rw [if_neg h0, PRAMultiplication.modelZero]
      constructor
      · intro h
        exact absurd h (zero_ne_one (α := M))
      · intro h
        exact absurd h.1 h0

theorem runK_base (k : MPKind) (a : Bool) (s : M) : F (runK k a) ![0, s] = s :=
  modelDropBase (stepK k a) s

theorem runK_succ (k : MPKind) (a : Bool) (n s : M) :
    F (runK k a) ![n + 1, s] = F (stepK k a) ![F (runK k a) ![n, s]] := by
  rw [runK, modelDropStep]
  have hv : (fun _ : Fin 1 => F (dropCode (stepK k a)) ![n, s]) =
      ![F (dropCode (stepK k a)) ![n, s]] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv]

theorem runK_definable (k : MPKind) (a : Bool) :
    𝚺₁-Function₂ (fun n x : M => F (runK k a) ![n, x]) := by
  have h : 𝚺₁.DefinableFunction (fun e : Fin 2 → M => F (runK k a) e) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) (runK k a))
  convert h using 1
  funext e
  exact congrArg (fun e : Fin 2 → M => F (runK k a) e) (Matrix.fun_eq_vec_two e).symm

/-- The run of the scheduler. -/
noncomputable def runKR (k : MPKind) (ct a : Bool) : ConPA.Ctl.Run M (semK k ct a) where
  run := fun n x => F (runK k a) ![n, x]
  run_definable := runK_definable k a
  run_zero := fun x => runK_base k a x
  run_succ := fun n x => by rw [runK_succ, stepK_eq k ct a]

theorem haltAfterK_model (k : MPKind) (ct a : Bool) (n : M) :
    F (haltAfterK k ct a) ![n] =
      F (haltAtK ct) ![F (runK k a) ![n, F initial Fin.elim0]] := by
  rw [haltAfterK, modelUnary, modelBin, modelProjection, initialConstant_model]
  simp only [Matrix.cons_val_zero]
  have hv (v : M) : (fun _ : Fin 1 => v) = ![v] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv]

/-! ## Target proofs give command words -/

theorem G_of_provable (k : MPKind) (ct a : Bool) (r : M) (hp : TargetProvable r) :
    ConPA.Ctl.G (semK k ct a) r := by
  obtain ⟨program, hprog⟩ := hp
  refine targetProof_sound (ConPA.Ctl.G (semK k ct a)) (ConPA.Ctl.G_definable (semK k ct a))
    ?_ ?_ ?_ ?_ program r hprog
  · intro x y
    rw [machineHead1_model]
    exact ConPA.Ctl.G_leaf (semK k ct a) 6 (by norm_num) x y 0 0 (by simp)
  · intro label x hx
    exact ConPA.Ctl.G_gen (semK k ct a) label x hx
  · intro x y hx hxy
    exact ConPA.Ctl.G_mp (semK k ct a) x y hx hxy
  · exact
      { head2 := fun x y z => ConPA.Ctl.G_leaf (semK k ct a) 5 (by norm_num) x z y 0 (by simp)
        head3 := fun x y z => ConPA.Ctl.G_leaf (semK k ct a) 4 (by norm_num) x z y 0 (by simp)
        head4 := fun x y z => ConPA.Ctl.G_leaf (semK k ct a) 3 (by norm_num) x z y 0 (by simp)
        head5 := fun x y => ConPA.Ctl.G_leaf (semK k ct a) 2 (by norm_num) x y 0 0 (by simp)
        head6 := fun x y z => ConPA.Ctl.G_leaf (semK k ct a) 1 (by norm_num) x z y 0 (by simp)
        rho8 := fun x y z u hu => ConPA.Ctl.G_leaf (semK k ct a) 7 (by norm_num) x z y u hu
        gate := fun x y z hx hy => by
          have h := ConPA.Ctl.G_axT (semK k ct a) x y z
          have he : (semK k ct a).axT x y z = oldBundleValue x y z := by
            change axTop x y z = _
            unfold axTop
            rw [if_neg]
            rintro (h1 | h1)
            · exact hy h1.symm
            · exact hx h1.symm
          rw [he] at h
          exact h
        diagonal := fun x => ConPA.Ctl.G_leaf (semK k ct a) 0 (by norm_num) 0 0 x 0 (by simp) }

/-- A target proof of the contradiction code makes the scheduler halt. -/
theorem provable_halts (k : MPKind) (ct a : Bool) (h : TargetProvable (1 : M)) :
    ∃ n : M, F (haltAfterK k ct a) ![n] = 1 := by
  obtain ⟨n, hn⟩ := ConPA.Ctl.derivation_halts (runKR k ct a) (⟪0, 0, 0, 0⟫ : M)
    (G_of_provable k ct a 1 h)
  refine ⟨n, ?_⟩
  rw [haltAfterK_model, haltAtK_iff k ct a, initial_eq]
  exact hn

/-! ## Soundness -/

/-- The store step preserves provability of the top, the cache and the stack entries. -/
theorem cstepK_sound (k : MPKind) (a : Bool) (c σ : M)
    (hs : SoundStore (π₁ σ) (π₁ (π₂ σ)) (π₂ (π₂ (π₂ σ)))) :
    SoundStore (π₁ (F (cstepCodeK k a) ![c, σ])) (π₁ (π₂ (F (cstepCodeK k a) ![c, σ])))
      (π₂ (π₂ (π₂ (F (cstepCodeK k a) ![c, σ])))) := by
  rw [cstepK_eval]
  simp only [pi₁_pair, pi₂_pair]
  by_cases h0 : π₁ c = 0
  · simp only [if_pos h0]
    have h := PA194MachineStack.shift_preserves _ _ _ hs
    rwa [fixedSecond_model, fixedFirst_model] at h
  · by_cases h1 : π₁ c = 1
    · simp only [if_neg h0, if_pos h1]
      obtain ⟨ht, hh, hw⟩ := hs
      by_cases hm : impValue (π₁ σ) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ c)) = π₂ (π₂ (π₂ σ))
      · rw [← hm] at hh
        have hb := PA194TargetVectorJoin.mp_closed _ _ ht hh
        cases k
        · simp only [if_pos hm]
          exact ⟨hb, zero_provable, push_sound TargetProvable 0 _ zero_provable hw⟩
        · simp only [if_pos hm]
          exact ⟨hb, zero_provable, hw⟩
        · simp only [if_pos hm]
          exact ⟨zero_provable, hb, hw⟩
      · cases k
        · simp only [if_neg hm]
          exact ⟨zero_provable, zero_provable, hw⟩
        · simp only [if_neg hm]
          exact ⟨zero_provable, zero_provable, hw⟩
        · simp only [if_neg hm]
          exact ⟨zero_provable, zero_provable, hw⟩
    · simp only [if_neg h0, if_neg h1]
      have h := ax_preserves (π₁ σ) (π₁ (π₂ σ)) (π₂ (π₂ (π₂ σ))) (π₁ (π₂ (π₂ σ)))
        (π₁ (π₂ (π₂ c))) (π₁ (π₂ c)) (F cA ![c, σ]) hs
      cases a
      · exact h
      · exact ⟨zero_provable, zero_provable, push_sound TargetProvable _ _ h.1 h.2.2⟩

theorem stepK_sound (k : MPKind) (a : Bool) (s : M) (hs : SoundPacked s) :
    SoundPacked (F (stepK k a) ![s]) := by
  unfold SoundPacked at hs ⊢
  rw [fT_model, fW_model, fH_model] at hs ⊢
  rw [stepK_eq k false a, sstep_unfold]
  simp only [pi₂_pair]
  exact cstepK_sound k a _ _ hs

theorem runK_def (k : MPKind) (a : Bool) (s : M) :
    𝚺₁-Function₁ (fun n : M => F (runK k a) ![n, s]) :=
  unary_from_binary _ s (runK_definable k a)

theorem runK_sound (k : MPKind) (a : Bool) (s n : M) (hs : SoundPacked s) :
    SoundPacked (F (runK k a) ![n, s]) := by
  haveI := soundPacked_def (M := M)
  haveI := runK_def k a s
  have hp : 𝚺₁-Predicate (fun n : M => SoundPacked (F (runK k a) ![n, s])) := by definability
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact hp
  | zero => rw [runK_base]; exact hs
  | succ n ih => rw [runK_succ]; exact stepK_sound k a _ ih

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
theorem halt_provable (k : MPKind) (ct a : Bool) (s : M) (hs : SoundPacked s)
    (hh : ConPA.Ctl.shalt (semK k ct a) s) : TargetProvable (1 : M) := by
  unfold SoundPacked at hs
  rw [fT_model, fW_model, fH_model] at hs
  obtain ⟨ht, hc, _⟩ := hs
  have h2 := hh.2
  unfold ConPA.Ctl.Sem.Halts ConPA.Ctl.Sem.k at h2
  cases ct
  · simp only [semK, Bool.false_eq_true, if_false, Nat.cast_one, one_mul] at h2
    rcases one_of_add_eq_one h2 with (h1 | h1)
    · rwa [h1] at ht
    · rwa [h1] at hc
  · simp only [semK, if_true, Nat.cast_zero, zero_mul, zero_add] at h2
    rwa [h2] at hc

/-- A halt of the scheduler gives a target proof of the contradiction code. -/
theorem halts_provable (k : MPKind) (ct a : Bool) (n : M)
    (hh : F (haltAfterK k ct a) ![n] = 1) : TargetProvable (1 : M) := by
  rw [haltAfterK_model, haltAtK_iff k ct a] at hh
  exact halt_provable k ct a _ (runK_sound k a _ n initial_sound) hh

/-- The scheduler halts exactly when the calculus proves the contradiction code. -/
theorem halts_iff_provable (k : MPKind) (ct a : Bool) :
    (∃ n : M, F (haltAfterK k ct a) ![n] = 1) ↔ TargetProvable (1 : M) :=
  ⟨fun ⟨n, hn⟩ => halts_provable k ct a n hn, provable_halts k ct a⟩

/-- The scheduler halts exactly when the modeled scheduler of the primary table halts. -/
theorem halts_iff_primary (k : MPKind) (ct a : Bool) :
    (∃ n : M, F (haltAfterK k ct a) ![n] = 1) ↔ ∃ n : M, F haltAfter ![n] = 1 :=
  (halts_iff_provable k ct a).trans PA194ModelFairness.halts_iff_provable.symm

#print axioms stepK_eq
#print axioms G_of_provable
#print axioms runK_sound
#print axioms halts_iff_provable
#print axioms halts_iff_primary
end models
end PA194ControllerScheduler
