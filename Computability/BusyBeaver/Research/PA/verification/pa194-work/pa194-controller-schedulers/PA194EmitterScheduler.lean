import PA194ControllerScheduler
import PA194EmitterSchedulerCore
import PA194ModelContext
import ConPAGenericCalculus

/-!
# Schedulers with a variant axiom emitter

Other candidates change entries of the AX command. Six changes are independent of each
other, of the command protocol and of the AX layout (`PA194EmitterSchedulerCore.Emitter`):

* `gd`: the separate diagonal is `Γ(D)` instead of `Γ(A)` (PA194D, PA194DHS, the GD family);
* `q`: the premises of the sixth head are exchanged (the Q, QH, QN families, PA194G, PA194GH);
* `x`: the fifth head is `W(D,H) → A` instead of `W(D,H) → 1` (PA194H5X);
* `ga`: the generalization is `U(A, h)` instead of `U(d, h)` (the G, GH, GD families);
* `bundled`: no diagonal is pushed and the gate is `¬(Γ(A) → (V → Q))` instead of
  `¬(V → Q)` (the original PA195);
* `delta`: no diagonal is pushed and the gate is `¬(Δ → (V → Q))` with the equality vacuity
  `Δ = E(H,D) → U(A, E(H,D))` (PA196).

Completeness, for every emitter (`provable_halts`). A proof of the contradiction code in the
calculus of the primary table (`TargetProvable`) gives a halting command word. The formulas
that the scheduler computes are closed under the rules and contain the restricted row and
the heads (`closedG`), so the laws of `ConPA.Calc` hold for them. Exchange gives the sixth
head back; the fifth head is `W → A` at `A = 1`; the generalization word of the primary
emitter uses an AX whose label argument equals the register `d`, so it works for both
binders. From a gate `¬(Y → X)` the gate `¬X` follows. `Γ(B)` is the diagonal entry of an
AX with `D = A = B`; or it follows from the gate `¬(Γ(B) → X)` with the arguments
`(B + 1, B + 1, B)`; or, with the equality vacuity, the gate gives the vacuity of both kinds
of atoms at fresh labels (`atomVacG`) and `ConPA.Calc.diagonal` gives `Γ(B)` for every code.

Soundness, for an arbitrary invariant. `Sound P e` says that the predicate `P` is
`Σ₁`-definable, closed under the rules, and contains the heads, the diagonals and the gate
of the primary calculus, and the equality vacuity if `e.delta`. Then every entry and the
gate of the AX of `e` are in `P`, the invariant that top, cache and stack entries are in `P`
is preserved along a run, and a halt puts the contradiction code in `P` (`halts_in`).
`TargetProvable` is such an invariant when `e.delta = false` (`soundTarget`), which gives

* `halts_iff_provable`: the scheduler halts at some time of the model exactly when the
  numerical calculus proves the contradiction code `1`;
* `halts_iff_primary`: exactly when the modeled scheduler of the primary table halts.

For every emitter, `PA194EmitterSchedulerPA` uses the invariant "arithmetic proves the
translation".

The schedulers are definitions at the level of commands. No connection with a literal table
or with a source program is proved or used.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194EmitterScheduler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194NumeralCode PA194TargetCantor
 PA194TargetStep PA194TargetExtendedStep PA194MachineProjections PA194MachineStack PA194MachineAXCode
 PA194MachineShiftMPCode PA194SchedulerCode PA194StackCode PA194BranchSeed PA194TargetProofLeaf
 PA194TargetLeaves PA194TargetGate PA194SchedulerIteration PA194SchedulerHaltCode PA194ModelFairness
 PA194ControllerScheduler
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open ConPA.Ctl (MPKind mpStore)

/-- The store step as a code of a command and a store. -/
noncomputable def cstepCodeE (e : Emitter) (k : MPKind) (a : Bool) : Code 2 :=
  bin pairCode
    (choose0 cTag sH (choose1 cTag (mpTopK k sT sH sD cY) (axTopEA e a cA sD sH cY cX4)))
    (bin pairCode
      (choose0 cTag (shiftStack sW)
        (choose1 cTag (mpStackK k sT sW sH sD cY) (axStackEA e a sT cA sD sH cY cX4 sW)))
      (bin pairCode
        (choose0 cTag sD (choose1 cTag (mpDK k sT sH sD cY) (axDA a cZ4)))
        (choose0 cTag (shiftCache sW) (choose1 cTag (mpHK k sT sH sD cY) (.zero 2)))))

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

/-! ## The entries of the variant AX -/

/-- `U(D, A → H) → (U(D, A) → U(D, H))`. -/
noncomputable def head6QValue (d a h : M) : M :=
  impValue (allValue d (impValue a h)) (impValue (allValue d a) (allValue d h))

/-- `W(D, H) → A` with `W(D, H) = U(D, E(H, D) → 1)`. -/
noncomputable def head5XValue (d a h : M) : M :=
  impValue (allValue d (negValue (eqValue h d))) a

/-- `¬(Γ(c) → (V(a,b,c) → Q(a,b,c)))`. -/
noncomputable def bundledGateValue (a b c : M) : M :=
  negValue (impValue (diagonalValue c)
    (impValue (memVacValue a b c) (separationTailValue a b c)))

/-- The eight leaf formulas of an AX that pushes its diagonal, top first. -/
noncomputable def baseLeaf (e : Emitter) (i : ℕ) (D H A d : M) : M :=
  match i with
  | 0 => diagonalValue (if e.gd then D else A)
  | 1 => if e.q then head6QValue D A H else head6Value D A H
  | 2 => if e.x then head5XValue D A H else head5Value D H
  | 3 => head4Value D A H
  | 4 => head3Value D A H
  | 5 => head2Value D A H
  | 6 => head1Value D H
  | 7 => rho8Value D A H d
  | _ => 0

/-- The seven leaf formulas of an AX that does not push a diagonal. -/
noncomputable def shiftLeaf (e : Emitter) (i : ℕ) (D H A d : M) : M :=
  match i with
  | 0 => baseLeaf e 1 D H A d
  | 1 => baseLeaf e 2 D H A d
  | 2 => baseLeaf e 3 D H A d
  | 3 => baseLeaf e 4 D H A d
  | 4 => baseLeaf e 5 D H A d
  | 5 => baseLeaf e 6 D H A d
  | 6 => baseLeaf e 7 D H A d
  | _ => 0

/-- `¬((E(a,b) → U(c, E(a,b))) → (V(a,b,c) → Q(a,b,c)))`. -/
noncomputable def deltaGateValue (a b c : M) : M :=
  negValue (impValue (impValue (eqValue a b) (allValue c (eqValue a b)))
    (impValue (memVacValue a b c) (separationTailValue a b c)))

/-- The leaf formulas pushed by AX, top first. -/
noncomputable def leafE (e : Emitter) (i : ℕ) (D H A d : M) : M :=
  if (e.bundled || e.delta) then shiftLeaf e i D H A d else baseLeaf e i D H A d

/-- The label of the generalization. -/
noncomputable def genLE (e : Emitter) (A d : M) : M := if e.ga then A else d

/-- The stack entries of AX. -/
noncomputable def axStackE (e : Emitter) (D H A d h t w : M) : M :=
  ConPA.Ctl.stackS (e.bundled || e.delta) (fun i => leafE e i D H A d)
    (allValue (genLE e A d) h) t w

/-- The bundled gate with its guard. -/
noncomputable def axTopB (H D A : M) : M :=
  if D = A ∨ H = A then 0 else bundledGateValue H D A

/-- The gate with the equality vacuity, with its guard. -/
noncomputable def axTopD (H D A : M) : M :=
  if D = A ∨ H = A then 0 else deltaGateValue H D A

/-- The gate of AX with its guard. -/
noncomputable def axTopE (e : Emitter) (H D A : M) : M :=
  if e.delta then axTopD H D A else if e.bundled then axTopB H D A else axTop H D A

theorem head6Q_model (d a h : M) : F head6Q ![d,a,h] = head6QValue d a h := by
  simp only [head6Q,machineImp_model,machineAll_model,modelProjection,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def,
    head6QValue]
  all_goals rfl

theorem head5X_model (d a h : M) : F head5X ![d,a,h] = head5XValue d a h := by
  simp only [head5X,machineImp_model,machineAll_model,machineNeg_model,eq_model,modelProjection,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
    Function.comp_def,head5XValue]
  all_goals rfl

theorem bundledGate_model (a b c : M) : F bundledGate ![a,b,c] = bundledGateValue a b c := by
  have hdiag : F (unary diagonal (Code.proj (2 : Fin 3))) ![a,b,c] = diagonalValue c := by
    rw [modelUnary, modelProjection]
    have hv : (fun _ : Fin 1 => (![a,b,c] : Fin 3 → M) 2) = ![c] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv, diagonal_model]
  simp only [bundledGate, machineNeg_model, machineImp_model, memVac_model,
    separationTail_model, hdiag, bundledGateValue]

theorem deltaGate_model (a b c : M) : F deltaGate ![a,b,c] = deltaGateValue a b c := by
  simp only [deltaGate, machineNeg_model, machineImp_model, machineAll_model, eq_model,
    memVac_model, separationTail_model, modelProjection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_def, deltaGateValue]
  all_goals rfl

theorem axStackE_model (e : Emitter) {n : Nat} (t A d h y x w : Code n) (env : Fin n → M) :
    F (axStackCodeE e t A d h y x w) env =
      axStackE e (F d env + F x env) (F h env + F y env) (F A env) (F d env) (F h env)
        (F t env) (F w env) := by
  have hdiag (c : M) : F diagonal (fun _ => c) = diagonalValue c := by
    have hv : (fun _ : Fin 1 => c) = ![c] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv, diagonal_model]
  rcases e with ⟨gd, q, x', ga, b, dl⟩
  cases gd <;> cases q <;> cases x' <;> cases ga <;> cases b <;> cases dl <;>
  · simp only [axStackCodeE, diagArg, head6E, head5E, genArg, pair_model, app3_model_pra,
      app4_model_pra, modelUnary, add_model, modelBin, head6_model, head6Q_model, head5_model,
      head5X_model, head4_model, head3_model, head2_model, machineHead1_model, rho8_model,
      machineAll_model, hdiag, axStackE, ConPA.Ctl.stackS, ConPA.Ctl.stack9, ConPA.Ctl.stack10,
      leafE, shiftLeaf, baseLeaf, genLE, Bool.or_false, Bool.or_true, Bool.false_eq_true,
      if_true, if_false]
    all_goals rfl

theorem axTopE_model (e : Emitter) {n : Nat} (A d h y x : Code n) (env : Fin n → M) :
    F (axTopCodeE e A d h y x) env =
      axTopE e (F h env + F y env) (F d env + F x env) (F A env) := by
  rcases e with ⟨gd, q, x', ga, b, dl⟩
  cases dl
  · cases b
    · simp only [axTopCodeE, axTopE, axTop_model, Bool.false_eq_true, ↓reduceIte]
    · simp only [axTopCodeE, axTopE, Bool.false_eq_true, ↓reduceIte, modelChooseEqual,
        PRAMultiplication.modelZero, app3_model_pra, bundledGate_model, add_model, axTopB]
      by_cases hd : F d env + F x env = F A env <;>
        by_cases hh : F h env + F y env = F A env <;> simp [hd, hh] <;> rfl
  · simp only [axTopCodeE, axTopE, ↓reduceIte, modelChooseEqual, PRAMultiplication.modelZero,
      app3_model_pra, deltaGate_model, add_model, axTopD]
    by_cases hd : F d env + F x env = F A env <;> by_cases hh : F h env + F y env = F A env <;>
      simp [hd, hh] <;> rfl

/-- The store step, component by component. The command is `⟪tag, y, x, z⟫`. -/
theorem cstepE_eval (e : Emitter) (k : MPKind) (a : Bool) (c σ : M) :
    F (cstepCodeE e k a) ![c, σ] =
      pair (if π₁ c = 0 then π₂ (π₂ (π₂ σ)) else if π₁ c = 1 then
          (match k with
            | .cache => 0
            | _ => if impValue (π₁ σ) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ c)) = π₂ (π₂ (π₂ σ)) then
                π₁ (π₂ (π₂ σ)) + π₁ (π₂ c) else 0)
        else
          (match a with
            | true => 0
            | false => axTopE e (π₂ (π₂ (π₂ σ)) + π₁ (π₂ c)) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ (π₂ c)))
                (F cA ![c, σ])))
      (pair (if π₁ c = 0 then second (π₁ (π₂ σ)) else if π₁ c = 1 then
          (match k with
            | .push => if impValue (π₁ σ) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ c)) = π₂ (π₂ (π₂ σ)) then
                cantor 0 (π₁ (π₂ σ)) else π₁ (π₂ σ)
            | _ => π₁ (π₂ σ))
        else
          (match a with
            | true => cantor
                (axTopE e (π₂ (π₂ (π₂ σ)) + π₁ (π₂ c)) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ (π₂ c)))
                  (F cA ![c, σ]))
                (axStackE e (π₁ (π₂ (π₂ σ)) + π₁ (π₂ (π₂ c))) (π₂ (π₂ (π₂ σ)) + π₁ (π₂ c))
                  (F cA ![c, σ]) (π₁ (π₂ (π₂ σ))) (π₂ (π₂ (π₂ σ))) (π₁ σ) (π₁ (π₂ σ)))
            | false => axStackE e (π₁ (π₂ (π₂ σ)) + π₁ (π₂ (π₂ c))) (π₂ (π₂ (π₂ σ)) + π₁ (π₂ c))
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
  · simp only [cstepCodeE, mpTopK, mpStackK, mpDK, mpHK, axTopEA, axStackEA, axDA, modelBin,
      modelPairCode, choose0_model, choose1_model, mpTop_model, mpStack_model, mpFail_model,
      axTopE_model, axStackE_model, pair_model, mpArg, shiftStack, shiftCache, unary_bracket,
      fixedFirst_model, fixedSecond_model, cTag_model, cY_model, cX4_model, cZ4_model,
      sT_model, sW_model, sD_model, sH_model, PRAMultiplication.modelZero]
    rfl

theorem cstepE_defined (e : Emitter) (k : MPKind) (a : Bool) :
    𝚺₁-Function₂ (fun c σ : M => F (cstepCodeE e k a) ![c, σ]) via
      (PA194CodeGraph.graph (cstepCodeE e k a)) :=
  .mk fun v => by
    have h := PA194CodeGraph.modelGraph (M := M) (cstepCodeE e k a)
    have he : (fun i : Fin 2 => v i.succ) = ![v 1, v 2] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
    rw [h.df v]
    show v 0 = F (cstepCodeE e k a) (fun x => v x.succ) ↔ v 0 = F (cstepCodeE e k a) ![v 1, v 2]
    rw [he]

theorem baseLeaf_ne_one (e : Emitter) (i : ℕ) (D H A d : M) : baseLeaf e i D H A d ≠ 1 := by
  unfold baseLeaf
  split
  · exact four_mul_ne_one _
  · split <;> exact four_mul_ne_one _
  · split <;> exact four_mul_ne_one _
  · exact four_mul_ne_one _
  · exact four_mul_ne_one _
  · exact four_mul_ne_one _
  · exact four_mul_ne_one _
  · exact four_mul_ne_one _
  · simp

theorem leafE_ne_one (e : Emitter) (i : ℕ) (D H A d : M) : leafE e i D H A d ≠ 1 := by
  unfold leafE
  split
  · unfold shiftLeaf
    split
    · exact baseLeaf_ne_one e _ _ _ _ _
    · exact baseLeaf_ne_one e _ _ _ _ _
    · exact baseLeaf_ne_one e _ _ _ _ _
    · exact baseLeaf_ne_one e _ _ _ _ _
    · exact baseLeaf_ne_one e _ _ _ _ _
    · exact baseLeaf_ne_one e _ _ _ _ _
    · exact baseLeaf_ne_one e _ _ _ _ _
    · simp
  · exact baseLeaf_ne_one e _ _ _ _ _

theorem axTopE_ne_one (e : Emitter) (H D A : M) : axTopE e H D A ≠ 1 := by
  unfold axTopE
  split
  · unfold axTopD
    split
    · simp
    · exact four_mul_ne_one _
  · split
    · unfold axTopB
      split
      · simp
      · exact four_mul_ne_one _
    · exact axTop_ne_one H D A

/-! ## The command semantics -/

noncomputable def semE (e : Emitter) (k : MPKind) (ct a : Bool) : ConPA.Ctl.Sem M where
  cstep := fun c σ => F (cstepCodeE e k a) ![c, σ]
  cstepDef := PA194CodeGraph.graph (cstepCodeE e k a)
  cstep_defined := cstepE_defined e k a
  mp := k
  cacheTest := ct
  ax11 := a
  short := e.bundled || e.delta
  axT := axTopE e
  leaf := leafE e
  genL := genLE e
  shift_eq := by
    intro y x t w d h
    rw [cstepE_eval]
    simp
  mp_eq := by
    intro y x t w d h
    rw [cstepE_eval]
    cases k <;> by_cases hm : 4 * cantor t (d + y) = h <;> simp [impValue, hm, mpStore]
  ax_eq := by
    intro A y x z t w d h
    rw [cstepE_eval, cA_model]
    cases a <;> simp [axStackE, allValue, impValue]
  axT_ne_one := axTopE_ne_one e
  leaf_ne_one := leafE_ne_one e
  genL_self := by
    intro i
    simp [genLE]

/-! ## The scheduler step -/

theorem sstep_unfold (e : Emitter) (k : MPKind) (ct a : Bool) (s : M) :
    ConPA.Ctl.sstep (semE e k ct a) s =
      pair (if π₁ (π₂ s) = 0 then π₁ s + 1 else π₁ s)
        (pair (ConPA.Ctl.nextLL a (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))))
          (F (cstepCodeE e k a)
            ![ConPA.Ctl.cmdL a (ConPA.Words.seed (π₁ s) (π₁ (π₂ s))), π₂ (π₂ s)])) :=
  rfl

/-- The step code is the scheduler step of `ConPA.Ctl` for the semantics `semE e k ct a`. -/
theorem stepE_eq (e : Emitter) (k : MPKind) (ct a : Bool) (s : M) :
    F (stepE e k a) ![s] = ConPA.Ctl.sstep (semE e k ct a) s := by
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
  rw [sstep_unfold, cstepE_eval, hcmd1, hcmd2, hcmd3, hcmd4, cA_cmdL]
  cases k <;> cases a <;>
  · simp only [stepE, pack_model, PA194SchedulerCode.nextN, nextLA, PA194SchedulerCode.nextL,
      nextTopE, nextStackE, nextDK, nextCacheK, zField, mpTopK, mpStackK, mpDK, mpHK, axTopEA,
      axStackEA, axDA, choose0_model, choose1_model, mpTop_model, mpStack_model, mpFail_model,
      axTopE_model, axStackE_model, pair_model, mpArg, shiftStack, shiftCache, unary_bracket,
      fixedFirst_model, fixedSecond_model, add_model, fN_model, fL_model, fT_model, fW_model,
      fD_model, fH_model, head_model, tail_model, yArg_model, tail2_model, xArg_model,
      tail3_model, zArg_model, tail4_model, axArg_model, hsucc, PRAMultiplication.modelZero,
      ConPA.Ctl.nextLL, Bool.false_eq_true, if_true, if_false]
    rfl

theorem haltAtE_iff (e : Emitter) (k : MPKind) (ct a : Bool) (s : M) :
    F (haltAtK ct) ![s] = 1 ↔ ConPA.Ctl.shalt (semE e k ct a) s :=
  (haltAtK_iff k ct a s).trans Iff.rfl

theorem runE_base (e : Emitter) (k : MPKind) (a : Bool) (s : M) :
    F (runE e k a) ![0, s] = s :=
  modelDropBase (stepE e k a) s

theorem runE_succ (e : Emitter) (k : MPKind) (a : Bool) (n s : M) :
    F (runE e k a) ![n + 1, s] = F (stepE e k a) ![F (runE e k a) ![n, s]] := by
  rw [runE, modelDropStep]
  have hv : (fun _ : Fin 1 => F (dropCode (stepE e k a)) ![n, s]) =
      ![F (dropCode (stepE e k a)) ![n, s]] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv]

theorem runE_definable (e : Emitter) (k : MPKind) (a : Bool) :
    𝚺₁-Function₂ (fun n x : M => F (runE e k a) ![n, x]) := by
  have h : 𝚺₁.DefinableFunction (fun v : Fin 2 → M => F (runE e k a) v) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) (runE e k a))
  convert h using 1
  funext v
  exact congrArg (fun v : Fin 2 → M => F (runE e k a) v) (Matrix.fun_eq_vec_two v).symm

/-- The run of the scheduler. -/
noncomputable def runER (e : Emitter) (k : MPKind) (ct a : Bool) :
    ConPA.Ctl.Run M (semE e k ct a) where
  run := fun n x => F (runE e k a) ![n, x]
  run_definable := runE_definable e k a
  run_zero := fun x => runE_base e k a x
  run_succ := fun n x => by rw [runE_succ, stepE_eq e k ct a]

theorem haltAfterE_model (e : Emitter) (k : MPKind) (ct a : Bool) (n : M) :
    F (haltAfterE e k ct a) ![n] =
      F (haltAtK ct) ![F (runE e k a) ![n, F initial Fin.elim0]] := by
  rw [haltAfterE, modelUnary, modelBin, modelProjection, initialConstant_model]
  simp only [Matrix.cons_val_zero]
  have hv (v : M) : (fun _ : Fin 1 => v) = ![v] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv]

/-! ## Target proofs give command words -/

/-- The leaves `1, …, 7` of the eight-leaf list are computed by the scheduler in both
layouts; when no diagonal is pushed they are the leaves `0, …, 6` of AX. -/
theorem G_base (e : Emitter) (k : MPKind) (ct a : Bool) (j : ℕ) (h1 : 1 ≤ j) (h8 : j < 8)
    (D H A d : M) (hd : d ≤ D) : ConPA.Ctl.G (semE e k ct a) (baseLeaf e j D H A d) := by
  cases hb : (e.bundled || e.delta)
  · have hm : j < (semE (M := M) e k ct a).m := by
      show j < (if (e.bundled || e.delta) = true then 7 else 8)
      rw [hb]
      exact h8
    have h : ConPA.Ctl.G (semE e k ct a) (leafE e j D H A d) :=
      ConPA.Ctl.G_leaf (semE e k ct a) j hm D H A d hd
    have e1 : leafE e j D H A d = baseLeaf e j D H A d := by simp [leafE, hb]
    rw [e1] at h
    exact h
  · have hm : j - 1 < (semE (M := M) e k ct a).m := by
      show j - 1 < (if (e.bundled || e.delta) = true then 7 else 8)
      rw [hb]
      show j - 1 < 7
      omega
    have h : ConPA.Ctl.G (semE e k ct a) (leafE e (j - 1) D H A d) :=
      ConPA.Ctl.G_leaf (semE e k ct a) (j - 1) hm D H A d hd
    have e1 : leafE e (j - 1) D H A d = baseLeaf e j D H A d := by
      have e0 : leafE e (j - 1) D H A d = shiftLeaf e (j - 1) D H A d := by simp [leafE, hb]
      rw [e0]
      interval_cases j <;> rfl
    rw [e1] at h
    exact h

/-- The restricted row and modus ponens for the formulas that the scheduler computes. -/
noncomputable def rulesG (e : Emitter) (k : MPKind) (ct a : Bool) :
    M6.Logic.RestrictedImplication.Rules (impValue (M := M)) (· ≤ ·)
      (fun r => PLift (ConPA.Ctl.G (semE e k ct a) r)) where
  mp := fun hab ha => ⟨ConPA.Ctl.G_mp (semE e k ct a) _ _ ha.down hab.down⟩
  row := fun x y z u h => ⟨G_base e k ct a 7 (by norm_num) (by norm_num) x z y u h⟩
  refl := fun x => le_refl x
  boundLeft := fun b h => PA194ModelLogic.le_impValue_left b h
  boundRight := fun b h => PA194ModelLogic.le_impValue_right b h

/-- The sixth head of the primary emitter: directly, or from the exchanged head by the
exchange law. -/
theorem G_head6 (e : Emitter) (k : MPKind) (ct a : Bool) (d x h : M) :
    ConPA.Ctl.G (semE e k ct a) (head6Value d x h) := by
  have h1 := G_base e k ct a 1 (by norm_num) (by norm_num) d h x 0 (by simp)
  cases hq : e.q
  · have e1 : baseLeaf e 1 d h x 0 = head6Value d x h := by simp [baseLeaf, hq]
    rw [e1] at h1
    exact h1
  · have e1 : baseLeaf e 1 d h x 0 = head6QValue d x h := by simp [baseLeaf, hq]
    rw [e1] at h1
    have hex := (M6.Logic.RestrictedImplication.exchange (rulesG e k ct a)
      (allValue d (impValue x h)) (allValue d x) (allValue d h)).down
    exact ConPA.Ctl.G_mp (semE e k ct a) (head6QValue d x h) (head6Value d x h) h1 hex

/-- The fifth head of the primary emitter: the variant head at `A = 1`. -/
theorem G_head5 (e : Emitter) (k : MPKind) (ct a : Bool) (d h : M) :
    ConPA.Ctl.G (semE e k ct a) (head5Value d h) := by
  have h1 := G_base e k ct a 2 (by norm_num) (by norm_num) d h 1 0 (by simp)
  have e1 : baseLeaf e 2 d h 1 0 = head5Value d h := by
    cases hx : e.x <;> simp [baseLeaf, hx, head5XValue, head5Value, exValue, negValue]
  rw [e1] at h1
  exact h1

/-- The formulas that the scheduler computes are closed under the rules of the calculus and
contain the restricted row and the first, second and sixth heads. -/
theorem closedG (e : Emitter) (k : MPKind) (ct a : Bool) :
    ConPA.Calc.Closed (ConPA.Ctl.G (semE (M := M) e k ct a)) where
  mp := fun x y hx hxy => ConPA.Ctl.G_mp (semE e k ct a) x y hx hxy
  gen := fun x y hy => ConPA.Ctl.G_gen (semE e k ct a) x y hy
  row := fun x y z u h => G_base e k ct a 7 (by norm_num) (by norm_num) x z y u h
  h1 := fun d h => G_base e k ct a 6 (by norm_num) (by norm_num) d h 0 0 (by simp)
  h2 := fun d x h => G_base e k ct a 5 (by norm_num) (by norm_num) d h x 0 (by simp)
  h6 := fun d x h => G_head6 e k ct a d x h

/-- The gate of AX under its guard, in the form of the emitter. -/
theorem G_top (e : Emitter) (k : MPKind) (ct a : Bool) (x y z : M) (hx : z ≠ x)
    (hy : z ≠ y) :
    ConPA.Ctl.G (semE e k ct a)
      (if e.delta then deltaGateValue x y z
        else if e.bundled then bundledGateValue x y z else oldBundleValue x y z) := by
  have h : ConPA.Ctl.G (semE e k ct a) (axTopE e x y z) :=
    ConPA.Ctl.G_axT (semE e k ct a) x y z
  have hguard : ¬(y = z ∨ x = z) := by
    rintro (h1 | h1)
    · exact hy h1.symm
    · exact hx h1.symm
  have e1 : axTopE e x y z =
      (if e.delta then deltaGateValue x y z
        else if e.bundled then bundledGateValue x y z else oldBundleValue x y z) := by
    cases hd : e.delta <;> cases hb : e.bundled <;>
      simp [axTopE, hd, hb, axTopD, axTopB, axTop, hguard]
  rw [e1] at h
  exact h

/-- The gate of the primary emitter under its guard: directly, or from a gate `¬(Y → X)`
that bundles a diagonal or an equality vacuity `Y`. -/
theorem G_gate (e : Emitter) (k : MPKind) (ct a : Bool) (x y z : M) (hx : z ≠ x)
    (hy : z ≠ y) : ConPA.Ctl.G (semE e k ct a) (oldBundleValue x y z) := by
  have h := G_top e k ct a x y z hx hy
  cases hd : e.delta
  · cases hb : e.bundled
    · simpa [hd, hb] using h
    · have g : ConPA.Ctl.G (semE e k ct a)
          (negValue (impValue (diagonalValue z)
            (impValue (memVacValue x y z) (separationTailValue x y z)))) := by
        simpa [hd, hb, bundledGateValue] using h
      exact ConPA.Calc.negImpRight (closedG e k ct a) g
  · have g : ConPA.Ctl.G (semE e k ct a)
        (negValue (impValue (impValue (eqValue x y) (allValue z (eqValue x y)))
          (impValue (memVacValue x y z) (separationTailValue x y z)))) := by
      simpa [hd, deltaGateValue] using h
    exact ConPA.Calc.negImpRight (closedG e k ct a) g

/-- With the equality vacuity in the gate, the formulas that the scheduler computes contain
the vacuity of both kinds of atoms at every label different from their labels. -/
theorem atomVacG (e : Emitter) (k : MPKind) (ct a : Bool) (hd : e.delta = true) :
    ConPA.Calc.AtomVac (ConPA.Ctl.G (semE (M := M) e k ct a)) where
  mem := fun x y z hx hy => by
    have h := G_gate e k ct a x y z hx hy
    have g : ConPA.Ctl.G (semE e k ct a)
        (negValue (impValue (impValue (memValue x y) (allValue z (memValue x y)))
          (separationTailValue x y z))) := h
    exact ConPA.Calc.negImpLeft (closedG e k ct a) g
  eq := fun x y z hx hy => by
    have h := G_top e k ct a x y z hx hy
    have g : ConPA.Ctl.G (semE e k ct a)
        (negValue (impValue (impValue (eqValue x y) (allValue z (eqValue x y)))
          (impValue (memVacValue x y z) (separationTailValue x y z)))) := by
      simpa [hd, deltaGateValue] using h
    exact ConPA.Calc.negImpLeft (closedG e k ct a) g

/-- The diagonal `Γ(B)`. With a pushed diagonal it is the first entry of an AX with
`D = A = B`. With the gate `¬(Γ(B) → X)` it follows from the gate with the arguments
`(B + 1, B + 1, B)`. With the equality vacuity in the gate it is the vacuity of the code `B`
at the label `B`, which holds for every code by `ConPA.Calc.diagonal`. -/
theorem G_diagonal (e : Emitter) (k : MPKind) (ct a : Bool) (b : M) :
    ConPA.Ctl.G (semE e k ct a) (diagonalValue b) := by
  cases hd : e.delta
  · cases hb : e.bundled
    · have hs : (e.bundled || e.delta) = false := by simp [hd, hb]
      have hm : 0 < (semE (M := M) e k ct a).m := by
        show 0 < (if (e.bundled || e.delta) = true then 7 else 8)
        rw [hs]
        show 0 < 8
        norm_num
      have h1 : ConPA.Ctl.G (semE e k ct a) (leafE e 0 b 0 b 0) :=
        ConPA.Ctl.G_leaf (semE e k ct a) 0 hm b 0 b 0 (by simp)
      have e1 : leafE e 0 b 0 b 0 = diagonalValue b := by simp [leafE, hs, baseLeaf]
      rw [e1] at h1
      exact h1
    · have hne : b ≠ b + 1 := by simp
      have h := G_top e k ct a (b + 1) (b + 1) b hne hne
      have g : ConPA.Ctl.G (semE e k ct a)
          (negValue (impValue (diagonalValue b)
            (impValue (memVacValue (b + 1) (b + 1) b)
              (separationTailValue (b + 1) (b + 1) b)))) := by
        simpa [hd, hb, bundledGateValue] using h
      exact ConPA.Calc.negImpLeft (closedG e k ct a) g
  · exact ConPA.Calc.diagonal (closedG e k ct a) (ConPA.Ctl.G_definable (semE e k ct a))
      (atomVacG e k ct a hd) b

theorem G_of_provable (e : Emitter) (k : MPKind) (ct a : Bool) (r : M)
    (hp : TargetProvable r) : ConPA.Ctl.G (semE e k ct a) r := by
  obtain ⟨program, hprog⟩ := hp
  refine targetProof_sound (ConPA.Ctl.G (semE e k ct a))
    (ConPA.Ctl.G_definable (semE e k ct a)) ?_ ?_ ?_ ?_ program r hprog
  · intro x y
    rw [machineHead1_model]
    exact G_base e k ct a 6 (by norm_num) (by norm_num) x y 0 0 (by simp)
  · intro label x hx
    exact ConPA.Ctl.G_gen (semE e k ct a) label x hx
  · intro x y hx hxy
    exact ConPA.Ctl.G_mp (semE e k ct a) x y hx hxy
  · exact
      { head2 := fun x y z => G_base e k ct a 5 (by norm_num) (by norm_num) x z y 0 (by simp)
        head3 := fun x y z => G_base e k ct a 4 (by norm_num) (by norm_num) x z y 0 (by simp)
        head4 := fun x y z => G_base e k ct a 3 (by norm_num) (by norm_num) x z y 0 (by simp)
        head5 := fun x y => G_head5 e k ct a x y
        head6 := fun x y z => G_head6 e k ct a x y z
        rho8 := fun x y z u hu => G_base e k ct a 7 (by norm_num) (by norm_num) x z y u hu
        gate := fun x y z hx hy => G_gate e k ct a x y z hx hy
        diagonal := fun x => G_diagonal e k ct a x }

/-- A target proof of the contradiction code makes the scheduler halt. -/
theorem provable_halts (e : Emitter) (k : MPKind) (ct a : Bool) (h : TargetProvable (1 : M)) :
    ∃ n : M, F (haltAfterE e k ct a) ![n] = 1 := by
  obtain ⟨n, hn⟩ := ConPA.Ctl.derivation_halts (runER e k ct a) (⟪0, 0, 0, 0⟫ : M)
    (G_of_provable e k ct a 1 h)
  refine ⟨n, ?_⟩
  rw [haltAfterE_model, haltAtE_iff e k ct a, initial_eq]
  exact hn

/-! ## Soundness, for an arbitrary invariant -/

/-- What the soundness direction needs from a predicate `P` for the emitter `e`: it is
`Σ₁`-definable, closed under the rules, and contains the heads, the diagonals and the gate of
the primary calculus, and the equality vacuity when the gate of `e` contains it. -/
structure Sound (P : M → Prop) (e : Emitter) : Prop where
  definable : 𝚺₁-Predicate P
  closed : ConPA.Calc.Closed P
  h3 : ∀ d a h : M, P (head3Value d a h)
  h4 : ∀ d a h : M, P (head4Value d a h)
  h5 : ∀ d h : M, P (head5Value d h)
  diagonal : ∀ c : M, P (diagonalValue c)
  gate : ∀ a b c : M, c ≠ a → c ≠ b → P (oldBundleValue a b c)
  eqVac : e.delta = true → ∀ a b c : M, c ≠ a → c ≠ b →
    P (impValue (eqValue a b) (allValue c (eqValue a b)))

variable {P : M → Prop}

/-- Every leaf of the eight-leaf list is in `P`. -/
theorem baseLeaf_in {e : Emitter} (R : Sound P e) (i : ℕ) (D H A d : M) (hd : d ≤ D) :
    P (baseLeaf e i D H A d) := by
  unfold baseLeaf
  split
  · exact R.diagonal _
  · split
    · exact R.closed.mp _ _ (R.closed.h6 D A H)
        (R.closed.exchange (allValue D A) (allValue D (impValue A H)) (allValue D H))
    · exact R.closed.h6 D A H
  · split
    · have h5 : P (impValue (allValue D (negValue (eqValue H D))) 1) := R.h5 D H
      exact R.closed.trans h5 (ConPA.Calc.explosion R.closed A)
    · exact R.h5 D H
  · exact R.h4 D A H
  · exact R.h3 D A H
  · exact R.closed.h2 D A H
  · exact R.closed.h1 D H
  · exact R.closed.row D A H d hd
  · exact R.closed.zero

/-- Every leaf of a variant AX is in `P`. -/
theorem leafE_in {e : Emitter} (R : Sound P e) (i : ℕ) (D H A d : M) (hd : d ≤ D) :
    P (leafE e i D H A d) := by
  unfold leafE
  split
  · unfold shiftLeaf
    split
    · exact baseLeaf_in R _ D H A d hd
    · exact baseLeaf_in R _ D H A d hd
    · exact baseLeaf_in R _ D H A d hd
    · exact baseLeaf_in R _ D H A d hd
    · exact baseLeaf_in R _ D H A d hd
    · exact baseLeaf_in R _ D H A d hd
    · exact baseLeaf_in R _ D H A d hd
    · exact R.closed.zero
  · exact baseLeaf_in R i D H A d hd

/-- The gate of a variant AX is in `P`: a bundled gate `¬(Y → X)` from `Y` and `¬X`. -/
theorem axTopE_in {e : Emitter} (R : Sound P e) (H D A : M) : P (axTopE e H D A) := by
  unfold axTopE
  split
  · rename_i hdelta
    unfold axTopD
    split
    · exact R.closed.zero
    · rename_i hguard
      exact ConPA.Calc.negImpIntro R.closed
        (R.eqVac hdelta H D A (fun ha => hguard (Or.inr ha.symm))
          (fun hb => hguard (Or.inl hb.symm)))
        (R.gate H D A (fun ha => hguard (Or.inr ha.symm)) (fun hb => hguard (Or.inl hb.symm)))
  · split
    · unfold axTopB
      split
      · exact R.closed.zero
      · rename_i hguard
        exact ConPA.Calc.negImpIntro R.closed (R.diagonal A)
          (R.gate H D A (fun ha => hguard (Or.inr ha.symm))
            (fun hb => hguard (Or.inl hb.symm)))
    · unfold axTop
      split
      · exact R.closed.zero
      · rename_i hguard
        exact R.gate H D A (fun ha => hguard (Or.inr ha.symm))
          (fun hb => hguard (Or.inl hb.symm))

/-- The invariant of a store: the top, the cache and all stack entries are in `P`. -/
def StoreP (P : M → Prop) (t w h : M) : Prop := P t ∧ P h ∧ SoundStack P w

/-- The variant AX preserves the invariant of the stack. -/
theorem axE_preserves {e : Emitter} (R : Sound P e) (t w h d x y A : M)
    (hs : StoreP P t w h) : SoundStack P (axStackE e (d + x) (h + y) A d h t w) := by
  obtain ⟨ht, hh, hw⟩ := hs
  have hl (i : ℕ) : P (leafE e i (d + x) (h + y) A d) :=
    leafE_in R i (d + x) (h + y) A d le_self_add
  have s0 := push_sound P t w ht hw
  have s1 := push_sound P (allValue (genLE e A d) h) _ (R.closed.gen (genLE e A d) h hh) s0
  have s3 := push_sound P _ _ (hl 6) s1
  have s4 := push_sound P _ _ (hl 5) s3
  have s5 := push_sound P _ _ (hl 4) s4
  have s6 := push_sound P _ _ (hl 3) s5
  have s7 := push_sound P _ _ (hl 2) s6
  have s8 := push_sound P _ _ (hl 1) s7
  have s9 := push_sound P _ _ (hl 0) s8
  have t2 := push_sound P _ _ (hl 7) s1
  have t3 := push_sound P _ _ (hl 6) t2
  have t4 := push_sound P _ _ (hl 5) t3
  have t5 := push_sound P _ _ (hl 4) t4
  have t6 := push_sound P _ _ (hl 3) t5
  have t7 := push_sound P _ _ (hl 2) t6
  have t8 := push_sound P _ _ (hl 1) t7
  have t9 := push_sound P _ _ (hl 0) t8
  unfold axStackE ConPA.Ctl.stackS
  split
  · exact s9
  · exact t9

/-- The store step preserves the invariant. -/
theorem cstepE_sound {e : Emitter} (R : Sound P e) (k : MPKind) (a : Bool) (c σ : M)
    (hs : StoreP P (π₁ σ) (π₁ (π₂ σ)) (π₂ (π₂ (π₂ σ)))) :
    StoreP P (π₁ (F (cstepCodeE e k a) ![c, σ])) (π₁ (π₂ (F (cstepCodeE e k a) ![c, σ])))
      (π₂ (π₂ (π₂ (F (cstepCodeE e k a) ![c, σ])))) := by
  rw [cstepE_eval]
  simp only [pi₁_pair, pi₂_pair]
  have hz : P (0 : M) := R.closed.zero
  by_cases h0 : π₁ c = 0
  · simp only [if_pos h0]
    obtain ⟨ht, hh, hw⟩ := hs
    have hp := pop_sound P hz _ hw
    exact ⟨hh, hp.1, hp.2⟩
  · by_cases h1 : π₁ c = 1
    · simp only [if_neg h0, if_pos h1]
      obtain ⟨ht, hh, hw⟩ := hs
      by_cases hm : impValue (π₁ σ) (π₁ (π₂ (π₂ σ)) + π₁ (π₂ c)) = π₂ (π₂ (π₂ σ))
      · rw [← hm] at hh
        have hb := R.closed.mp _ _ ht hh
        cases k
        · simp only [if_pos hm]
          exact ⟨hb, hz, push_sound P 0 _ hz hw⟩
        · simp only [if_pos hm]
          exact ⟨hb, hz, hw⟩
        · simp only [if_pos hm]
          exact ⟨hz, hb, hw⟩
      · cases k
        · simp only [if_neg hm]
          exact ⟨hz, hz, hw⟩
        · simp only [if_neg hm]
          exact ⟨hz, hz, hw⟩
        · simp only [if_neg hm]
          exact ⟨hz, hz, hw⟩
    · simp only [if_neg h0, if_neg h1]
      have hg := axTopE_in R (π₂ (π₂ (π₂ σ)) + π₁ (π₂ c))
        (π₁ (π₂ (π₂ σ)) + π₁ (π₂ (π₂ c))) (F cA ![c, σ])
      have hst := axE_preserves R (π₁ σ) (π₁ (π₂ σ)) (π₂ (π₂ (π₂ σ))) (π₁ (π₂ (π₂ σ)))
        (π₁ (π₂ (π₂ c))) (π₁ (π₂ c)) (F cA ![c, σ]) hs
      cases a
      · exact ⟨hg, hz, hst⟩
      · exact ⟨hz, hz, push_sound P _ _ hg hst⟩

/-- The invariant of a packed state `⟪n, l, t, w, d, h⟫`. -/
def PackedP (P : M → Prop) (s : M) : Prop := StoreP P (F fT ![s]) (F fW ![s]) (F fH ![s])

theorem packedP_def_generic (hP : 𝚺₁-Predicate P) (ft fw fh : M → M)
    (ht : 𝚺₁-Function₁ ft) (hw : 𝚺₁-Function₁ fw) (hh : 𝚺₁-Function₁ fh) :
    𝚺₁-Predicate (fun s => P (ft s) ∧ P (fh s) ∧ SoundStack P (fw s)) := by
  haveI := ht
  haveI := hw
  haveI := hh
  haveI := hP
  haveI := soundStack_def P hP
  definability

theorem packedP_def (hP : 𝚺₁-Predicate P) : 𝚺₁-Predicate (PackedP (M := M) P) :=
  packedP_def_generic hP _ _ _ (code_unary_def fT) (code_unary_def fW) (code_unary_def fH)

theorem stepE_sound {e : Emitter} (R : Sound P e) (k : MPKind) (a : Bool) (s : M)
    (hs : PackedP P s) : PackedP P (F (stepE e k a) ![s]) := by
  unfold PackedP at hs ⊢
  rw [fT_model, fW_model, fH_model] at hs ⊢
  rw [stepE_eq e k false a, sstep_unfold]
  simp only [pi₂_pair]
  exact cstepE_sound R k a _ _ hs

theorem runE_def (e : Emitter) (k : MPKind) (a : Bool) (s : M) :
    𝚺₁-Function₁ (fun n : M => F (runE e k a) ![n, s]) :=
  unary_from_binary _ s (runE_definable e k a)

theorem runE_sound {e : Emitter} (R : Sound P e) (k : MPKind) (a : Bool) (s n : M)
    (hs : PackedP P s) : PackedP P (F (runE e k a) ![n, s]) := by
  haveI := packedP_def (M := M) R.definable
  haveI := runE_def e k a s
  have hp : 𝚺₁-Predicate (fun n : M => PackedP P (F (runE e k a) ![n, s])) := by definability
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact hp
  | zero => rw [runE_base]; exact hs
  | succ n ih => rw [runE_succ]; exact stepE_sound R k a _ ih

theorem initial_in {e : Emitter} (R : Sound P e) : PackedP P (F initial Fin.elim0) := by
  unfold PackedP initial
  simp only [pack_model, fT, fW, fH, fst_model, snd_model, modelProjection,
    Matrix.cons_val_zero, pi₁_pair, pi₂_pair, PRAMultiplication.modelZero]
  exact ⟨R.closed.zero, R.closed.zero, zero_sound P⟩

/-- A halting SHIFT in a state with the invariant puts the contradiction code in `P`. -/
theorem halt_in (e : Emitter) (k : MPKind) (ct a : Bool) (s : M) (hs : PackedP P s)
    (hh : ConPA.Ctl.shalt (semE e k ct a) s) : P (1 : M) := by
  unfold PackedP at hs
  rw [fT_model, fW_model, fH_model] at hs
  obtain ⟨ht, hc, _⟩ := hs
  have h2 := hh.2
  unfold ConPA.Ctl.Sem.Halts ConPA.Ctl.Sem.k at h2
  cases ct
  · simp only [semE, Bool.false_eq_true, if_false, Nat.cast_one, one_mul] at h2
    rcases one_of_add_eq_one h2 with (h1 | h1)
    · rwa [h1] at ht
    · rwa [h1] at hc
  · simp only [semE, if_true, Nat.cast_zero, zero_mul, zero_add] at h2
    rwa [h2] at hc

/-- A halt of the scheduler puts the contradiction code in every sound invariant. -/
theorem halts_in {e : Emitter} (R : Sound P e) (k : MPKind) (ct a : Bool) (n : M)
    (hh : F (haltAfterE e k ct a) ![n] = 1) : P (1 : M) := by
  rw [haltAfterE_model, haltAtE_iff e k ct a] at hh
  exact halt_in e k ct a _ (runE_sound R k a _ n (initial_in R)) hh

/-! ## The invariant `TargetProvable` -/

/-- Without the equality vacuity in the gate, provability in the numerical calculus of the
primary table is a sound invariant. -/
theorem soundTarget (e : Emitter) (he : e.delta = false) :
    Sound (TargetProvable (M := M)) e where
  definable := targetProvable_definable
  closed :=
    { mp := fun x y hx hxy => PA194TargetVectorJoin.mp_closed x y hx hxy
      gen := fun x y hy => PA194TargetGeneralize.generalize_closed x y hy
      row := fun x y z u h => rho8_provable x y z u h
      h1 := fun d h => by
        rw [← machineHead1_model]
        exact head1_provable d h
      h2 := fun d x h => head2_provable d x h
      h6 := fun d x h => head6_provable d x h }
  h3 := fun d x h => head3_provable d x h
  h4 := fun d x h => head4_provable d x h
  h5 := fun d h => head5_provable d h
  diagonal := fun c => diagonal_provable c
  gate := fun x y z hx hy => gate_provable x y z hx hy
  eqVac := fun h => by
    rw [he] at h
    exact absurd h (by simp)

/-- A halt of the scheduler gives a target proof of the contradiction code. -/
theorem halts_provable (e : Emitter) (he : e.delta = false) (k : MPKind) (ct a : Bool) (n : M)
    (hh : F (haltAfterE e k ct a) ![n] = 1) : TargetProvable (1 : M) :=
  halts_in (soundTarget e he) k ct a n hh

/-- Without the equality vacuity in the gate, the scheduler halts exactly when the calculus
of the primary table proves the contradiction code. For the gate with the equality vacuity
the corresponding statement about refutability of arithmetic is in
`PA194EmitterSchedulerPA`. -/
theorem halts_iff_provable (e : Emitter) (he : e.delta = false) (k : MPKind) (ct a : Bool) :
    (∃ n : M, F (haltAfterE e k ct a) ![n] = 1) ↔ TargetProvable (1 : M) :=
  ⟨fun ⟨n, hn⟩ => halts_provable e he k ct a n hn, provable_halts e k ct a⟩

/-- Without the equality vacuity in the gate, the scheduler halts exactly when the modeled
scheduler of the primary table halts. -/
theorem halts_iff_primary (e : Emitter) (he : e.delta = false) (k : MPKind) (ct a : Bool) :
    (∃ n : M, F (haltAfterE e k ct a) ![n] = 1) ↔ ∃ n : M, F haltAfter ![n] = 1 :=
  (halts_iff_provable e he k ct a).trans PA194ModelFairness.halts_iff_provable.symm

#print axioms stepE_eq
#print axioms G_of_provable
#print axioms runE_sound
#print axioms halts_iff_provable
#print axioms halts_iff_primary
end models
end PA194EmitterScheduler
