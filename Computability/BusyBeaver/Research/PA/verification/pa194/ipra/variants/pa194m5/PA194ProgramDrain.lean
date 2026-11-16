import PA194ProgramControl

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

namespace PA194ProgramDrain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SchedulerFetchPositive PA194SourceRegisterRelation PA194SourceFetchLoop
open PA194IteratedSimulation PA194ClockInvariantDefinable
open PA194SourceControllerCode (pc destination)
open PA194SourceRegisters PA194SourceInstructionModel
open PA194ModelMPDrain (location tally tick tickCons frameDef argsAfter partialDef partialZero subSelf tallyZero)

abbrev Program := PA194ProgramControl.Program
abbrev row := PA194ProgramControl.row
abbrev step := PA194ProgramControl.step
abbrev run := PA194ProgramControl.run

/-- A finite group of increment rows followed by a jump to the loop entry. -/
inductive Increments (program : Program) (exit : Nat) : Nat → List (Fin 9) → Prop where
  | jump (site : Nat) (valid : site < program.length) (cert : row program site = some (.jump (some exit))) :
      Increments program exit site []
  | inc (site next : Nat) (r : Fin 9) (registers : List (Fin 9)) (valid : site < program.length)
      (cert : row program site = some (.inc r (some next))) (rest : Increments program exit next registers) :
      Increments program exit site (r :: registers)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


variable (program : Program)

theorem rowStep (q : Nat) (hq : q < program.length) (s : M)
    (hs : F pc ![s] = modelNumeral M q) {i : M6.Source.Instruction}
    (hrow : row program q = some i) (hstep : i ≠ .halt) :
    F (step program) ![s] = instructionSem (some i) s := by
  change PA194ProgramControl.row program q = some i at hrow
  rw [PA194ProgramControl.actionAt program q hq s hs,hrow]
  cases i with
  | halt => exact False.elim (hstep rfl)
  | inc r next =>
    simpa only [PA194ProgramControl.action] using instructionModel (some (.inc r next)) s
  | dec r zero positive =>
    simpa only [PA194ProgramControl.action] using instructionModel (some (.dec r zero positive)) s
  | jump next =>
    simpa only [PA194ProgramControl.action] using instructionModel (some (.jump next)) s

theorem sourceInc (q d : Nat) (r : Fin 9) (hq : q < program.length)
    (hinst : row program q = some (.inc r (some d)))
    (args : Fin 11 → M) (tail : M) :
    F (step program) ![sourceState q args tail] =
      sourceState d (Function.update args ⟨r.val,by have h := r.isLt; omega⟩ (regsOfArgs args r+1)) tail := by
  rw [rowStep program q hq _ (statePC q args tail) hinst (by intro h; cases h)]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change pair (modelNumeral M d) (putSem r.val (pi₂ (sourceState q args tail))
    (F Code.succ (fun _ => getSem r.val (pi₂ (sourceState q args tail))))) = _
  rw [stateReg q args tail r,←modelAddOne]
  change pair (modelNumeral M d) (putSem r.val (pi₂ (pair (modelNumeral M q)
    (pack (regsOfArgs args) tail))) (regsOfArgs args r+1)) = _
  rw [pi₂_pair,updateRegister]
  rfl

theorem sourceJump (q d : Nat) (hq : q < program.length)
    (hinst : row program q = some (.jump (some d)))
    (args : Fin 11 → M) (tail : M) :
    F (step program) ![sourceState q args tail] = sourceState d args tail := by
  rw [rowStep program q hq _ (statePC q args tail) hinst (by intro h; cases h)]
  change pair (modelNumeral M d) (pi₂ (pair (modelNumeral M q) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]; rfl

theorem sourceDecPositive (q d : Nat) (r : Fin 9) (z : Option Nat) (hq : q < program.length)
    (hinst : row program q = some (.dec r z (some d)))
    (args : Fin 11 → M) (tail m : M) (hm : regsOfArgs args r = m+1) :
    F (step program) ![sourceState q args tail] =
      sourceState d (Function.update args ⟨r.val,by have h := r.isLt; omega⟩ m) tail := by
  have hn : getSem r.val (pi₂ (sourceState q args tail)) ≠ (0 : M) := by
    rw [stateReg,hm]
    exact ne_of_gt (lt_of_le_of_lt (zero_le : (0 : M) ≤ m) (lt_add_of_pos_right m (Arithmetic.zero_lt_one : (0 : M) < 1)))
  have hp : F predCode (fun _ => getSem r.val (pi₂ (sourceState q args tail))) = m := by
    rw [stateReg,hm,show m+1 = F Code.succ (fun _ => m) from modelAddOne m,modelPredSucc]
  rw [rowStep program q hq _ (statePC q args tail) hinst (by intro h; cases h)]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change (if getSem r.val (pi₂ (sourceState q args tail)) = (0 : M) then _ else _) = _
  rw [if_neg hn]
  change pair (modelNumeral M d) (putSem r.val (pi₂ (sourceState q args tail))
      (F predCode (fun _ => getSem r.val (pi₂ (sourceState q args tail))))) = _
  rw [hp]
  change pair (modelNumeral M d) (putSem r.val (pi₂ (pair (modelNumeral M q)
    (pack (regsOfArgs args) tail))) m) = _
  rw [pi₂_pair,updateRegister]
  rfl

theorem sourceDecZero (q d : Nat) (r : Fin 9) (p : Option Nat) (hq : q < program.length)
    (hinst : row program q = some (.dec r (some d) p))
    (args : Fin 11 → M) (tail : M) (hz : regsOfArgs args r = (0 : M)) :
    F (step program) ![sourceState q args tail] = sourceState d args tail := by
  have hr : getSem r.val (pi₂ (sourceState q args tail)) = (0 : M) := (stateReg q args tail r).trans hz
  rw [rowStep program q hq _ (statePC q args tail) hinst (by intro h; cases h)]
  simp only [PA194SourceInstructionModel.instructionSem,destination]
  change (if getSem r.val (pi₂ (sourceState q args tail)) = (0 : M) then _ else _) = _
  rw [if_pos hr]
  change pair (modelNumeral M d) (pi₂ (pair (modelNumeral M q) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]; rfl

def Reaches (s t : M) : Prop := ∃ c : M, F (run program) ![c,s] = t
def ReachesPositive (s t : M) : Prop := ∃ c : M, 0 < c ∧ F (run program) ![c,s] = t

theorem append {s t u : M} (h : Reaches program s t) (h' : Reaches program t u) : Reaches program s u := by
  obtain ⟨c,hc⟩ := h
  obtain ⟨d,hd⟩ := h'
  refine ⟨c+d,?_⟩
  change F (iterate (step program)) ![c+d,s] = u
  rw [PA194ControllerRunAdd.iterateAdd]
  change F (run program) ![d,F (run program) ![c,s]] = u
  rw [hc,hd]

theorem appendPositive {s t u : M} (h : Reaches program s t) (h' : ReachesPositive program t u) :
    ReachesPositive program s u := by
  obtain ⟨c,hc⟩ := h
  obtain ⟨d,hd,he⟩ := h'
  have hc' : (0 : M) ≤ c := zero_le
  refine ⟨c+d,lt_of_lt_of_le hd (le_add_of_nonneg_left hc'),?_⟩
  change F (iterate (step program)) ![c+d,s] = u
  rw [PA194ControllerRunAdd.iterateAdd]
  change F (run program) ![d,F (run program) ![c,s]] = u
  rw [hc,he]

theorem oneStep {s t : M} (h : F (step program) ![s] = t) : ReachesPositive program s t := by
  refine ⟨1,_root_.zero_lt_one,?_⟩
  change F (iterate (step program)) ![(1 : M),s] = t
  rw [←zero_add (1 : M),iterateSucc,iterateZero,h]

theorem ReachesPositive.reaches {s t : M} (h : ReachesPositive program s t) : Reaches program s t :=
  ⟨h.choose,h.choose_spec.2⟩

theorem incrementsRun {q exit : Nat} {rs : List (Fin 9)}
    (trace : Increments program exit q rs) (args : Fin 11 → M) (tail : M) :
    Reaches program (sourceState q args tail) (sourceState exit (tick rs args) tail) := by
  induction trace generalizing args with
  | jump site valid cert =>
    have ht : tick [] args = args := by funext i; simp [tick,tally,show modelNumeral M 0 = (0:M) from rfl]
    rw [ht]
    exact (oneStep program (sourceJump program site _ valid cert args tail)).reaches
  | inc site next r regs valid cert rest ih =>
    let out := Function.update args (location r) (args (location r)+1)
    have h := sourceInc program site next r valid cert args tail
    change F (step program) ![sourceState site args tail] = sourceState next out tail at h
    exact append program (oneStep program h).reaches (by rw [←tickCons r regs args]; exact ih out)

private theorem pathDef (r c : M → M) (n : M)
    (hr : 𝚺₁-Function₁ r) (hc : 𝚺₁-Function₁ c) :
    𝚺₁-Predicate (fun j : M => n < j ∨ ∃ t : M, r t = c j) := by
  haveI := hr
  haveI := hc
  definability

theorem runMany (frame : M → M) (n : M) (hframe : 𝚺₁-Function₁ frame)
    (hstep : ∀ j, j < n → Reaches program (frame j) (frame (j+1))) :
    ∀ j, j ≤ n → Reaches program (frame 0) (frame j) := by
  have hr : 𝚺₁-Function₁ (fun t => F (run program) ![t,frame 0]) := bindBinary _ _ (binaryCodeDef (run program))
  have h : ∀ j, n < j ∨ Reaches program (frame 0) (frame j) := by
    intro j
    induction j using ISigma1.sigma1_succ_induction with
    | hP => exact pathDef _ _ n hr hframe
    | zero => exact Or.inr ⟨0,iterateZero (step program) _⟩
    | succ j ih =>
      by_cases hbig : n < j+1
      · exact Or.inl hbig
      · right
        have hj : j < n := lt_of_lt_of_le (lt_add_one j) (not_lt.mp hbig)
        exact append program (ih.resolve_left (not_lt_of_ge (le_of_lt hj))) (hstep j hj)
  exact fun j hj => (h j).resolve_left (not_lt_of_ge hj)

theorem drain (site first exit : Nat) (r : Fin 9) (rs : List (Fin 9)) (valid : site < program.length)
    (entry : row program site = some (.dec r (some exit) (some first)))
    (loop : Increments program site first rs) (hr : r ∉ rs)
    (args : Fin 11 → M) (tail : M) :
    ReachesPositive program (sourceState site args tail)
      (sourceState exit (argsAfter args r rs (args (location r))) tail) := by
  let n := args (location r)
  let a := argsAfter args r rs
  let frame := fun j => sourceState site (a j) tail
  have hf : 𝚺₁-Function₁ frame := frameDef site (fun i j => a j i) tail (partialDef args r rs)
  have stepLoop (j : M) (hj : j < n) : Reaches program (frame j) (frame (j+1)) := by
    obtain ⟨v,hv⟩ := le_iff_exists_add.mp (lt_iff_succ_le.mp hj)
    have hbefore : a j (location r) = v+1 := by
      simp only [a,argsAfter,if_true]
      change F subCode ![n,j] = v+1
      rw [hv,show (j+1)+v = j+(v+1) by ac_rfl]
      exact modelSubAdd j (v+1)
    let out := Function.update (a j) (location r) v
    have hs := sourceDecPositive program site first r (some exit) valid entry (a j) tail v hbefore
    change F (step program) ![frame j] = sourceState first out tail at hs
    have ht : tick rs out = a (j+1) := by
      funext i
      by_cases hi : i = location r
      · subst i
        simp only [tick,out,Function.update_self,tallyZero hr,
          show modelNumeral M 0 = (0:M) from rfl,add_zero,a,argsAfter,if_true]
        change v = F subCode ![n,j+1]
        rw [hv]
        exact (modelSubAdd (j+1) v).symm
      · simp only [tick,out,Function.update_of_ne hi,a,argsAfter,hi,if_false,mul_add,mul_one]
        rw [add_assoc]
    exact append program (oneStep program hs).reaches (by change Reaches program _ (sourceState site (a (j+1)) tail); rw [←ht]; exact incrementsRun program loop out tail)
  have hrun := runMany program frame n hf stepLoop n le_rfl
  change Reaches program (sourceState site (a 0) tail) (sourceState site (a n) tail) at hrun
  rw [show a 0 = args from partialZero args r rs] at hrun
  have hz : a n (location r) = (0 : M) := by
    simp only [a,argsAfter,if_true]
    exact subSelf _
  exact appendPositive program hrun (oneStep program (sourceDecZero program site exit r (some first) valid entry (a n) tail hz))


/-- The terminating counter loop adds the coefficient times the old counter
    to register 1 and clears register 7 in any modeled register file. -/
theorem multiply (site first exit coefficient : Nat) (valid : site < program.length)
    (entry : row program site = some (.dec 7 (some exit) (some first)))
    (loop : Increments program site first (List.replicate coefficient (1 : Fin 9)))
    (args : Fin 11 → M) (tail : M) :
    ReachesPositive program (sourceState site args tail)
      (sourceState exit
        (Function.update (Function.update args 1 (args 1+modelNumeral M coefficient * args 7)) 7 0)
        tail) := by
  have hn : (7 : Fin 9) ∉ List.replicate coefficient (1 : Fin 9) := by simp
  have hd := drain program site first exit 7 (List.replicate coefficient 1)
    valid entry loop hn args tail
  have hoff : argsAfter args 7 (List.replicate coefficient 1) (args (location 7)) =
        Function.update (Function.update args 1 (args 1+modelNumeral M coefficient * args 7)) 7 0 := by
    funext i
    by_cases h7 : i = 7
    · subst i
      simp [argsAfter,location,subSelf]
    · by_cases h1 : i = 1
      · subst i
        simp [argsAfter,location,tally,List.map_replicate]
      · simp [argsAfter,location,tally,List.map_replicate,List.count_replicate,h7,h1,Ne.symm h1,
          show modelNumeral M 0 = (0 : M) from rfl]
  rwa [hoff] at hd

#print axioms rowStep
#print axioms drain
#print axioms multiply
end models
end PA194ProgramDrain
