import PA194SourceFetchRestoreLoop
import PA194ControllerRunAdd
import PA194ClockInvariantDefinable

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

namespace PA194ModelMPDrain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation PA194SourceFetchLoop
open PA194SourceFetchRestoreLoop PA194IteratedSimulation PA194ClockInvariantDefinable

def row (site : Nat) : Option M6.Source.Instruction :=
  (M6.Source.PathTrie.nthSite PA194.SourceTree.trie site).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie)

def location (r : Fin 9) : Fin 11 := ⟨r.val,by have := r.isLt; omega⟩

/-- A finite group of increment rows followed by a jump to the loop entry. -/
inductive Increments (exit : Nat) : Nat → List (Fin 9) → Prop where
  | jump (site : Nat) (valid : site < 3673) (cert : row site = some (.jump (some exit))) :
      Increments exit site []
  | inc (site next : Nat) (r : Fin 9) (registers : List (Fin 9)) (valid : site < 3673)
      (cert : row site = some (.inc r (some next))) (rest : Increments exit next registers) :
      Increments exit site (r :: registers)

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

def Reaches (s t : M) : Prop := ∃ c : M, F run ![c,s] = t
def ReachesPositive (s t : M) : Prop := ∃ c : M, 0 < c ∧ F run ![c,s] = t

theorem append {s t u : M} (h : Reaches s t) (h' : Reaches t u) : Reaches s u := by
  obtain ⟨c,hc⟩ := h
  obtain ⟨d,hd⟩ := h'
  refine ⟨c+d,?_⟩
  change F (iterate step) ![c+d,s] = u
  rw [PA194ControllerRunAdd.iterateAdd]
  change F run ![d,F run ![c,s]] = u
  rw [hc,hd]

theorem appendPositive {s t u : M} (h : Reaches s t) (h' : ReachesPositive t u) :
    ReachesPositive s u := by
  obtain ⟨c,hc⟩ := h
  obtain ⟨d,hd,he⟩ := h'
  have hc' : (0 : M) ≤ c := zero_le
  refine ⟨c+d,lt_of_lt_of_le hd (le_add_of_nonneg_left hc'),?_⟩
  change F (iterate step) ![c+d,s] = u
  rw [PA194ControllerRunAdd.iterateAdd]
  change F run ![d,F run ![c,s]] = u
  rw [hc,he]

theorem oneStep {s t : M} (h : F step ![s] = t) : ReachesPositive s t := by
  refine ⟨1,_root_.zero_lt_one,?_⟩
  change F (iterate step) ![(1 : M),s] = t
  rw [←zero_add (1 : M),iterateSucc,iterateZero,h]

theorem ReachesPositive.reaches {s t : M} (h : ReachesPositive s t) : Reaches s t :=
  ⟨h.choose,h.choose_spec.2⟩

def tally (r : Fin 11) (regs : List (Fin 9)) : Nat := (regs.map location).count r

noncomputable def tick (regs : List (Fin 9)) (args : Fin 11 → M) : Fin 11 → M :=
  fun i => args i+modelNumeral M (tally i regs)

theorem tickCons (r : Fin 9) (rs : List (Fin 9)) (args : Fin 11 → M) :
    tick rs (Function.update args (location r) (args (location r)+1)) = tick (r::rs) args := by
  funext i
  by_cases hi : i = location r
  · subst i
    simp only [tick,tally,List.map_cons,List.count_cons,beq_self_eq_true,if_true,
      Function.update_self]
    rw [PA194FiniteControls.modelNumeralSucc]
    ac_rfl
  · have hne : (location r == i) = false := by simp [Ne.symm hi]
    simp only [tick,tally,List.map_cons,List.count_cons,hne,Bool.false_eq_true,if_false,Function.update_of_ne hi,
      Nat.add_zero]

theorem incrementsRun {q exit : Nat} {rs : List (Fin 9)}
    (trace : Increments exit q rs) (args : Fin 11 → M) (tail : M) :
    Reaches (sourceState q args tail) (sourceState exit (tick rs args) tail) := by
  induction trace generalizing args with
  | jump site valid cert =>
    have ht : tick [] args = args := by funext i; simp [tick,tally,show modelNumeral M 0 = (0:M) from rfl]
    rw [ht]
    exact (oneStep (sourceJump site _ valid cert args tail)).reaches
  | inc site next r regs valid cert rest ih =>
    let out := Function.update args (location r) (args (location r)+1)
    have h := sourceInc site next r valid cert args tail
    change F step ![sourceState site args tail] = sourceState next out tail at h
    exact append (oneStep h).reaches (by rw [←tickCons r regs args]; exact ih out)

private theorem pathDef (r c : M → M) (n : M)
    (hr : 𝚺₁-Function₁ r) (hc : 𝚺₁-Function₁ c) :
    𝚺₁-Predicate (fun j : M => n < j ∨ ∃ t : M, r t = c j) := by
  haveI := hr
  haveI := hc
  definability

theorem runMany (frame : M → M) (n : M) (hframe : 𝚺₁-Function₁ frame)
    (hstep : ∀ j, j < n → Reaches (frame j) (frame (j+1))) :
    ∀ j, j ≤ n → Reaches (frame 0) (frame j) := by
  have hr : 𝚺₁-Function₁ (fun t => F run ![t,frame 0]) := bindBinary _ _ (binaryCodeDef run)
  have h : ∀ j, n < j ∨ Reaches (frame 0) (frame j) := by
    intro j
    induction j using ISigma1.sigma1_succ_induction with
    | hP => exact pathDef _ _ n hr hframe
    | zero => exact Or.inr ⟨0,iterateZero step _⟩
    | succ j ih =>
      by_cases hbig : n < j+1
      · exact Or.inl hbig
      · right
        have hj : j < n := lt_of_lt_of_le (lt_add_one j) (not_lt.mp hbig)
        exact append (ih.resolve_left (not_lt_of_ge (le_of_lt hj))) (hstep j hj)
  exact fun j hj => (h j).resolve_left (not_lt_of_ge hj)

theorem frameDef (site : Nat) (a : Fin 11 → M → M) (tail : M)
    (ha : ∀ i, 𝚺₁-Function₁ (a i)) :
    𝚺₁-Function₁ (fun j : M => sourceState site (fun i => a i j) tail) := by
  letI := ha 0
  letI := ha 1
  letI := ha 2
  letI := ha 3
  letI := ha 4
  letI := ha 5
  letI := ha 6
  letI := ha 7
  letI := ha 8
  change 𝚺₁-Function₁ (fun j : M => pair (modelNumeral M site)
    (pair (a 0 j) (pair (a 1 j) (pair (a 2 j) (pair (a 3 j) (pair (a 4 j)
      (pair (a 5 j) (pair (a 6 j) (pair (a 7 j) (pair (a 8 j) tail))))))))))
  definability

noncomputable def argsAfter (args : Fin 11 → M) (r : Fin 9) (rs : List (Fin 9)) (j : M) : Fin 11 → M :=
  fun i => if i = location r then F subCode ![args i,j]
    else args i+modelNumeral M (tally i rs)*j

private theorem bindFirst (f : M → M → M) (a : M) (h : 𝚺₁-Function₂ f) :
    𝚺₁-Function₁ (fun j => f a j) := by
  haveI := h
  definability

theorem subByDef (a : M) : 𝚺₁-Function₁ (fun j => F subCode ![a,j]) :=
  bindFirst _ a (binaryCodeDef subCode)

theorem partialDef (args : Fin 11 → M) (r : Fin 9) (rs : List (Fin 9)) (i : Fin 11) :
    𝚺₁-Function₁ (fun j : M => argsAfter args r rs j i) := by
  by_cases hi : i = location r
  · simp only [argsAfter,hi,if_true]
    exact subByDef _
  · simp only [argsAfter,hi,if_false]
    definability

theorem subSelf (z : M) : F subCode ![z,z] = (0 : M) := by
  have h := modelSubAdd z (0 : M)
  change F subCode ![z+0,z] = (0 : M) at h
  simpa only [add_zero] using h

theorem partialZero (args : Fin 11 → M) (r : Fin 9) (rs : List (Fin 9)) :
    argsAfter args r rs 0 = args := by
  funext i
  by_cases hi : i = location r
  · simp only [argsAfter,hi,if_true]
    exact PRASubtraction.modelSubZero _
  · simp [argsAfter,hi]

theorem tallyZero {r : Fin 9} {rs : List (Fin 9)} (h : r ∉ rs) :
    tally (location r) rs = 0 := by
  apply List.count_eq_zero.mpr
  intro hi
  obtain ⟨u,hu,hr⟩ := List.mem_map.mp hi
  have he : u = r := Fin.ext (congrArg (Fin.val : Fin 11 → Nat) hr)
  exact h (he ▸ hu)

theorem drain (site first exit : Nat) (r : Fin 9) (rs : List (Fin 9)) (valid : site < 3673)
    (entry : row site = some (.dec r (some exit) (some first)))
    (loop : Increments site first rs) (hr : r ∉ rs)
    (args : Fin 11 → M) (tail : M) :
    ReachesPositive (sourceState site args tail)
      (sourceState exit (argsAfter args r rs (args (location r))) tail) := by
  let n := args (location r)
  let a := argsAfter args r rs
  let frame := fun j => sourceState site (a j) tail
  have hf : 𝚺₁-Function₁ frame := frameDef site (fun i j => a j i) tail (partialDef args r rs)
  have stepLoop (j : M) (hj : j < n) : Reaches (frame j) (frame (j+1)) := by
    obtain ⟨v,hv⟩ := le_iff_exists_add.mp (lt_iff_succ_le.mp hj)
    have hbefore : a j (location r) = v+1 := by
      simp only [a,argsAfter,if_true]
      change F subCode ![n,j] = v+1
      rw [hv,show (j+1)+v = j+(v+1) by ac_rfl]
      exact modelSubAdd j (v+1)
    let out := Function.update (a j) (location r) v
    have hs := sourceDecPositive site first r (some exit) valid entry (a j) tail v hbefore
    change F step ![frame j] = sourceState first out tail at hs
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
    exact append (oneStep hs).reaches (by change Reaches _ (sourceState site (a (j+1)) tail); rw [←ht]; exact incrementsRun loop out tail)
  have hrun := runMany frame n hf stepLoop n le_rfl
  change Reaches (sourceState site (a 0) tail) (sourceState site (a n) tail) at hrun
  rw [show a 0 = args from partialZero args r rs] at hrun
  have hz : a n (location r) = (0 : M) := by
    simp only [a,argsAfter,if_true]
    exact subSelf _
  exact appendPositive hrun (oneStep (sourceDecZero site exit r (some first) valid entry (a n) tail hz))

#print axioms runMany
#print axioms frameDef
#print axioms drain
end models
end PA194ModelMPDrain
