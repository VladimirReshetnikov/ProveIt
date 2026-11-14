import PA194SchedulerCode
import PA194SchedulerHalt
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194SchedulerIteration
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194NumeralCode PA194TargetCantor
 PA194TargetStep PA194TargetExtendedStep PA194MachineProjections PA194MachineStack PA194MachineAXCode
 PA194MachineShiftMPCode PA194SchedulerCode PA194StackCode PA194BranchSeed PA194TargetProofLeaf

noncomputable def fst {m : Nat} (a : Code m) : Code m := unary firstProjection a
noncomputable def snd {m : Nat} (a : Code m) : Code m := unary secondProjection a
noncomputable def fN : Code 1 := fst (.proj 0)
noncomputable def fL : Code 1 := fst (snd (.proj 0))
noncomputable def fT : Code 1 := fst (snd (snd (.proj 0)))
noncomputable def fW : Code 1 := fst (snd (snd (snd (.proj 0))))
noncomputable def fD : Code 1 := fst (snd (snd (snd (snd (.proj 0)))))
noncomputable def fH : Code 1 := snd (snd (snd (snd (snd (.proj 0)))))
noncomputable def pack {m : Nat} (n l t w d h : Code m) : Code m :=
  bin pairCode n (bin pairCode l (bin pairCode t (bin pairCode w (bin pairCode d h))))
noncomputable def step : Code 1 := pack (nextN fN fL) (nextL fN fL) (nextTop fN fL fT fW fD fH)
  (nextStack fN fL fT fW fD fH) (nextD fN fL fD) (nextCache fN fL fW)
noncomputable def run : Code 2 := dropCode step
noncomputable def initial : Code 0 := pack (numeralCode 0 2) (.zero 0) (.zero 0) (.zero 0) (.zero 0) (.zero 0)
noncomputable def haltAt : Code 1 := halt fN fL fT fH

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

theorem fst_model {m : Nat} (a : Code m) (e : Fin m → M) : F (fst a) e = π₁ (F a e) := by
  rw [fst,modelUnary,modelPi1Code firstProjection firstProjection_certified]
theorem snd_model {m : Nat} (a : Code m) (e : Fin m → M) : F (snd a) e = π₂ (F a e) := by
  rw [snd,modelUnary,modelPi2Code secondProjection secondProjection_certified]
theorem pack_model {m : Nat} (n l t w d h : Code m) (e : Fin m → M) :
    F (pack n l t w d h) e = pair (F n e) (pair (F l e) (pair (F t e) (pair (F w e) (pair (F d e) (F h e))))) := by
  simp only [pack,modelBin,modelPairCode]

theorem step_fields (s : M) :
    let ns := F step ![s]
    F fT ![ns] = F (nextTop fN fL fT fW fD fH) ![s] ∧
    F fW ![ns] = F (nextStack fN fL fT fW fD fH) ![s] ∧
    F fH ![ns] = F (nextCache fN fL fW) ![s] := by
  simp only [step,pack_model,fT,fW,fH,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair]
  exact ⟨trivial,trivial,trivial⟩

def SoundPacked (s : M) : Prop := SoundStore (F fT ![s]) (F fW ![s]) (F fH ![s])

theorem step_preserves (s : M) (hs : SoundPacked s) : SoundPacked (F step ![s]) := by
  have hf := step_fields s
  unfold SoundPacked
  rw [hf.1,hf.2.1,hf.2.2]
  exact PA194SchedulerCode.store_preserves fN fL fT fW fD fH ![s] hs

theorem code_unary_def (c : Code 1) : 𝚺₁-Function₁ (fun s : M => F c ![s]) := by
  have h : 𝚺₁.DefinableFunction (fun e : Fin 1 → M => F c e) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) c)
  convert h using 1
  funext e
  change F c ![e 0] = F c e
  apply congrArg (fun e : Fin 1 → M => F c e)
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem soundPacked_def_generic (ft fw fh : M → M)
    (ht : 𝚺₁-Function₁ ft) (hw : 𝚺₁-Function₁ fw) (hh : 𝚺₁-Function₁ fh) :
    𝚺₁-Predicate (fun s => TargetProvable (ft s) ∧ TargetProvable (fh s) ∧ TargetStack (fw s)) := by
  haveI := ht
  haveI := hw
  haveI := hh
  haveI := targetProvable_definable (M := M)
  haveI := targetStack_def (M := M)
  definability

theorem soundPacked_def : 𝚺₁-Predicate (SoundPacked (M := M)) :=
  soundPacked_def_generic _ _ _ (code_unary_def fT) (code_unary_def fW) (code_unary_def fH)

theorem run_base (s : M) : F run ![0,s] = s := modelDropBase step s

theorem run_succ (k s : M) : F run ![k+1,s] = F step ![F run ![k,s]] := by
  rw [run,modelDropStep]
  have hv : (fun _ : Fin 1 => F (dropCode step) ![k,s]) = ![F (dropCode step) ![k,s]] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv]

theorem unary_from_binary (f : M → M → M) (s : M) (hf : 𝚺₁-Function₂ f) :
    𝚺₁-Function₁ (fun n => f n s) := by
  haveI := hf
  definability

theorem run_def (s : M) : 𝚺₁-Function₁ (fun n : M => F run ![n,s]) := by
  have h : 𝚺₁.DefinableFunction (fun e : Fin 2 → M => F run e) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) run)
  have hf : 𝚺₁-Function₂ (fun n s : M => F run ![n,s]) := by
    convert h using 1
    funext e
    exact congrArg (fun e : Fin 2 → M => F run e) (Matrix.fun_eq_vec_two e).symm
  exact unary_from_binary _ s hf

theorem run_sound (s k : M) (hs : SoundPacked s) : SoundPacked (F run ![k,s]) := by
  haveI := soundPacked_def (M := M)
  haveI := run_def s
  have hp : 𝚺₁-Predicate (fun k : M => SoundPacked (F run ![k,s])) := by definability
  induction k using ISigma1.sigma1_succ_induction with
  | hP => exact hp
  | zero => rw [run_base]; exact hs
  | succ k ih => rw [run_succ]; exact step_preserves _ ih

theorem initial_sound : SoundPacked (F initial Fin.elim0) := by
  unfold SoundPacked initial
  simp only [pack_model,fT,fW,fH,fst_model,snd_model,modelProjection,Matrix.cons_val_zero,pi₁_pair,pi₂_pair,PRAMultiplication.modelZero]
  exact soundStore_zero (M := M)

theorem run_halt_provable (s k : M) (hs : SoundPacked s)
    (hh : F haltAt ![F run ![k,s]] = 1) : TargetProvable (1 : M) := by
  have h := run_sound s k hs
  exact PA194SchedulerHalt.halt_implies_provable fN fL fT fW fH ![F run ![k,s]] h hh

theorem initial_run_halt_provable (k : M)
    (hh : F haltAt ![F run ![k,F initial Fin.elim0]] = 1) : TargetProvable (1 : M) :=
  run_halt_provable _ k initial_sound hh

#print axioms initial_sound
#print axioms run_halt_provable
#print axioms initial_run_halt_provable
#print axioms soundPacked_def
#print axioms run_base
#print axioms run_succ
#print axioms run_sound
#print axioms step_fields
#print axioms step_preserves
end models
end PA194SchedulerIteration
