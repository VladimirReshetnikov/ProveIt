import PA194DecoderRoundCode
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceReconstruct
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive PA194SourcePCBound
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
noncomputable def drop : Nat → M → M
  | 0, f => f
  | n+1, f => drop n (pi₂ f)
noncomputable def rebuild : Nat → M → M
  | 0, f => f
  | n+1, f => pair (pi₁ f) (rebuild n (pi₂ f))

theorem rebuildEq (n : Nat) (f : M) : rebuild n f = f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [rebuild,ih,pair_unpair]

noncomputable def argsOfFile (f : M) : Fin 11 → M := fun i => getSem i.val f

theorem fileReconstruct (f : M) : pack (regsOfArgs (argsOfFile f)) (drop 9 f) = f := by
  change rebuild 9 f = f
  exact rebuildEq 9 f

theorem stateReconstruct (s : M) (hpc : F pc ![s] = modelNumeral M 34) :
    sourceState 34 (argsOfFile (pi₂ s)) (drop 9 (pi₂ s)) = s := by
  have hp : pi₁ s = modelNumeral M 34 := (pcModel s).symm.trans hpc
  change pair (modelNumeral M 34) (pack (regsOfArgs (argsOfFile (pi₂ s))) (drop 9 (pi₂ s))) = s
  rw [fileReconstruct,←hp,pair_unpair]
#print axioms fileReconstruct
#print axioms stateReconstruct
end models
end PA194SourceReconstruct
