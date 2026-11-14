import PA194ModelDenseStartup
import PA194RegisterFileStandard
import PA194RegisterPermutation
import PA194ZeroRuns
import PA194StateOne
import PA194FetchPrefixBinding
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194StartupSourceFrame
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StandardCodeBridge PA194RegisterFile PA194RegisterFileStandard
open PA194RegisterPermutation PA194ZeroRuns PA194FiniteControls PA194StateOne PRAModelIOpenPairing

/-- The source-file prefix consists of nine logical registers and one spare;
the suffix retains all 25 remaining one-valued spare blocks. -/
def seedTail : Nat := PA194Bounded.bits (M6.Runtime.sepsR (List.replicate 25 1))
def firstTen : List Nat := [0,0,0,0,0,0,2,0,0,1]
def seedArgs : Fin 11 → Nat := ![2,0,0,0,0,0,0,0,0,1,seedTail]
def seedWord : Nat := word (M6.Runtime.sepsR firstTen) seedTail

local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)

theorem sourceSeedNat : F sourceFileCode seedArgs = seedWord := by
  have h := modelSourceFile (M := Nat) seedArgs
  have hv : physicalArgs seedArgs = valuesArg firstTen seedTail := by
    have h : ∀ i : Fin 11, physicalArgs seedArgs i = valuesArg firstTen seedTail i := by decide +kernel
    exact funext h
  rw [hv] at h
  have hs := sourceFile firstTen seedTail
  exact h.trans hs

theorem zerosNat (n x : Nat) : F zeros ![n,x] = 2^n*x := by
  induction n with
  | zero =>
    have h := modelZerosZero (M := Nat) x
    change F zeros ![0,x] = x at h
    simpa using h
  | succ n ih =>
    have h := modelZerosSucc (M := Nat) n x
    change F zeros ![F Code.succ (fun _ => n),x] =
      F addCode ![F zeros ![n,x],F zeros ![n,x]] at h
    rw [natSucc,natAdd] at h
    rw [h,ih,pow_succ,Nat.mul_assoc,Nat.mul_comm 2 x,←Nat.mul_assoc,Nat.mul_two]

theorem seedBits : PA194Bounded.bits PA194StartupData.seedFrame.r =
    1+2*((2^47)*(1+2*seedWord)) := by
  rw [← PA194StartupData.last_eq]
  decide +kernel

/-- The source register arguments really are the logical registers read from
    the complete 35-block standard startup file. -/
theorem seedArgs_logical (i : Fin 9) :
    seedArgs ⟨i.val, by have h := i.isLt; omega⟩ =
      M6.Source.readFile PA194StartupData.seedFile i := by
  have h : ∀ i : Fin 9,
      seedArgs ⟨i.val, by have hh := i.isLt; omega⟩ =
        M6.Source.readFile PA194StartupData.seedFile i := by decide +kernel
  exact h i

theorem firstSourceInstruction :
    M6.Source.resolveAt PA194SourceProgram.sites 25 =
      some (.dec 8 (some 27) (some 26)) := by
  have h := PA194FetchSource.fetch_prefix_at ⟨0,by decide⟩
  simpa [PA194FetchSource.fetchPrefixExpected] using h

theorem seededRegister8 : M6.Source.readFile PA194StartupData.seedFile 8 = 0 := by decide +kernel

/-- In the standard source semantics, the first seed instruction takes its
zero branch to site 27, leaving all logical registers unchanged. This is not
yet a physical implementation theorem. -/
theorem firstSeedSourceStep :
    M6.Source.step PA194SourceProgram.sites ⟨.at 25,M6.Source.readFile PA194StartupData.seedFile⟩ =
      ⟨.at 27,M6.Source.readFile PA194StartupData.seedFile⟩ := by
  rw [M6.Source.step_of_resolved firstSourceInstruction]
  simp [M6.Source.execute, seededRegister8, M6.Source.destination]
#print axioms firstSeedSourceStep
#print axioms seedArgs_logical

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelSourceSeed : F sourceFileCode (fun i => modelNumeral M (seedArgs i)) = modelNumeral M seedWord := by
  have h := (modelStandardCode (M := M) sourceFileCode) seedArgs
  rw [sourceSeedNat] at h
  exact h

theorem seedRight_sourceLayout :
    let f := F sourceFileCode (fun i => modelNumeral M (seedArgs i))
    let x := F zeros ![modelNumeral M 47,f+f+1]
    modelNumeral M (PA194Bounded.bits PA194StartupData.seedFrame.r) = x+x+1 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let f := F sourceFileCode (fun i => modelNumeral M (seedArgs i))
  have hf : f = modelNumeral M seedWord := modelSourceSeed
  have hinner : f+f+1 = modelNumeral M (1+2*seedWord) := by
    rw [hf,←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
    congr 1
  have hz : F zeros ![modelNumeral M 47,f+f+1] = modelNumeral M (2^47*(1+2*seedWord)) := by
    rw [hinner]
    have h := (modelStandardCode (M := M) zeros) (![47,1+2*seedWord] : Fin 2 → Nat)
    have hv : (fun i => modelNumeral M ((![47,1+2*seedWord] : Fin 2 → Nat) i)) =
      ![modelNumeral M 47,modelNumeral M (1+2*seedWord)] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
    rw [hv,zerosNat] at h
    exact h
  rw [hz,←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd,seedBits]
  congr 1

/-- The fixed startup endpoint exposes the full permuted register file and
all remaining spare blocks behind the exact state-24 source header. -/
theorem modelDenseStartupSourceFrame :
    let f := F sourceFileCode (fun i => modelNumeral M (seedArgs i))
    let x := F zeros ![modelNumeral M 47,f+f+1]
    F PA194Stepper.stepper ![modelNumeral M 58154,modelNumeral M 0] =
      F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,x+x+1]] := by
  dsimp only
  rw [←seedRight_sourceLayout]
  exact PA194ModelDenseStartup.modelDenseStartup
#print axioms modelSourceSeed
#print axioms seedRight_sourceLayout
#print axioms modelDenseStartupSourceFrame
end models
end PA194StartupSourceFrame
