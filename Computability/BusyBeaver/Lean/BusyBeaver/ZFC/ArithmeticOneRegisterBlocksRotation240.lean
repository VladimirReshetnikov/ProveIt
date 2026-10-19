import BusyBeaver.ZFC.ArithmeticCantor
import BusyBeaver.ZFC.ArithmeticMachinePerm252
import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!
Total internal repetition of the value-one register block 011.
This is tape-code algebra for the Rotation240 spare invariant: an increment
appends one such block, while a positive decrement appends none. It proves no
machine transition or simulation. The count and suffix are arbitrary internal
values of every IΣ1 model; the Nat adapter uses the existing bitsCode codec.
The construction follows ArithmeticZeroRegisterBlocks254 with affine update
8*x+6 instead of 4*x+2. No proof limits are raised.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticOneRegisterBlocksRotation240
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachinePerm252

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out suffix. out = suffix”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index suffix. out = 8*previous+6”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero parameters := parameters 0
  succ _ _ previous := 8*previous+6
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef, numeral_eq_natCast]

noncomputable def oneBlocks (count suffix : V) : V :=
  construction.result ![suffix] count

def oneBlocksDef : 𝚺₁.Semisentence 3 := blueprint.resultDef
def oneBlocksDeltaDef : 𝚫₁.Semisentence 3 := blueprint.resultDeltaDef

instance oneBlocks_defined : 𝚺₁-Function₂[V] oneBlocks via oneBlocksDef := .mk fun e => by
  have he : (fun i : Fin 1 => e i.succ.succ) = ![e 2] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have h := (construction (V := V)).result_defined.df e
  change blueprint.resultDef.val.Evalb e ↔
    e 0 = construction.result (fun i : Fin 1 => e i.succ.succ) (e 1) at h
  rw [he] at h
  change blueprint.resultDef.val.Evalb e ↔ e 0 = construction.result ![e 2] (e 1)
  exact h

instance oneBlocks_defined_delta : 𝚫₁-Function₂[V] oneBlocks via oneBlocksDeltaDef :=
  oneBlocks_defined.graph_delta
instance oneBlocks_definable : 𝚺₁-Function₂[V] oneBlocks :=
  oneBlocks_defined.to_definable

@[simp] theorem oneBlocks_zero (suffix : V) : oneBlocks 0 suffix = suffix := by
  simp [oneBlocks, construction]

@[simp] theorem oneBlocks_succ (count suffix : V) :
    oneBlocks (count+1) suffix = 8*oneBlocks count suffix+6 := by
  simp [oneBlocks, PR.Construction.result_succ, construction]

theorem oneBlocks_one (suffix : V) : oneBlocks 1 suffix = 8*suffix+6 := by
  simpa only [zero_add, oneBlocks_zero] using oneBlocks_succ (0 : V) suffix

/-- Concatenation for two arbitrary internal counts, with the whole suffix retained. -/
theorem oneBlocks_add (leftCount rightCount suffix : V) :
    oneBlocks (leftCount+rightCount) suffix =
      oneBlocks rightCount (oneBlocks leftCount suffix) := by
  induction rightCount using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ rightCount ih => rw [←add_assoc, oneBlocks_succ, oneBlocks_succ, ih]

/-- A block appended after the repeated spares can be absorbed into their count. -/
theorem oneBlocks_push (count suffix : V) :
    oneBlocks count (8*suffix+6) = oneBlocks (count+1) suffix := by
  calc
    oneBlocks count (8*suffix+6) = oneBlocks count (oneBlocks 1 suffix) := by
      rw [oneBlocks_one]
    _ = oneBlocks (1+count) suffix := (oneBlocks_add 1 count suffix).symm
    _ = oneBlocks (count+1) suffix := by rw [add_comm]

theorem oneBlocks_total (count suffix : V) :
    ∃! out, oneBlocksDef.val.Evalb ![out,count,suffix] := by simp

/-- Only this comparison specializes to Nat and ordinary finite lists. -/
theorem oneBlocks_bitsCode (count : Nat) (suffix : List Bool) :
    oneBlocks count (bitsCode suffix) =
      bitsCode ((List.replicate count [false,true,true]).flatten ++ suffix) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [oneBlocks_succ, ih]
    simp only [List.replicate_succ, List.flatten_cons,
      List.cons_append, List.nil_append, bitsCode, Bool.toNat_false, Bool.toNat_true]
    omega

theorem oneBlocksDef_bitsCode (out count : Nat) (suffix : List Bool) :
    oneBlocksDef.val.Evalb ![out,count,bitsCode suffix] ↔
      out = bitsCode ((List.replicate count [false,true,true]).flatten ++ suffix) := by
  simp [oneBlocks_bitsCode]

end SetTheory.BusyBeaver.ZFC.ArithmeticOneRegisterBlocksRotation240
