import BusyBeaver.ZFC.ArithmeticCantor
import BusyBeaver.ZFC.ArithmeticMachinePerm252
import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!
Total internal repetition of an unmarked zero register block.
The actual register encoding is [false,true]; in least-significant-first tape
coding it prepends 2+4*suffix. A fixed Blueprint1 graph iterates that map from
an arbitrary suffix, for every IΣ1 model count. The Nat adapter uses actual
ArithmeticMachinePerm252.bitsCode. No machine transition, spare invariant,
register-file simulation, or first-exit theorem is assumed or asserted.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachinePerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The suffix is a fixed parameter, not an additional recursion index. -/
def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out suffix. out = suffix”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index suffix. out = 4*previous+2”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef
noncomputable def construction : PR.Construction V blueprint where
  zero parameters := parameters 0
  succ _ _ previous := 4*previous+2
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef, numeral_eq_natCast]

noncomputable def zeroBlocks (count suffix : V) : V := construction.result ![suffix] count

def zeroBlocksDef : 𝚺₁.Semisentence 3 := blueprint.resultDef
def zeroBlocksDeltaDef : 𝚫₁.Semisentence 3 := blueprint.resultDeltaDef
instance zeroBlocks_defined : 𝚺₁-Function₂[V] zeroBlocks via zeroBlocksDef := .mk fun e => by
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
instance zeroBlocks_defined_delta : 𝚫₁-Function₂[V] zeroBlocks via zeroBlocksDeltaDef :=
  zeroBlocks_defined.graph_delta
instance zeroBlocks_definable : 𝚺₁-Function₂[V] zeroBlocks := zeroBlocks_defined.to_definable

@[simp] theorem zeroBlocks_zero (suffix : V) : zeroBlocks 0 suffix = suffix := by
  simp [zeroBlocks, construction]
@[simp] theorem zeroBlocks_succ (count suffix : V) :
    zeroBlocks (count+1) suffix = 4*zeroBlocks count suffix+2 := by
  simp [zeroBlocks, PR.Construction.result_succ, construction]

theorem zeroBlocks_one (suffix : V) : zeroBlocks 1 suffix = 4*suffix+2 := by
  simpa only [zero_add, zeroBlocks_zero] using zeroBlocks_succ (0 : V) suffix

/-- Concatenation of two internally long runs of the same zero block. -/
theorem zeroBlocks_add (leftCount rightCount suffix : V) :
    zeroBlocks (leftCount+rightCount) suffix =
      zeroBlocks rightCount (zeroBlocks leftCount suffix) := by
  induction rightCount using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ rightCount ih => rw [←add_assoc, zeroBlocks_succ, zeroBlocks_succ, ih]

/-- One complete block may be moved into the suffix without losing it. -/
theorem zeroBlocks_push (count suffix : V) :
    zeroBlocks count (4*suffix+2) = zeroBlocks (count+1) suffix := by
  calc
    zeroBlocks count (4*suffix+2) = zeroBlocks count (zeroBlocks 1 suffix) := by
      rw [zeroBlocks_one]
    _ = zeroBlocks (1+count) suffix := (zeroBlocks_add 1 count suffix).symm
    _ = zeroBlocks (count+1) suffix := by rw [add_comm]

/-- Two arithmetic reads see false then true, leaving the entire suffix. -/
theorem zeroBlocks_bit (count suffix : V) : zeroBlocks (count+1) suffix % 2 = 0 := by
  rw [zeroBlocks_succ]
  have he : (4*zeroBlocks count suffix+2 : V) = (2*zeroBlocks count suffix+1)*2+0 := by ring
  rw [he]
  exact mod_mul_add_of_lt _ 2 (by simp : (0 : V) < 2)

theorem zeroBlocks_half (count suffix : V) :
    zeroBlocks (count+1) suffix / 2 = 2*zeroBlocks count suffix+1 := by
  rw [zeroBlocks_succ]
  have he : (4*zeroBlocks count suffix+2 : V) = 2*(2*zeroBlocks count suffix+1)+0 := by ring
  rw [he]
  exact div_mul_add' _ 2 (by simp : (0 : V) < 2)

theorem zeroBlocks_second_bit (count suffix : V) :
    (zeroBlocks (count+1) suffix / 2) % 2 = 1 := by
  rw [zeroBlocks_half]
  simpa only [mul_comm] using
    (mod_mul_add_of_lt (zeroBlocks count suffix) 2 (by simp : (1 : V) < 2))

theorem zeroBlocks_tail_two (count suffix : V) :
    zeroBlocks (count+1) suffix / 2 / 2 = zeroBlocks count suffix := by
  rw [zeroBlocks_half]
  exact div_mul_add' _ 2 (by simp : (1 : V) < 2)

theorem zeroBlocks_total (count suffix : V) :
    ∃! out, zeroBlocksDef.val.Evalb ![out,count,suffix] := by simp

/-- The ordinary Nat comparison uses the actual maintained tape-half codec.
It is separate from the universal internal arithmetic laws above. -/
theorem zeroBlocks_bitsCode (count : Nat) (suffix : List Bool) :
    zeroBlocks count (bitsCode suffix) =
      bitsCode ((List.replicate count [false,true]).flatten ++ suffix) := by
  induction count with
  | zero => simp [bitsCode]
  | succ count ih =>
    rw [zeroBlocks_succ, ih]
    simp only [List.replicate_succ, List.flatten_cons, List.append_assoc,
      List.cons_append, List.nil_append, bitsCode, Bool.toNat_false, Bool.toNat_true]
    omega

theorem zeroBlocksDef_bitsCode (out count : Nat) (suffix : List Bool) :
    zeroBlocksDef.val.Evalb ![out,count,bitsCode suffix] ↔
      out = bitsCode ((List.replicate count [false,true]).flatten ++ suffix) := by
  simp [zeroBlocks_bitsCode]

end SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254
