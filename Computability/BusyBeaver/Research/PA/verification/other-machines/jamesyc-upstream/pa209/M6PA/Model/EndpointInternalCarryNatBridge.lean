module
public import M6PA.Model.PATheory
public import M6PA.Model.PAInternalCarryCode
public import M6PA.Model.EndpointInternalScanNatBridge
@[expose] public section

namespace M6.Arithmetic.PA.InternalTrace.CarryCode
open M6 M6.Arithmetic.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ScanBits

/-- The existing Foundation HFS vector code of a standard list. -/
noncomputable def fileCode : List Nat → Nat
  | [] => 0
  | p::ps => p ∷ fileCode ps

@[simp] theorem fileCode_nil : fileCode [] = 0 := rfl
@[simp] theorem fileCode_cons (p : Nat) (ps : List Nat) :
    fileCode (p::ps) = p ∷ fileCode ps := rfl

theorem right_standard (vs : List Nat) (tail : List Bool) :
    rightFile (fileCode vs) (ZipNatTape.bits tail) =
      ZipNatTape.bits (Runtime.sepsR vs ++ tail) := by
  induction vs with
  | nil => simp [Runtime.sepsR]
  | cons p ps ih =>
    rw [fileCode_cons,right_adjoin,ih]
    have hb := repeat_bits p true (Runtime.sepsR ps ++ tail)
    simp only [Bool.toNat_true] at hb
    rw [hb]
    simp [Native.sepsR_cons,List.replicate_succ,ZipNatTape.bits_cons,NatTape.push] <;> omega

theorem left_standard (vs : List Nat) (left : List Bool) :
    leftFile (fileCode vs) (ZipNatTape.bits left) =
      ZipNatTape.bits ((Native.carryR vs).reverse ++ left) := by
  induction vs generalizing left with
  | nil => simp [Native.carryR]
  | cons p ps ih =>
    have hbits : repeatBits p 1 (4*ZipNatTape.bits left+2) =
        ZipNatTape.bits (List.replicate p true ++ false::true::left) := by
      rw [show 4*ZipNatTape.bits left+2 = 2*(2*ZipNatTape.bits left+1) by omega]
      simpa [ZipNatTape.bits_cons,NatTape.push] using repeat_bits p true (false::true::left)
    rw [fileCode_cons,left_adjoin]
    apply Eq.trans (congrArg (leftFile (fileCode ps)) hbits)
    rw [ih]
    simp [Native.carryR_cons,List.reverse_append,List.reverse_replicate,List.append_assoc]

theorem cost_standard (vs : List Nat) :
    cost (fileCode vs) = (vs.map fun p => p+2).sum := by
  induction vs with
  | nil => simp
  | cons p ps ih => simp [ih]

#print axioms right_standard
#print axioms left_standard
#print axioms cost_standard
end M6.Arithmetic.PA.InternalTrace.CarryCode

