module
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Machine.PAInternalScanBits
public import PA196.Arithmetic.Machine.EndpointZipNatTape
@[expose] public section

namespace PA196.Arithmetic.Machine.PA.InternalTrace.ScanBits
open M6 PA196.Arithmetic.Machine.PA
/-- Standard-model calibration to the existing zipper's binary stack encoding.
This lemma calibrates the code; the PA scan proof uses model induction separately. -/
theorem repeat_bits (n : Nat) (b : Bool) (tail : List Bool) :
    repeatBits n b.toNat (ZipNatTape.bits tail) =
      ZipNatTape.bits (List.replicate n b ++ tail) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [repeat_succ,List.replicate_succ,ZipNatTape.bits_cons,NatTape.push,ih]
#print axioms repeat_bits
end PA196.Arithmetic.Machine.PA.InternalTrace.ScanBits

