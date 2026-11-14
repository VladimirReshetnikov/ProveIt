import PA194SourceSearchCoding
namespace PA194TermShiftPR
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping M6.PA.RelationalSource
open PA194SourceSearchCoding
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

def termShiftCode (n : Nat) : Nat :=
  if n = 0 then 0
  else if (n - 1).unpair.1 = 1 then Nat.pair 1 ((n - 1).unpair.2 + 1) + 1 else n

theorem termShiftCode_primrec : Primrec termShiftCode := by
  have hu : Primrec (fun n : Nat => (n - 1).unpair) := by
    simpa using Primrec.unpair.comp Primrec.pred
  have ht : Primrec (fun n : Nat => (n - 1).unpair.1) := Primrec.fst.comp hu
  have hv : Primrec (fun n : Nat => (n - 1).unpair.2 + 1) := Primrec.succ.comp (Primrec.snd.comp hu)
  have hp : Primrec (fun n : Nat => Nat.pair 1 ((n - 1).unpair.2 + 1) + 1) := by
    have h := Primrec.succ.comp (Primrec.encode.comp ((Primrec.const (1 : Nat)).pair hv))
    simpa using h
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) hp Primrec.id)

theorem termShiftCode_correct {n : Nat} (t : SyntacticSemiterm language n) :
    termShiftCode (Encodable.encode t) = Encodable.encode (Rew.shift t) := by
  cases t with
  | bvar x => simp [termShiftCode, Semiterm.encode_eq_toNat, Semiterm.toNat, Rew.shift]
  | fvar x => simp [termShiftCode, Semiterm.encode_eq_toNat, Semiterm.toNat, Rew.shift]
  | func f v => exact nomatch f

theorem termShiftCode_eq_internal {n : Nat} (t : SyntacticSemiterm language n) :
    termShiftCode (Encodable.encode t) = termShift language (Encodable.encode t) := by
  cases t with
  | bvar x =>
    simpa [termShiftCode, Semiterm.encode_eq_toNat, Semiterm.toNat, qqBvar, nat_pair_eq] using
      (termShift_bvar (L := language) (V := Nat) (x : Nat)).symm
  | fvar x =>
    simpa [termShiftCode, Semiterm.encode_eq_toNat, Semiterm.toNat, qqFvar, nat_pair_eq] using
      (termShift_fvar (L := language) (V := Nat) x).symm
  | func f v => exact nomatch f

#print axioms termShiftCode_eq_internal
#print axioms termShiftCode_primrec
#print axioms termShiftCode_correct
end PA194TermShiftPR
