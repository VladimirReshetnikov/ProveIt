import PA194TermShiftPR
namespace PA194VecShiftPR
open LO LO.FirstOrder LO.FirstOrder.Arithmetic M6.PA.RelationalSource
open PA194SourceSearchCoding PA194TermShiftPR
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

def vec2ShiftCode (v : Nat) : Nat :=
  Nat.pair (termShiftCode (v-1).unpair.1)
    (Nat.pair (termShiftCode ((v-1).unpair.2-1).unpair.1) 0 + 1) + 1

theorem vec2ShiftCode_primrec : Primrec vec2ShiftCode := by
  have hu : Primrec (fun n : Nat => (n - 1).unpair) := by
    simpa using Primrec.unpair.comp Primrec.pred
  have h1 := termShiftCode_primrec.comp (Primrec.fst.comp hu)
  have h2 := termShiftCode_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.pred.comp (Primrec.snd.comp hu))))
  have htail := Primrec.succ.comp (Primrec.encode.comp (h2.pair (Primrec.const (0 : Nat))))
  have hout := Primrec.succ.comp (Primrec.encode.comp (h1.pair htail))
  exact hout

theorem vec2ShiftCode_correct {n : Nat} (v : Fin 2 → SyntacticSemiterm language n) :
    vec2ShiftCode (Matrix.vecToNat fun i => Encodable.encode (v i)) =
      Matrix.vecToNat fun i => Encodable.encode (Rew.shift (v i)) := by
  simp [vec2ShiftCode, Matrix.vecToNat, Matrix.foldr_succ, Matrix.vecHead, Matrix.vecTail, termShiftCode_correct]

#print axioms vec2ShiftCode_primrec
#print axioms vec2ShiftCode_correct
end PA194VecShiftPR
