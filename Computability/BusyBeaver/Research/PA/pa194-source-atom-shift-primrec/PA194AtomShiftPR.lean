import PA194VecShiftPR
set_option maxHeartbeats 1000000
namespace PA194AtomShiftPR
open LO LO.FirstOrder LO.FirstOrder.Arithmetic M6.PA.RelationalSource
open PA194SourceSearchCoding PA194VecShiftPR
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

def atomShiftCode (c : Nat) : Nat :=
  let p := (c-1).unpair
  let q := p.2.unpair
  let r := q.2.unpair
  Nat.pair p.1 (Nat.pair q.1 (Nat.pair r.1 (vec2ShiftCode r.2))) + 1

theorem atomShiftCode_primrec : Primrec atomShiftCode := by
  apply Primrec.nat_iff.mpr
  have tag : Nat.Primrec (fun n => (n-1).unpair.1) := Nat.Primrec.left.comp Nat.Primrec.pred
  have arity : Nat.Primrec (fun n => (n-1).unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.pred)
  have rel : Nat.Primrec (fun n => (n-1).unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.pred))
  have vec : Nat.Primrec (fun n => (n-1).unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.pred))
  exact Nat.Primrec.succ.comp (tag.pair (arity.pair (rel.pair ((Primrec.nat_iff.mp vec2ShiftCode_primrec).comp vec))))

theorem atomShiftCode_rel {n : Nat} (r : Relation 2) (v : Fin 2 → SyntacticSemiterm language n) :
    atomShiftCode (Encodable.encode (Semiformula.rel r v)) =
      Encodable.encode (Semiformula.shift (Semiformula.rel r v)) := by
  simp [atomShiftCode, Semiformula.encode_rel, Semiformula.shift, vec2ShiftCode_correct]

theorem atomShiftCode_nrel {n : Nat} (r : Relation 2) (v : Fin 2 → SyntacticSemiterm language n) :
    atomShiftCode (Encodable.encode (Semiformula.nrel r v)) =
      Encodable.encode (Semiformula.shift (Semiformula.nrel r v)) := by
  simp [atomShiftCode, Semiformula.encode_nrel, Semiformula.shift, vec2ShiftCode_correct]

#print axioms atomShiftCode_primrec
#print axioms atomShiftCode_rel
#print axioms atomShiftCode_nrel
end PA194AtomShiftPR
