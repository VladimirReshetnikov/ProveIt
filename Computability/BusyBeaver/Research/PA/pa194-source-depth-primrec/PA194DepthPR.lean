import PA194FormulaShiftPR
namespace PA194DepthPR
open LO LO.FirstOrder LO.FirstOrder.Arithmetic M6.PA.RelationalSource
open PA194SourceSearchCoding
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

def depthCode : Nat → Nat
  | 0 => 0
  | e+1 =>
    let tag := e.unpair.1
    let data := e.unpair.2
    if tag = 4 ∨ tag = 5 then max (depthCode data.unpair.1) (depthCode data.unpair.2)
    else if tag = 6 ∨ tag = 7 then depthCode data + 1
    else 0
termination_by n => n
decreasing_by
  all_goals first
    | exact lt_of_le_of_lt (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) (Nat.lt_succ_self _)
    | exact lt_of_le_of_lt (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)) (Nat.lt_succ_self _)
    | exact Nat.lt_succ_of_le (Nat.unpair_right_le _)

theorem depthCode_correct {n : Nat} (p : Semiproposition language n) :
    depthCode (Encodable.encode p) = depth p := by
  induction p using Semiformula.rec' with
  | hverum => change depthCode (Nat.pair 2 0 + 1) = 0; simp [depthCode]
  | hfalsum => change depthCode (Nat.pair 3 0 + 1) = 0; simp [depthCode]
  | hrel r v =>
    cases r <;> simp [Semiformula.encode_eq_toNat, Semiformula.toNat, depthCode, depth]
  | hnrel r v =>
    cases r <;> simp [Semiformula.encode_eq_toNat, Semiformula.toNat, depthCode, depth]
  | hand p q ihp ihq =>
    change depthCode (Nat.pair 4 (Nat.pair p.toNat q.toNat) + 1) = max (depth p) (depth q)
    simp only [depthCode, Nat.unpair_pair]
    rw [← Semiformula.encode_eq_toNat p, ← Semiformula.encode_eq_toNat q, ihp, ihq]
    simp
  | hor p q ihp ihq =>
    change depthCode (Nat.pair 5 (Nat.pair p.toNat q.toNat) + 1) = max (depth p) (depth q)
    simp only [depthCode, Nat.unpair_pair]
    rw [← Semiformula.encode_eq_toNat p, ← Semiformula.encode_eq_toNat q, ihp, ihq]
    simp
  | hall p ihp =>
    change depthCode (Nat.pair 6 p.toNat + 1) = depth p + 1
    simp only [depthCode, Nat.unpair_pair]
    rw [← Semiformula.encode_eq_toNat p, ihp]
    simp
  | hexs p ihp =>
    change depthCode (Nat.pair 7 p.toNat + 1) = depth p + 1
    simp only [depthCode, Nat.unpair_pair]
    rw [← Semiformula.encode_eq_toNat p, ihp]
    simp

def depthStep (tab : List Nat) : Nat :=
  let n := tab.length
  if n = 0 then 0 else
    let e := n - 1
    let tag := e.unpair.1
    let data := e.unpair.2
    if tag = 4 ∨ tag = 5 then max (tab.getD data.unpair.1 0) (tab.getD data.unpair.2 0)
    else if tag = 6 ∨ tag = 7 then tab.getD data 0 + 1
    else 0

theorem depthStep_primrec : Primrec depthStep := by
  let len : List Nat → Nat := List.length
  let tag : List Nat → Nat := fun tab => (len tab - 1).unpair.1
  let data : List Nat → Nat := fun tab => (len tab - 1).unpair.2
  have plen : Primrec len := Primrec.list_length
  have ptag : Primrec tag := (Primrec.fst.comp (Primrec.unpair.comp Primrec.pred)).comp plen
  have pdata : Primrec data := (Primrec.snd.comp (Primrec.unpair.comp Primrec.pred)).comp plen
  have pleft : Primrec (fun tab : List Nat => tab.getD (data tab).unpair.1 0) :=
    Primrec.list_getD 0 |>.comp Primrec.id (Primrec.fst.comp (Primrec.unpair.comp pdata))
  have pright : Primrec (fun tab : List Nat => tab.getD (data tab).unpair.2 0) :=
    Primrec.list_getD 0 |>.comp Primrec.id (Primrec.snd.comp (Primrec.unpair.comp pdata))
  have pchild : Primrec (fun tab : List Nat => tab.getD (data tab) 0) :=
    Primrec.list_getD 0 |>.comp Primrec.id pdata
  exact Primrec.ite (Primrec.eq.comp plen (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite ((Primrec.eq.comp ptag (Primrec.const 4)).or (Primrec.eq.comp ptag (Primrec.const 5)))
      (Primrec.nat_max.comp pleft pright)
      (Primrec.ite ((Primrec.eq.comp ptag (Primrec.const 6)).or (Primrec.eq.comp ptag (Primrec.const 7)))
        (Primrec.succ.comp pchild) (Primrec.const 0)))

theorem depthStep_correct (n : Nat) :
    depthStep ((List.range n).map depthCode) = depthCode n := by
  cases n with
  | zero => simp [depthStep, depthCode]
  | succ e =>
    have hget (j : Nat) (hj : j < e+1) :
        ((List.range (e+1)).map depthCode).getD j 0 = depthCode j := by
      rw [List.getD_eq_getElem _ _ (by simpa using hj)]
      simp [List.getElem_map, List.getElem_range]
    have hdata : e.unpair.2 < e+1 := Nat.lt_succ_of_le (Nat.unpair_right_le e)
    have hleft : e.unpair.2.unpair.1 < e+1 := lt_of_le_of_lt (Nat.unpair_left_le _) hdata
    have hright : e.unpair.2.unpair.2 < e+1 := lt_of_le_of_lt (Nat.unpair_right_le _) hdata
    simp only [depthStep, List.length_map, List.length_range, Nat.succ_ne_zero, if_false,
      Nat.succ_sub_one, hget _ hleft, hget _ hright, hget _ hdata]
    rw [depthCode]

theorem depthCode_primrec : Primrec depthCode := by
  have hg : Primrec₂ (fun (_ : Unit) (tab : List Nat) => some (depthStep tab)) :=
    Primrec.option_some.comp (depthStep_primrec.comp Primrec.snd)
  have h : Primrec₂ (fun (_ : Unit) (n : Nat) => depthCode n) :=
    Primrec.nat_strong_rec _ hg (fun _ n => by simp only [depthStep_correct])
  exact h.comp (Primrec.const ()) Primrec.id

def sequentDepthCode (xs : List Nat) : Nat := xs.foldr (fun x r => max (depthCode x) r) 0

theorem sequentDepthCode_primrec : Primrec sequentDepthCode := by
  have hstep : Primrec₂ (fun (_ : List Nat) (p : Nat × Nat) => max (depthCode p.1) p.2) :=
    (Primrec.nat_max.comp (depthCode_primrec.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) hstep

theorem sequentDepthCode_correct (xs : List (Proposition language)) :
    sequentDepthCode (xs.map Encodable.encode) =
      PA194Logic.Relational.Source.sequentDepth (xs : PA194Logic.Relational.Source.SourceSequent) := by
  simp [sequentDepthCode, PA194Logic.Relational.Source.sequentDepth,
    Multiset.coe_foldr, List.foldr_map, depthCode_correct]

#print axioms sequentDepthCode_primrec
#print axioms sequentDepthCode_correct
#print axioms depthCode_primrec
#print axioms depthStep_correct
#print axioms depthStep_primrec
#print axioms depthCode_correct
end PA194DepthPR
