import PA194AtomShiftPR
namespace PA194FormulaShiftPR
open LO LO.FirstOrder LO.FirstOrder.Arithmetic M6.PA.RelationalSource
open PA194SourceSearchCoding PA194AtomShiftPR
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Syntactic code recursion. On malformed inputs this is simply a total code function. -/
def formulaShiftCode : Nat → Nat
  | 0 => 0
  | e+1 =>
    let tag := e.unpair.1
    let data := e.unpair.2
    if tag = 0 ∨ tag = 1 then atomShiftCode (e+1)
    else if tag = 2 ∨ tag = 3 then e+1
    else if tag = 4 ∨ tag = 5 then
      Nat.pair tag (Nat.pair (formulaShiftCode data.unpair.1)
        (formulaShiftCode data.unpair.2)) + 1
    else if tag = 6 ∨ tag = 7 then Nat.pair tag (formulaShiftCode data) + 1
    else 0
termination_by n => n
decreasing_by
  all_goals first
    | exact lt_of_le_of_lt (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) (Nat.lt_succ_self _)
    | exact lt_of_le_of_lt (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)) (Nat.lt_succ_self _)
    | exact Nat.lt_succ_of_le (Nat.unpair_right_le _)

theorem formulaShiftCode_correct {n : Nat} (p : Semiproposition language n) :
    formulaShiftCode (Encodable.encode p) = Encodable.encode (Semiformula.shift p) := by
  induction p using Semiformula.rec' with
  | hverum =>
    change formulaShiftCode (Nat.pair 2 0 + 1) = Nat.pair 2 0 + 1
    simp [formulaShiftCode]
  | hfalsum =>
    change formulaShiftCode (Nat.pair 3 0 + 1) = Nat.pair 3 0 + 1
    simp [formulaShiftCode]
  | hrel r v =>
    cases r with
    | eq =>
      have h := atomShiftCode_rel Relation.eq v
      simp only [Semiformula.encode_rel] at h ⊢
      rw [formulaShiftCode]
      simpa using h
    | mem =>
      have h := atomShiftCode_rel Relation.mem v
      simp only [Semiformula.encode_rel] at h ⊢
      rw [formulaShiftCode]
      simpa using h
  | hnrel r v =>
    cases r with
    | eq =>
      have h := atomShiftCode_nrel Relation.eq v
      simp only [Semiformula.encode_nrel] at h ⊢
      rw [formulaShiftCode]
      simpa using h
    | mem =>
      have h := atomShiftCode_nrel Relation.mem v
      simp only [Semiformula.encode_nrel] at h ⊢
      rw [formulaShiftCode]
      simpa using h
  | hand p q ihp ihq =>
    change formulaShiftCode (Nat.pair 4 (Nat.pair p.toNat q.toNat) + 1) =
      Nat.pair 4 (Nat.pair (Semiformula.shift p).toNat (Semiformula.shift q).toNat) + 1
    simp only [formulaShiftCode, Nat.unpair_pair]
    rw [← Semiformula.encode_eq_toNat p, ← Semiformula.encode_eq_toNat q,
      ihp, ihq]
    rfl
  | hor p q ihp ihq =>
    change formulaShiftCode (Nat.pair 5 (Nat.pair p.toNat q.toNat) + 1) =
      Nat.pair 5 (Nat.pair (Semiformula.shift p).toNat (Semiformula.shift q).toNat) + 1
    simp only [formulaShiftCode, Nat.unpair_pair]
    rw [← Semiformula.encode_eq_toNat p, ← Semiformula.encode_eq_toNat q,
      ihp, ihq]
    rfl
  | hall p ihp =>
    simp only [Semiformula.shift, Rewriting.shift, Rewriting.app_all, Rew.q_shift]
    change formulaShiftCode (Nat.pair 6 p.toNat + 1) = Nat.pair 6 (Semiformula.shift p).toNat + 1
    simp only [formulaShiftCode, Nat.unpair_pair]
    rw [← Semiformula.encode_eq_toNat p, ihp]
    rfl
  | hexs p ihp =>
    simp only [Semiformula.shift, Rewriting.shift, Rewriting.app_exs, Rew.q_shift]
    change formulaShiftCode (Nat.pair 7 p.toNat + 1) = Nat.pair 7 (Semiformula.shift p).toNat + 1
    simp only [formulaShiftCode, Nat.unpair_pair]
    rw [← Semiformula.encode_eq_toNat p, ihp]
    rfl

/-- The next value of the recursion table from values for smaller codes. -/
def tableStep (tab : List Nat) : Nat :=
  let n := tab.length
  if n = 0 then 0 else
    let e := n - 1
    let tag := e.unpair.1
    let data := e.unpair.2
    if tag = 0 ∨ tag = 1 then atomShiftCode n
    else if tag = 2 ∨ tag = 3 then n
    else if tag = 4 ∨ tag = 5 then
      Nat.pair tag (Nat.pair (tab.getD data.unpair.1 0) (tab.getD data.unpair.2 0)) + 1
    else if tag = 6 ∨ tag = 7 then Nat.pair tag (tab.getD data 0) + 1
    else 0

theorem tableStep_primrec : Primrec tableStep := by
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
  have ppair : Primrec (fun tab : List Nat => Nat.pair (tag tab) (Nat.pair (tab.getD (data tab).unpair.1 0)
      (tab.getD (data tab).unpair.2 0)) + 1) := by
    exact Primrec.succ.comp (Primrec.encode.comp (ptag.pair (Primrec.encode.comp (pleft.pair pright))))
  have pquant : Primrec (fun tab : List Nat => Nat.pair (tag tab) (tab.getD (data tab) 0) + 1) :=
    Primrec.succ.comp (Primrec.encode.comp (ptag.pair pchild))
  exact Primrec.ite (Primrec.eq.comp plen (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite ((Primrec.eq.comp ptag (Primrec.const 0)).or (Primrec.eq.comp ptag (Primrec.const 1)))
      (atomShiftCode_primrec.comp plen)
      (Primrec.ite ((Primrec.eq.comp ptag (Primrec.const 2)).or (Primrec.eq.comp ptag (Primrec.const 3)))
        plen (Primrec.ite ((Primrec.eq.comp ptag (Primrec.const 4)).or (Primrec.eq.comp ptag (Primrec.const 5)))
          ppair (Primrec.ite ((Primrec.eq.comp ptag (Primrec.const 6)).or (Primrec.eq.comp ptag (Primrec.const 7)))
            pquant (Primrec.const 0)))))

theorem tableStep_correct (n : Nat) :
    tableStep ((List.range n).map formulaShiftCode) = formulaShiftCode n := by
  cases n with
  | zero => simp [tableStep, formulaShiftCode]
  | succ e =>
    have hget (j : Nat) (hj : j < e+1) :
        ((List.range (e+1)).map formulaShiftCode).getD j 0 = formulaShiftCode j := by
      rw [List.getD_eq_getElem _ _ (by simpa using hj)]
      simp [List.getElem_map, List.getElem_range]
    have hdata : e.unpair.2 < e+1 := Nat.lt_succ_of_le (Nat.unpair_right_le e)
    have hleft : e.unpair.2.unpair.1 < e+1 :=
      lt_of_le_of_lt (Nat.unpair_left_le _) hdata
    have hright : e.unpair.2.unpair.2 < e+1 :=
      lt_of_le_of_lt (Nat.unpair_right_le _) hdata
    simp only [tableStep, List.length_map, List.length_range, Nat.succ_ne_zero, if_false,
      Nat.succ_sub_one, hget _ hleft, hget _ hright, hget _ hdata]
    rw [formulaShiftCode]

theorem formulaShiftCode_primrec : Primrec formulaShiftCode := by
  have hg : Primrec₂ (fun (_ : Unit) (tab : List Nat) => some (tableStep tab)) :=
    Primrec.option_some.comp (tableStep_primrec.comp Primrec.snd)
  have h : Primrec₂ (fun (_ : Unit) (n : Nat) => formulaShiftCode n) :=
    Primrec.nat_strong_rec _ hg (fun _ n => by simp only [tableStep_correct])
  exact h.comp (Primrec.const ()) Primrec.id

theorem codedSearch_primrec :
    Primrec₂ (fun (xs : List Nat) (q : Nat) => xs.find? (fun p => decide (formulaShiftCode p = q))) :=
  PA194SearchPR.search_primrec formulaShiftCode formulaShiftCode_primrec

theorem codedSearch_matches (xs : List (Proposition language)) (q : Proposition language) :
    (xs.map Encodable.encode).find? (fun p => decide (formulaShiftCode p = Encodable.encode q)) =
      (xs.find? (fun p => decide (Semiformula.shift p = q))).map Encodable.encode := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    by_cases h : Semiformula.shift p = q
    · have hc : formulaShiftCode (Encodable.encode p) = Encodable.encode q := by
        rw [formulaShiftCode_correct, h]
      simp [List.find?, h, hc]
    · have hc : formulaShiftCode (Encodable.encode p) ≠ Encodable.encode q := by
        rw [formulaShiftCode_correct]
        exact fun he => h (Encodable.encode_injective he)
      simp [List.find?, h, hc, ih]

theorem codedSearch_selected (xs : List (Proposition language)) (q : Proposition language)
    (h : q ∈ xs.map Semiformula.shift) :
    (xs.map Encodable.encode).find? (fun p => decide (formulaShiftCode p = Encodable.encode q)) =
      some (Encodable.encode (PA194Logic.Relational.Source.findPreimage xs Semiformula.shift q h).val) := by
  rw [codedSearch_matches, PA194SearchPR.search_eq_preimage xs Semiformula.shift q h]
  rfl

#print axioms codedSearch_primrec
#print axioms codedSearch_selected
#print axioms formulaShiftCode_primrec
#print axioms tableStep_correct
#print axioms tableStep_primrec
#print axioms formulaShiftCode_correct
end PA194FormulaShiftPR
