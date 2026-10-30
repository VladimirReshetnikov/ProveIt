import DiophantineConsistency.HerbrandSchedule
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandTupleSchedule
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage HerbrandSchedule

abbrev Tuple := Fin 4 → SyntacticTerm language
def bound (t : Tuple) : ℕ := Finset.univ.sup (fun i => HerbrandSchedule.bound (t i))

theorem lt_bound (t : Tuple) (k : Fin 4) {i : ℕ} (h : (t k).FVar? i) : i < bound t := by
  have hi := HerbrandSchedule.lt_bound (t k) h
  have hk : HerbrandSchedule.bound (t k) ≤ bound t := Finset.le_sup (f := fun i => HerbrandSchedule.bound (t i)) (Finset.mem_univ k)
  omega

def stage (t : Tuple) : ℕ := Nat.pair (Encodable.encode t) (bound t) + 1

def candidate : ℕ → Tuple
  | 0 => fun _ => zeroTerm
  | j+1 => match Encodable.decode (Nat.unpair j).1 with
    | none => fun _ => zeroTerm
    | some t => if bound t = (Nat.unpair j).2 then t else fun _ => zeroTerm

theorem candidate_stage (t : Tuple) : candidate (stage t) = t := by
  simp [candidate, stage, Encodable.encodek]

theorem candidate_before (j : ℕ) (k : Fin 4) {i : ℕ} (hi : ((candidate j) k).FVar? i) : i < j := by
  cases j with
  | zero => simp [candidate, zeroTerm, Semiterm.FVar?] at hi
  | succ j =>
      cases hd : (Encodable.decode (Nat.unpair j).1 : Option Tuple) with
      | none => simp [candidate, hd, zeroTerm, Semiterm.FVar?] at hi
      | some t =>
        by_cases hb : bound t = (Nat.unpair j).2
        · have ht' : (t k).FVar? i := by simpa [candidate, hd, hb] using hi
          have ht := lt_bound t k ht'
          have hp := Nat.unpair_right_le j
          omega
        · simp [candidate, hd, hb, zeroTerm, Semiterm.FVar?] at hi
end DiophantineConsistency.HerbrandTupleSchedule
