import FiniteCube

namespace BudgetAnalysis.BitIntegral

/-- Fixed denominator 2^d; cut-off ask at depth zero is unreachable under Bounded. -/
def numerator : Nat → T → Hist → Int
  | 0, .ret z, _ => z
  | 0, .ask _ _, _ => 0
  | d+1, .ret z, _ => 2^(d+1) * z
  | d+1, .ask q next, h =>
    match h q with
    | some b => 2 * numerator d (next b) h
    | none => numerator d (next false) (record h q false) +
              numerator d (next true) (record h q true)

theorem numerator_ret (d : Nat) (z : Int) (h : Hist) :
    numerator d (.ret z) h = 2^d * z := by
  cases d <;> simp [numerator]

/-- No contribution to the denominator depends on the magnitude of a bit address. -/
theorem numerator_correct {t : T} {d : Nat} (ht : Dialogue.Bounded t d)
    (qs : List Nat) (nd : qs.Nodup) (o : Oracle) :
    (2^qs.length : Int) * numerator d t (context qs o) =
      2^d * total (fun x => Dialogue.eval x t) (cube qs o) := by
  induction ht generalizing qs o with
  | ret z d =>
    rw [numerator_ret]
    change _ = 2^d * total (fun _ => z) (cube qs o)
    rw [total_const, cube_length]
    simp only [Int.natCast_pow, Int.cast_ofNat_Int]
    ac_rfl
  | ask q next d _ ih =>
    by_cases mem : q ∈ qs
    · have fresh : context qs o q = none := by simp [context, mem]
      rw [numerator]
      simp only [fresh]
      change _ = 2^(d+1) * total (fun x => Dialogue.eval x (next (x q))) (cube qs o)
      rw [total_partition _ q (fun b x => Dialogue.eval x (next b))]
      simp only [cube_slice qs nd o q mem, record_context qs nd]
      have F := ih false _ (nd.erase q) (put o q false)
      have G := ih true _ (nd.erase q) (put o q true)
      have len : qs.length = (qs.erase q).length + 1 := by
        have pos := List.length_pos_of_mem mem
        have dif := List.length_erase_of_mem mem
        omega
      have double : (2 ^ qs.length : Int) = 2 * 2 ^ (qs.erase q).length := by
        rw [len, Int.pow_succ]; ac_rfl
      rw [double, Int.mul_assoc, Int.mul_add, F, G, ← Int.mul_add,
          Int.pow_succ]
      ac_rfl
    · have fixed : context qs o q = some (o q) := by simp [context, mem]
      rw [numerator]
      simp only [fixed]
      have same : total (fun x => Dialogue.eval x (.ask q next)) (cube qs o) =
          total (fun x => Dialogue.eval x (next (o q))) (cube qs o) := by
        apply total_congr
        intro x hx
        simp [Dialogue.eval, cube_fixed _ o q mem x hx]
      rw [same, Int.mul_left_comm, ih (o q) qs nd o, Int.pow_succ]
      ac_rfl

end BudgetAnalysis.BitIntegral
