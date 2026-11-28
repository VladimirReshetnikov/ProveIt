import Std

/-!
# A finite greedy covering lemma

A state is the span already reached, a move adds one translate, and
`missing` is the dimension still missing in the target space.
The list of choices contains the possible translates. The trace inequality in
the paper supplies the hypothesis on the sum when its coefficients are
rational and denominators are cleared. All calculations here are exact
natural-number inequalities. The Hilbert-space statements are proved in
the paper.
-/

namespace GreedyCoverAffine

private theorem sumGreaterOfAllGreater {choices : List α} {cap : Nat} {weight : α → Nat}
    (hne : choices ≠ []) (hgt : ∀ g ∈ choices, cap < weight g) :
    choices.length * cap < (choices.map weight).sum := by
  cases choices with
  | nil => contradiction
  | cons g gs =>
    have hfirst := hgt g (by simp)
    have htail : ∀ x ∈ gs, cap < weight x :=
      fun x hx => hgt x (List.mem_cons_of_mem _ hx)
    cases gs with
    | nil => simpa using hfirst
    | cons g' gs' =>
      have hrest := sumGreaterOfAllGreater (choices := g' :: gs')
        (by simp) htail
      simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Nat.add_lt_add hfirst hrest

/-- At least one choice is as good as a bound for the mean. -/
theorem existsChoice {choices : List α} (hne : choices ≠ [])
    {weight : α → Nat} {cap : Nat} (hmean : (choices.map weight).sum ≤ choices.length * cap) :
    ∃ g ∈ choices, weight g ≤ cap := by
  classical
  apply Classical.byContradiction
  intro hfail
  have hgt := sumGreaterOfAllGreater hne (fun g hg =>
    Nat.lt_of_not_ge (fun hle => hfail ⟨g, hg, hle⟩))
  exact (Nat.not_lt_of_ge hmean) hgt

/-- The homogeneous geometric sum, including its degenerate cases. -/
def geometricSum (num den : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => num ^ k + den * geometricSum num den k

/-- Expansion of the geometric sum against the difference of the two bases. -/
theorem geometricIdentity (num den k : Nat) (hbase : num ≤ den) :
    num ^ k + (den - num) * geometricSum num den k = den ^ k := by
  induction k with
  | zero => simp [geometricSum]
  | succ k ih =>
    have recstep : den * (num ^ k + (den - num) * geometricSum num den k)
        = den * den ^ k := congrArg (den * ·) ih
    have hadd : num + (den - num) = den := by omega
    calc
      num ^ (k+1) + (den - num) * geometricSum num den (k+1)
          = num ^ k * (num + (den - num)) + den * ((den - num) * geometricSum num den k) := by
            simp only [geometricSum, Nat.pow_succ, Nat.mul_add]
            ac_rfl
      _ = den * (num ^ k + (den - num) * geometricSum num den k) := by
            rw [hadd, Nat.mul_add, Nat.mul_comm (num ^ k) den]
      _ = den ^ (k+1) := by rw [recstep, Nat.pow_succ, Nat.mul_comm]

/-- A mean affine contraction yields a sequence of choices attaining its iterate. -/
theorem existsRun (choices : List α) (hne : choices ≠ []) (move : σ → α → σ)
    (missing : σ → Nat) (num den bias : Nat)
    (hmean : ∀ s, (choices.map (fun g => den * missing (move s g))).sum ≤
      choices.length * (num * missing s + bias)) (initial : σ) (k : Nat) :
    ∃ moves : List α, moves.length = k ∧ (∀ g ∈ moves, g ∈ choices) ∧
      den ^ k * missing (moves.foldl move initial) ≤ num ^ k * missing initial +
        bias * geometricSum num den k := by
  induction k generalizing initial with
  | zero => exact ⟨[], rfl, by simp, by simp [geometricSum]⟩
  | succ k ih =>
    obtain ⟨g, hg, hstep⟩ := existsChoice hne (hmean initial)
    obtain ⟨rest, hlen, hmem, hrun⟩ := ih (move initial g)
    refine ⟨g :: rest, by simp [hlen], ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hm
      · exact hg
      · exact hmem x hm
    · simp only [List.foldl_cons]
      calc
        den ^ (k + 1) * missing (rest.foldl move (move initial g))
            = den * (den ^ k * missing (rest.foldl move (move initial g))) := by
                rw [Nat.pow_succ]; ac_rfl
        _ ≤ den * (num ^ k * missing (move initial g) + bias * geometricSum num den k) :=
            Nat.mul_le_mul_left _ hrun
        _ = num ^ k * (den * missing (move initial g)) + den * (bias * geometricSum num den k) := by
            rw [Nat.mul_add]; ac_rfl
        _ ≤ num ^ k * (num * missing initial + bias) + den * (bias * geometricSum num den k) :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ hstep) _
        _ = num ^ (k + 1) * missing initial + bias * geometricSum num den (k+1) := by
            simp only [geometricSum, Nat.pow_succ, Nat.mul_add]
            ac_rfl

end GreedyCoverAffine

#print axioms GreedyCoverAffine.existsRun
