import GRHArticle.ProgressionFree.PolynomialNaturalExchangeWeights

/-!
# Explicit gains in the valuation exchange

For at least five linear factors, two elementary power bounds give a
uniform lower bound on the exchange bracket. For field sizes 2, 3 and 4
we use the first eight greedy exponent terms.
-/

namespace GRHArticle.ProgressionFree

/-- The part of the density gain left after extracting the common cofactor
density and one copy of each selected prime weight. -/
noncomputable def naturalExchangeBracket (w : List ℝ) : ℝ :=
  (w.map (1 + ·)).prod - 1 - (w.map positiveGreedyWeight).prod

private theorem lower_quadratic_binomial {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    1 + n*x + n*(n-1)*x^2/2 ≤ (1+x)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (1+x), Nat.cast_succ]
    have hc : 0 ≤ (n : ℝ)*((n : ℝ)-1) := by
      cases n with
      | zero => simp
      | succ k => simp; positivity
    have h := mul_le_mul_of_nonneg_right ih (show 0 ≤ 1+x by linarith)
    nlinarith only [h, mul_nonneg hc (pow_nonneg hx 3)]

private theorem one_sub_mul_pow_upper {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (1+x)^n * (1 - n*x) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, mul_assoc]
    apply le_trans (mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith : 0 ≤ 1+x) n)) ih
    nlinarith only [mul_nonneg (show 0 ≤ (n:ℝ)+1 by positivity) (sq_nonneg x)]

/-- With `q ≥ 5` linear factors the bracket is at least `1/15`. -/
theorem naturalExchangeBracket_linear_lower (q : ℕ) (hq : 5 ≤ q) :
    (1:ℝ)/15 ≤ naturalExchangeBracket (List.replicate q (1/(q:ℝ))) := by
  let a : ℝ := q
  have ha : 5 ≤ a := by dsimp [a]; exact_mod_cast hq
  have ha₀ : 0 < a := by linarith
  have ha₁ : 0 < a-1 := by linarith
  let x := 1/(a*(a-1))
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hw : 1/a < 1 := (div_lt_one ha₀).mpr (by linarith)
  have hT : positiveGreedyWeight (1/a) ≤ 1+x := by
    apply (positiveGreedyWeight_le_quadratic (by positivity) hw).trans_eq
    dsimp [x]; field_simp
  have hgeom := one_sub_mul_pow_upper hx q
  change (1+x)^q * (1-a*x) ≤ 1 at hgeom
  have hax : a*x = 1/(a-1) := by dsimp [x]; field_simp
  have hax' : a*x ≤ 1/4 := by rw [hax]; apply (div_le_div_iff₀ ha₁ (by norm_num)).mpr; linarith
  have htp : positiveGreedyWeight (1/a)^q ≤ 4/3 := by
    have hb := mul_le_mul_of_nonneg_left (show 3/4 ≤ 1-a*x by linarith)
      (pow_nonneg (by linarith : 0 ≤ 1+x) q)
    apply (pow_le_pow_left₀ (positiveGreedyWeight_nonneg (by positivity)) hT q).trans
    linarith only [hb, hgeom]
  have hbin := lower_quadratic_binomial (show 0 ≤ 1/a by positivity) q
  change 1 + a*(1/a) + a*(a-1)*(1/a)^2/2 ≤ _ at hbin
  have he : 1 + a*(1/a) + a*(a-1)*(1/a)^2/2 = 2 + (a-1)/(2*a) := by field_simp; ring
  have hl : 2/5 ≤ (a-1)/(2*a) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  rw [he] at hbin
  simp only [naturalExchangeBracket, List.map_replicate, List.prod_replicate]
  change 1/15 ≤ (1+1/a)^q - 1 - positiveGreedyWeight (1/a)^q
  linarith only [hbin, hl, htp]

private noncomputable def upperEight (w : ℝ) : ℝ := 1+w^2+w^3+w^8/(1-w)

private theorem prod_positiveGreedyWeight_le (l : List ℝ)
    (hl : ∀ w ∈ l, 0 ≤ w ∧ w < 1) :
    (l.map positiveGreedyWeight).prod ≤ (l.map upperEight).prod := by
  induction l with
  | nil => simp
  | cons w l ih =>
    have hw := hl w (by simp)
    have ht (v : ℝ) (hv : v ∈ l) := hl v (by simp [hv])
    simp only [List.map_cons, List.prod_cons]
    apply mul_le_mul (positiveGreedyWeight_le_eight hw.1 hw.2) (ih ht)
    · apply List.prod_nonneg
      intro x hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      exact positiveGreedyWeight_nonneg (ht v hv).1
    · exact (positiveGreedyWeight_nonneg hw.1).trans (positiveGreedyWeight_le_eight hw.1 hw.2)

private theorem bracket_finite_lower (l : List ℝ) (hl : ∀ w ∈ l, 0 ≤ w ∧ w < 1) :
    (l.map (1 + ·)).prod - 1 - (l.map upperEight).prod ≤ naturalExchangeBracket l :=
  sub_le_sub_left (prod_positiveGreedyWeight_le l hl) _

/-- The three small-field rows use the respective degree multisets
`[1,1,2,3]`, `[1,1,1,2]`, and `[1,1,1,1]`. -/
theorem naturalExchangeBracket_small :
    (6622:ℝ)/100000 < naturalExchangeBracket [1/2,1/2,1/4,1/8] ∧
    (9852:ℝ)/100000 < naturalExchangeBracket [1/3,1/3,1/3,1/9] ∧
    (9023:ℝ)/100000 < naturalExchangeBracket [1/4,1/4,1/4,1/4] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    apply lt_of_lt_of_le _ (bracket_finite_lower _ (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> norm_num)) <;>
    norm_num [upperEight]

/-- Lower estimate for the full gain using only the squarefree cofactor bound. -/
noncomputable def naturalExchangeGainLower (z : ℝ) (w : List ℝ) : ℝ :=
  (1-z) * (w.map (fun x ↦ (1-x)*x)).prod * naturalExchangeBracket w

/-- The three density gain estimates in the article's table, certified against
the rational geometric-tail bounds. -/
theorem naturalExchangeGainLower_small :
    (4244:ℝ)/100000000 < naturalExchangeGainLower (1/2) [1/2,1/2,1/4,1/8] ∧
    (7119:ℝ)/100000000 < naturalExchangeGainLower (1/3) [1/3,1/3,1/3,1/9] ∧
    (8364:ℝ)/100000000 < naturalExchangeGainLower (1/4) [1/4,1/4,1/4,1/4] := by
  unfold naturalExchangeGainLower
  refine ⟨?_, ?_, ?_⟩ <;>
    apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_left (bracket_finite_lower _ (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> norm_num)) (by norm_num)) <;>
    norm_num [upperEight]

end GRHArticle.ProgressionFree
