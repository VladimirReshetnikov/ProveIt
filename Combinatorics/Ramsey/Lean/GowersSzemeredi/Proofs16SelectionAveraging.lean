import GowersSzemeredi.Proofs16LineFreimanUnconditional

/-! The selection averaging behind Lemma 19 of arXiv:2109.03093.

Step 2 of the bilinear Bogolyubov argument chooses, for every `y`, a value
`f(y) ∈ U_y` with `|U_y| ≤ K`. The aim is for `f` to satisfy many prescribed
requirements at once. A requirement fixes `f` on a set `S` of at most four
points, to values allowed by the `U`'s. The paper chooses `f` at random: each
requirement holds with probability `≥ K⁻⁴`, so some `f` satisfies a `K⁻⁴`
fraction.

Here the argument is deterministic, by double counting over all selections
`Fintype.piFinset U`:
* the selections meeting a requirement form the product with `U_x` replaced
  by `{v x}` on `S` (`card_meeting`), so they make up at least `K^(−|S|)` of
  all selections (`card_all_le_mul_meeting`);
* summing over requirements, some selection meets at least `|T|/K⁴` of them
  (`exists_good_selection`).

With Corollary 7.6 and Lemma 7.8 in place of [49]'s Theorem 17, this is
the selection half of [49]'s Lemma 19. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

variable {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]

/-- A selection `f` meets a requirement `(S, v)`: `f = v` on `S`. -/
def Meets (f : X → Y) (r : Finset X × (X → Y)) : Prop := ∀ x ∈ r.1, f x = r.2 x

/-- The selections meeting a requirement form a product set. -/
theorem card_meeting (U : X → Finset Y) (r : Finset X × (X → Y))
    (hr : ∀ x ∈ r.1, r.2 x ∈ U x) :
    ((Fintype.piFinset U).filter fun f => Meets f r).card =
      ∏ x, (if x ∈ r.1 then 1 else (U x).card) := by
  have : (Fintype.piFinset U).filter (fun f => Meets f r) =
      Fintype.piFinset fun x => if x ∈ r.1 then {r.2 x} else U x := by
    ext f
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Meets]
    constructor
    · rintro ⟨hU, hm⟩ x
      by_cases hx : x ∈ r.1
      · rw [if_pos hx, Finset.mem_singleton]
        exact hm x hx
      · rw [if_neg hx]
        exact hU x
    · intro h
      refine ⟨fun x => ?_, fun x hx => ?_⟩
      · by_cases hx : x ∈ r.1
        · have := h x
          rw [if_pos hx, Finset.mem_singleton] at this
          rw [this]
          exact hr x hx
        · have := h x
          rwa [if_neg hx] at this
      · have := h x
        rwa [if_pos hx, Finset.mem_singleton] at this
  rw [this, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro x _
  split_ifs <;> simp

/-- All selections number at most `K^|S|` times those meeting `(S, v)`. -/
theorem card_all_le_mul_meeting (U : X → Finset Y) {K : Nat} (hK : ∀ x, (U x).card ≤ K)
    (r : Finset X × (X → Y)) (hr : ∀ x ∈ r.1, r.2 x ∈ U x) :
    (Fintype.piFinset U).card ≤
      K ^ r.1.card * ((Fintype.piFinset U).filter fun f => Meets f r).card := by
  rw [card_meeting U r hr, Fintype.card_piFinset]
  -- split both products over `S` and its complement
  rw [← Finset.prod_mul_prod_compl r.1, ← Finset.prod_mul_prod_compl r.1
    (fun x => if x ∈ r.1 then 1 else (U x).card)]
  have h1 : ∏ x ∈ r.1, (if x ∈ r.1 then 1 else (U x).card) = 1 :=
    Finset.prod_eq_one fun x hx => by rw [if_pos hx]
  have h2 : ∏ x ∈ r.1ᶜ, (if x ∈ r.1 then 1 else (U x).card) = ∏ x ∈ r.1ᶜ, (U x).card :=
    Finset.prod_congr rfl fun x hx => by rw [if_neg (Finset.mem_compl.mp hx)]
  have h3 : ∏ x ∈ r.1, (U x).card ≤ K ^ r.1.card := by
    calc ∏ x ∈ r.1, (U x).card ≤ ∏ _x ∈ r.1, K := Finset.prod_le_prod' fun x _ => hK x
      _ = K ^ r.1.card := Finset.prod_const K
  rw [h1, h2, one_mul]
  exact Nat.mul_le_mul_right _ h3

/-- **Selection averaging.** If every requirement fixes at most four points
to allowed values, and `1 ≤ K`, some selection meets at least `|T|/K⁴`
requirements. -/
theorem exists_good_selection (U : X → Finset Y) (hne : ∀ x, (U x).Nonempty) {K : Nat}
    (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K) (T : Finset (Finset X × (X → Y)))
    (hT : ∀ r ∈ T, r.1.card ≤ 4 ∧ ∀ x ∈ r.1, r.2 x ∈ U x) :
    ∃ f ∈ Fintype.piFinset U, T.card ≤ K ^ 4 * (T.filter fun r => Meets f r).card := by
  set F := Fintype.piFinset U
  have hFpos : 0 < F.card := by
    rw [Fintype.card_piFinset]
    exact Finset.prod_pos fun x _ => (hne x).card_pos
  -- each requirement is met by at least `|F|/K⁴` selections
  have hreq : ∀ r ∈ T, F.card ≤ K ^ 4 * (F.filter fun f => Meets f r).card := by
    intro r hr
    obtain ⟨hS, hv⟩ := hT r hr
    calc F.card ≤ K ^ r.1.card * (F.filter fun f => Meets f r).card :=
          card_all_le_mul_meeting U hK r hv
      _ ≤ K ^ 4 * (F.filter fun f => Meets f r).card :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hK1 hS)
  -- double counting
  have hdouble : ∑ f ∈ F, (T.filter fun r => Meets f r).card =
      ∑ r ∈ T, (F.filter fun f => Meets f r).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  by_contra hcon
  push Not at hcon
  have hlt : K ^ 4 * ∑ f ∈ F, (T.filter fun r => Meets f r).card < F.card * T.card := by
    rw [Finset.mul_sum]
    calc ∑ f ∈ F, K ^ 4 * (T.filter fun r => Meets f r).card
        < ∑ _f ∈ F, T.card := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hFpos)
          fun f hf => hcon f hf
      _ = F.card * T.card := by rw [Finset.sum_const, smul_eq_mul]
  have hge : F.card * T.card ≤ K ^ 4 * ∑ r ∈ T, (F.filter fun f => Meets f r).card := by
    rw [Finset.mul_sum]
    calc F.card * T.card = ∑ _r ∈ T, F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ r ∈ T, K ^ 4 * (F.filter fun f => Meets f r).card := Finset.sum_le_sum hreq
  rw [hdouble] at hlt
  omega

end LeanProofs.GowersSzemeredi
