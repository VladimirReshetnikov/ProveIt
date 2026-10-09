import GowersSzemeredi.Proofs16BipartiteQuasirandom

/-! Boolean common-neighborhood counts and a quantitative bound for
missing witnesses. The threshold is the full predicted count, with no
extra factor from halving it. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def edgeIndicator {X Y : Type*} (E : X → Y → Prop) (x : X) (y : Y) : Real :=
  if E x y then 1 else 0

theorem commonCount_indicator {X Y I J : Type*} [Fintype X] [Fintype Y]
    [Fintype I] [Fintype J] (E : X → Y → Prop) (M : Finset (J → Y)) (x : I → X) :
    commonCount (edgeIndicator E) M x =
      ((M.filter fun w => ∀ i j, E (x i) (w j)).card : Real) := by
  have hp (w : J → Y) : (∏ q : I × J, edgeIndicator E (x q.1) (w q.2)) =
      if ∀ i j, E (x i) (w j) then 1 else 0 := by
    by_cases h : ∀ i j, E (x i) (w j)
    · simp [edgeIndicator, h]
    · rw [if_neg h]
      push Not at h
      obtain ⟨i, j, hij⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ (i, j)) (by simp [edgeIndicator, hij])
  simp only [commonCount, hp]
  simp

theorem commonCount_indicator_pos_iff {X Y I J : Type*} [Fintype X] [Fintype Y]
    [Fintype I] [Fintype J] (E : X → Y → Prop) (M : Finset (J → Y)) (x : I → X) :
    0 < commonCount (edgeIndicator E) M x ↔ ∃ w ∈ M, ∀ i j, E (x i) (w j) := by
  rw [commonCount_indicator]
  simp only [Nat.cast_pos, Finset.card_pos, Finset.filter_nonempty_iff]

theorem commonCount_indicator_eq_zero_iff {X Y I J : Type*} [Fintype X] [Fintype Y]
    [Fintype I] [Fintype J] (E : X → Y → Prop) (M : Finset (J → Y)) (x : I → X) :
    commonCount (edgeIndicator E) M x = 0 ↔ ¬ ∃ w ∈ M, ∀ i j, E (x i) (w j) := by
  rw [commonCount_indicator]
  simp

/-- Zero counts deviate by the entire predicted mass. -/
theorem common_neighbourhood_zero_card {X Y I J : Type*}
    [Fintype X] [Fintype Y] [Nonempty Y] [Fintype I] [Fintype J]
    {G : X → Y → Real} {delta epsilon tau : Real}
    (hG0 : ∀ x y, 0 ≤ G x y) (hG1 : ∀ x y, G x y ≤ 1)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) (heps : 0 ≤ epsilon) (htau : 0 ≤ tau)
    (hbox : boxSum (fun x y => G x y - delta) ≤
      epsilon^4 * (Fintype.card X : Real)^2 * (Fintype.card Y : Real)^2)
    (M : Finset (J → Y)) (hM : tau * Fintype.card (J → Y) ≤ (M.card : Real)) :
    ((Finset.univ.filter fun x : I → X => commonCount G M x = 0).card : Real) *
      (delta^(Fintype.card I * Fintype.card J) * tau)^2 ≤
      4 * Fintype.card I * Fintype.card J * epsilon * Fintype.card (I → X) := by
  let eta := delta^(Fintype.card I * Fintype.card J) * tau
  have heta : 0 ≤ eta := by positivity
  have hdev := common_neighbourhood_deviation_card (I := I) hG0 hG1 hd0 hd1 heps hbox M heta
  apply le_trans _ hdev
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg eta)
  exact_mod_cast Finset.card_le_card (show
    (Finset.univ.filter fun x : I → X => commonCount G M x = 0) ⊆
      (Finset.univ.filter fun x : I → X => eta * Fintype.card (J → Y) ≤
        |commonCount G M x - delta^(Fintype.card I * Fintype.card J) * M.card|) from by
    intro x hx
    have hz := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hz, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    dsimp [eta]
    have h := mul_le_mul_of_nonneg_left hM (pow_nonneg hd0 (Fintype.card I * Fintype.card J))
    simpa only [mul_assoc] using h)

/-- At most the stated number of tuples have no common witness in M. -/
theorem common_neighbourhood_no_witness_card {X Y I J : Type*}
    [Fintype X] [Fintype Y] [Nonempty Y] [Fintype I] [Fintype J]
    (E : X → Y → Prop) {delta epsilon tau : Real}
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) (heps : 0 ≤ epsilon) (htau : 0 ≤ tau)
    (hbox : boxSum (fun x y => edgeIndicator E x y - delta) ≤
      epsilon^4 * (Fintype.card X : Real)^2 * (Fintype.card Y : Real)^2)
    (M : Finset (J → Y)) (hM : tau * Fintype.card (J → Y) ≤ (M.card : Real)) :
    ((Finset.univ.filter fun x : I → X => ¬ ∃ w ∈ M, ∀ i j, E (x i) (w j)).card : Real) *
      (delta^(Fintype.card I * Fintype.card J) * tau)^2 ≤
      4 * Fintype.card I * Fintype.card J * epsilon * Fintype.card (I → X) := by
  have h := common_neighbourhood_zero_card (I := I)
    (G := edgeIndicator E) (fun x y => by unfold edgeIndicator; split_ifs <;> norm_num)
    (fun x y => by unfold edgeIndicator; split_ifs <;> norm_num) hd0 hd1 heps htau hbox M hM
  simpa only [commonCount_indicator_eq_zero_iff] using h

/-- The single-vertex form, with no function-space encoding in the bound. -/
theorem vertex_no_witness_card {X Y J : Type*}
    [Fintype X] [Fintype Y] [Nonempty Y] [Fintype J]
    (E : X → Y → Prop) {delta epsilon tau : Real}
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) (heps : 0 ≤ epsilon) (htau : 0 ≤ tau)
    (hbox : boxSum (fun x y => edgeIndicator E x y - delta) ≤
      epsilon^4 * (Fintype.card X : Real)^2 * (Fintype.card Y : Real)^2)
    (M : Finset (J → Y)) (hM : tau * Fintype.card (J → Y) ≤ (M.card : Real)) :
    ((Finset.univ.filter fun x : X => ¬ ∃ w ∈ M, ∀ j, E x (w j)).card : Real) *
      (delta^(Fintype.card J) * tau)^2 ≤
      4 * Fintype.card J * epsilon * Fintype.card X := by
  have h := common_neighbourhood_no_witness_card (I := Unit) E hd0 hd1 heps htau hbox M hM
  have hc : (Finset.univ.filter fun x : X => ¬ ∃ w ∈ M, ∀ j, E x (w j)).card =
      (Finset.univ.filter fun x : Unit → X => ¬ ∃ w ∈ M, ∀ i j, E (x i) (w j)).card := by
    apply Finset.card_bij (fun x _ => fun _ : Unit => x)
    · intro x hx
      simpa using hx
    · intro x hx y hy heq
      exact congrFun heq ()
    · intro x hx
      refine ⟨x (), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rintro ⟨w, hw, he⟩
        apply (Finset.mem_filter.mp hx).2
        refine ⟨w, hw, fun i j => ?_⟩
        cases i
        exact he j
      · funext i
        cases i
        rfl
  simp only [Fintype.card_unit, one_mul, Fintype.card_fun, pow_one,
    Nat.cast_one, mul_one] at h
  convert h using 1
  congr 2
  convert hc using 1
  congr 1
  ext x
  simp

end LeanProofs.GowersSzemeredi
