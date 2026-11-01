import DiophantineConsistency.PRAWitnessFormulaFunctions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-! # Growth of syntax codes in `𝗜𝚺₁`

Witness bounds in negated positions need the values of the syntax functions
bounded by their arguments. Codes are built by pairing, and
`tau X D = 2^((X + 4) · 2^D)` is closed under it: two codes below `tau X D`
pair below `tau X (D + 2)` (`pair_le_tau`). Formula induction then bounds
`neg`, `shift` and `subst` doubly exponentially; for `subst` the parameter
grows at quantifiers (`qVec`), but only by squaring its entries
(`qVec_entries`), which costs two more levels of `tau` per quantifier. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessCodeGrowth
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open PRAWitnessTermFunctions PRAWitnessSetTerms PRAWitnessRepeatVec PRAWitnessFormulaFunctions

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The tower `tau` -/

/-- `tau X D = 2^((X + 4) · 2^D)`. -/
noncomputable def tau (X D : V) : V := Exp.exp ((X + 4) * Exp.exp D)

instance tau_definable : 𝚺₁-Function₂ (tau : V → V → V) := by
  unfold tau; definability

theorem le_tauE (X D : V) : X + 4 ≤ (X + 4) * Exp.exp D :=
  le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (exp_pos D))

theorem lt_tau (X D : V) : X + 4 < tau X D := lt_of_le_of_lt (le_tauE X D) (lt_exp _)

theorem le_tau (X D : V) : X ≤ tau X D := le_trans le_self_add (le_of_lt (lt_tau X D))

theorem four_le_tau (X D : V) : 4 ≤ tau X D := le_trans le_add_self (le_of_lt (lt_tau X D))

theorem tau_mono {X X' D D' : V} (hX : X ≤ X') (hD : D ≤ D') : tau X D ≤ tau X' D' :=
  exp_monotone_le.mpr (mul_le_mul' (add_le_add hX le_rfl) (exp_monotone_le.mpr hD))

theorem tau_strict (X : V) {D D' : V} (hD : D < D') : tau X D < tau X D' := by
  unfold tau
  exact exp_monotone.mpr (mul_lt_mul_of_pos_left (exp_monotone.mpr hD) (by positivity))

theorem tau_add_two (X D : V) : tau X (D + 2) = tau X D * tau X D * (tau X D * tau X D) := by
  unfold tau
  rw [exp_add, exp_two_eq]
  have h : (X + 4) * (Exp.exp D * (2 * 2)) =
      ((X + 4) * Exp.exp D + (X + 4) * Exp.exp D) + ((X + 4) * Exp.exp D + (X + 4) * Exp.exp D) := by
    ring
  rw [h]; simp only [exp_add]

theorem quartic_key (T : V) (hT : 4 ≤ T) : (T + T + 1) * (T + T + 1) + 1 ≤ T * T * (T * T) := by
  obtain ⟨u, rfl⟩ := le_iff_exists_add.mp hT
  have h : (4 + u) * (4 + u) * ((4 + u) * (4 + u)) =
      ((4 + u) + (4 + u) + 1) * ((4 + u) + (4 + u) + 1) + 1 +
        (174 + 220 * u + 92 * u * u + 16 * u * u * u + u * u * u * u) := by ring
  rw [h]; exact le_self_add

/-- **Pairing costs two levels of `tau`.** -/
theorem pair_le_tau {a b X D : V} (ha : a ≤ tau X D) (hb : b ≤ tau X D) :
    ⟪a, b⟫ + 1 ≤ tau X (D + 2) := by
  rw [tau_add_two]
  exact le_trans (add_le_add (pair_le_sq ha hb) le_rfl) (quartic_key _ (four_le_tau X D))

theorem sq_le_tau {t X D : V} (ht : t ≤ tau X D) : (t + 1) * (t + 1) + 1 ≤ tau X (D + 2) := by
  rw [tau_add_two]
  have h1 : t + 1 ≤ tau X D + tau X D + 1 := add_le_add (le_trans ht le_self_add) le_rfl
  exact le_trans (add_le_add (mul_le_mul' h1 h1) le_rfl) (quartic_key _ (four_le_tau X D))

theorem tau_add_le (X D v : V) : tau X D + v ≤ tau (X + v) D := by
  have e1 : (X + v + 4) * Exp.exp D = (X + 4) * Exp.exp D + v * Exp.exp D := by ring
  unfold tau
  rw [e1, exp_add]
  have h2 : v + 1 ≤ Exp.exp (v * Exp.exp D) :=
    lt_iff_succ_le.mp (lt_of_lt_of_le (lt_exp v)
      (exp_monotone_le.mpr (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (exp_pos D)))))
  have hT : 1 ≤ Exp.exp ((X + 4) * Exp.exp D) := pos_iff_one_le.mp (exp_pos _)
  calc Exp.exp ((X + 4) * Exp.exp D) + v
      ≤ Exp.exp ((X + 4) * Exp.exp D) + Exp.exp ((X + 4) * Exp.exp D) * v :=
        add_le_add le_rfl (le_mul_of_one_le_left (by simp) hT)
    _ = Exp.exp ((X + 4) * Exp.exp D) * (v + 1) := by ring
    _ ≤ Exp.exp ((X + 4) * Exp.exp D) * Exp.exp (v * Exp.exp D) := mul_le_mul' le_rfl h2

theorem code2_le_tau {c a X D : V} (hc : c ≤ tau X D) (ha : a ≤ tau X D) :
    ⟪c, a⟫ + 1 ≤ tau X (D + 2) := pair_le_tau hc ha

theorem code3_le_tau {c a b X D : V} (hc : c ≤ tau X D) (ha : a ≤ tau X D) (hb : b ≤ tau X D) :
    ⟪c, a, b⟫ + 1 ≤ tau X (D + 2 + 2) :=
  pair_le_tau (le_trans hc (tau_mono le_rfl le_self_add)) (le_trans le_self_add (pair_le_tau ha hb))

theorem code4_le_tau {c k R v X D : V} (hc : c ≤ tau X D) (hk : k ≤ tau X D) (hR : R ≤ tau X D)
    (hv : v ≤ tau X D) : ⟪c, k, R, v⟫ + 1 ≤ tau X (D + 2 + 2 + 2) :=
  pair_le_tau (le_trans hc (tau_mono le_rfl (le_trans le_self_add le_self_add)))
    (le_trans le_self_add (code3_le_tau hk hR hv))

theorem repeatVec_le_tau {m X D : V} (hm : m ≤ tau X D) : ∀ k, repeatVec m k ≤ tau X (D + 2 * k) := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    rw [repeatVec_succ, adjoin_def, show D + 2 * (k + 1) = D + 2 * k + 2 by ring]
    exact pair_le_tau (le_trans hm (tau_mono le_rfl le_self_add)) ih

/-! ### Formula codes -/

theorem lt_pair_right_of_pos {c : V} (hc : 0 < c) (x : V) : x < ⟪c, x⟫ :=
  lt_of_le_of_lt (le_pair_right 0 x) (pair_lt_pair_left hc x)

theorem add_two_le_and_left (p q : V) : p + 2 ≤ p ^⋏ q := by
  have h : p < ⟪4, ⟪p, q⟫⟫ := lt_of_le_of_lt (le_pair_left p q) (lt_pair_right_of_pos (by simp) _)
  simpa [qqAnd, add_assoc, one_add_one_eq_two] using add_le_add (lt_iff_succ_le.mp h) (le_refl 1)

theorem add_two_le_and_right (p q : V) : q + 2 ≤ p ^⋏ q := by
  have h : q < ⟪4, ⟪p, q⟫⟫ := lt_of_le_of_lt (le_pair_right p q) (lt_pair_right_of_pos (by simp) _)
  simpa [qqAnd, add_assoc, one_add_one_eq_two] using add_le_add (lt_iff_succ_le.mp h) (le_refl 1)

theorem add_two_le_or_left (p q : V) : p + 2 ≤ p ^⋎ q := by
  have h : p < ⟪5, ⟪p, q⟫⟫ := lt_of_le_of_lt (le_pair_left p q) (lt_pair_right_of_pos (by simp) _)
  simpa [qqOr, add_assoc, one_add_one_eq_two] using add_le_add (lt_iff_succ_le.mp h) (le_refl 1)

theorem add_two_le_or_right (p q : V) : q + 2 ≤ p ^⋎ q := by
  have h : q < ⟪5, ⟪p, q⟫⟫ := lt_of_le_of_lt (le_pair_right p q) (lt_pair_right_of_pos (by simp) _)
  simpa [qqOr, add_assoc, one_add_one_eq_two] using add_le_add (lt_iff_succ_le.mp h) (le_refl 1)

theorem add_two_le_all (p : V) : p + 2 ≤ ^∀ p := by
  have h : p < ⟪6, p⟫ := lt_pair_right_of_pos (by simp) p
  simpa [qqAll, add_assoc, one_add_one_eq_two] using add_le_add (lt_iff_succ_le.mp h) (le_refl 1)

theorem add_two_le_exs (p : V) : p + 2 ≤ ^∃ p := by
  have h : p < ⟪7, p⟫ := lt_pair_right_of_pos (by simp) p
  simpa [qqExs, add_assoc, one_add_one_eq_two] using add_le_add (lt_iff_succ_le.mp h) (le_refl 1)

/-! ### Negation and shift -/

theorem small_le (P : V) {n : ℕ} (hn : n ≤ 8) : (n : V) ≤ P + 8 :=
  le_trans (by exact_mod_cast hn) le_add_self

theorem depth6_le (A : V) : (0 : V) + 2 + 2 + 2 ≤ A + 6 := by
  rw [show (0 : V) + 2 + 2 + 2 = 6 by norm_num]; exact le_add_self

theorem depth2_le (A : V) : (0 : V) + 2 ≤ A + 6 := by
  rw [show (0 : V) + 2 = 2 by norm_num]; exact le_trans (by norm_num) (le_add_self (a := (6 : V)) (b := A))

theorem depth_step {p P : V} (h : p + 2 ≤ P) : 2 * p + 6 ≤ 2 * P + 2 := by
  calc 2 * p + 6 = 2 * (p + 2) + 2 := by ring
    _ ≤ 2 * P + 2 := add_le_add (mul_le_mul' le_rfl h) le_rfl

theorem depth_three (P : V) : 2 * P + 2 + 2 + 2 ≤ 2 * P + 6 := le_of_eq (by ring)

theorem depth_two (P : V) : 2 * P + 2 + 2 ≤ 2 * P + 6 :=
  le_trans (le_of_eq (by ring)) (add_le_add le_rfl (by norm_num : (4 : V) ≤ 6))

theorem depth_k {k P : V} (h : k ≤ P) : 0 + 2 * k + 2 + 2 + 2 ≤ 2 * P + 6 :=
  le_trans (le_of_eq (by ring)) (add_le_add (mul_le_mul' le_rfl h) le_rfl)

theorem le_tau_of (P c D : V) (h : c ≤ P + 8) : c ≤ tau (P + 8) D := le_trans h (le_tau _ _)

/-- Small constants lie below any `tau (Y + 8) D`; `_h` only fixes `Y` and `D`. -/
theorem le_tau_of' {Y D t : V} (n : ℕ) (_h : t ≤ tau (Y + 8) D) (hn : n ≤ 8 := by norm_num) :
    (n : V) ≤ tau (Y + 8) D :=
  le_tau_of Y n D (small_le Y hn)

private theorem lift_tau_bound {p P y : V} {f : V → V} (hf : Monotone f)
    (hp : p + 2 ≤ P) (hy : y ≤ tau (f p + 8) (2 * p + 6)) :
    y ≤ tau (f P + 8) (2 * P + 2) :=
  le_trans hy (tau_mono (add_le_add (hf (le_trans le_self_add hp)) le_rfl) (depth_step hp))

private theorem lift_tau_id {p P y : V} (hp : p + 2 ≤ P)
    (hy : y ≤ tau (p + 8) (2 * p + 6)) : y ≤ tau (P + 8) (2 * P + 2) :=
  lift_tau_bound (f := fun x => x) (fun _ _ h => h) hp hy

private theorem lift_tau_sq {p P y : V} (hp : p + 2 ≤ P)
    (hy : y ≤ tau ((p + 2) * (p + 2) + 1 + 8) (2 * p + 6)) :
    y ≤ tau ((P + 2) * (P + 2) + 1 + 8) (2 * P + 2) :=
  lift_tau_bound (f := fun x => (x + 2) * (x + 2) + 1) (fun _ _ h => sq2_mono h) hp hy

/-- **Negation is doubly exponentially bounded.** -/
theorem neg_le : ∀ p : V, IsUFormula ℒₛₑₜ p → neg ℒₛₑₜ p ≤ tau (p + 8) (2 * p + 6) := by
  refine IsUFormula.ISigma1.sigma1_succ_induction (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k R v hR hv
    rw [neg_rel hR hv]
    set P := ^rel k R v
    have h := code4_le_tau (le_tau_of P 1 0 (by simpa using small_le P (n := 1) (by norm_num)))
      (le_tau_of P k 0 (le_trans (arity_lt_rel k R v).le le_self_add))
      (le_tau_of P R 0 (le_trans (r_lt_rel k R v).le le_self_add))
      (le_tau_of P v 0 (le_trans (v_lt_rel k R v).le le_self_add))
    exact le_trans (by simpa [qqNRel] using h) (tau_mono le_rfl (depth6_le _))
  · intro k R v hR hv
    rw [neg_nrel hR hv]
    set P := ^nrel k R v
    have h := code4_le_tau (le_tau_of P 0 0 (by simp))
      (le_tau_of P k 0 (le_trans (arity_lt_nrel k R v).le le_self_add))
      (le_tau_of P R 0 (le_trans (r_lt_nrel k R v).le le_self_add))
      (le_tau_of P v 0 (le_trans (v_lt_nrel k R v).le le_self_add))
    exact le_trans (by simpa [qqRel] using h) (tau_mono le_rfl (depth6_le _))
  · rw [neg_verum]
    have h := code2_le_tau (le_tau_of (^⊤ : V) 3 0 (by simpa using small_le (^⊤ : V) (n := 3) (by norm_num)))
      (le_tau_of (^⊤ : V) 0 0 (by simp))
    exact le_trans (by simpa [qqFalsum] using h) (tau_mono le_rfl (depth2_le _))
  · rw [neg_falsum]
    have h := code2_le_tau (le_tau_of (^⊥ : V) 2 0 (by simpa using small_le (^⊥ : V) (n := 2) (by norm_num)))
      (le_tau_of (^⊥ : V) 0 0 (by simp))
    exact le_trans (by simpa [qqVerum] using h) (tau_mono le_rfl (depth2_le _))
  · intro p q hp hq ihp ihq
    rw [neg_and hp hq]
    set P := p ^⋏ q
    have hp2 := add_two_le_and_left p q; have hq2 := add_two_le_and_right p q
    have hnp : neg ℒₛₑₜ p ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hp2 ihp
    have hnq : neg ℒₛₑₜ q ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hq2 ihq
    have h := code3_le_tau (le_tau_of' 5 hnp) hnp hnq
    exact le_trans (by simpa [qqOr] using h) (tau_mono le_rfl (depth_three P))
  · intro p q hp hq ihp ihq
    rw [neg_or hp hq]
    set P := p ^⋎ q
    have hp2 := add_two_le_or_left p q; have hq2 := add_two_le_or_right p q
    have hnp : neg ℒₛₑₜ p ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hp2 ihp
    have hnq : neg ℒₛₑₜ q ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hq2 ihq
    have h := code3_le_tau (le_tau_of' 4 hnp) hnp hnq
    exact le_trans (by simpa [qqAnd] using h) (tau_mono le_rfl (depth_three P))
  · intro p hp ihp
    rw [neg_all hp]
    set P := ^∀ p
    have hp2 := add_two_le_all p
    have hnp : neg ℒₛₑₜ p ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hp2 ihp
    have h := code2_le_tau (le_tau_of' 7 hnp) hnp
    exact le_trans (by simpa [qqExs] using h) (tau_mono le_rfl (depth_two P))
  · intro p hp ihp
    rw [neg_ex hp]
    set P := ^∃ p
    have hp2 := add_two_le_exs p
    have hnp : neg ℒₛₑₜ p ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hp2 ihp
    have h := code2_le_tau (le_tau_of' 6 hnp) hnp
    exact le_trans (by simpa [qqAll] using h) (tau_mono le_rfl (depth_two P))

/-- **Shift is doubly exponentially bounded.** -/
theorem shift_le : ∀ p : V, IsUFormula ℒₛₑₜ p →
    shift ℒₛₑₜ p ≤ tau ((p + 2) * (p + 2) + 1 + 8) (2 * p + 6) := by
  refine IsUFormula.ISigma1.sigma1_succ_induction (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k R v hR hv
    rw [shift_rel hR hv]
    set P := ^rel k R v
    have hkP : k ≤ P := (arity_lt_rel k R v).le
    have hRP : R ≤ P := (r_lt_rel k R v).le
    have hvP : v ≤ P := (v_lt_rel k R v).le
    have hY {c : V} (h : c ≤ P) (D : V) : c ≤ tau ((P + 2) * (P + 2) + 1 + 8) D :=
      le_tau_of _ c D (le_trans (le_trans h (le_sq2 P)) le_self_add)
    have hv' : termShiftVec ℒₛₑₜ k v ≤ tau ((P + 2) * (P + 2) + 1 + 8) (0 + 2 * k) :=
      le_trans (termShiftVec_le k v) (repeatVec_le_tau
        (le_tau_of _ _ 0 (le_trans (sq2_mono hvP) le_self_add)) k)
    have h := code4_le_tau (le_tau_of' 0 hv') (hY hkP _) (hY hRP _) hv'
    exact le_trans (by simpa [qqRel] using h) (tau_mono le_rfl (depth_k hkP))
  · intro k R v hR hv
    rw [shift_nrel hR hv]
    set P := ^nrel k R v
    have hkP : k ≤ P := (arity_lt_nrel k R v).le
    have hRP : R ≤ P := (r_lt_nrel k R v).le
    have hvP : v ≤ P := (v_lt_nrel k R v).le
    have hY {c : V} (h : c ≤ P) (D : V) : c ≤ tau ((P + 2) * (P + 2) + 1 + 8) D :=
      le_tau_of _ c D (le_trans (le_trans h (le_sq2 P)) le_self_add)
    have hv' : termShiftVec ℒₛₑₜ k v ≤ tau ((P + 2) * (P + 2) + 1 + 8) (0 + 2 * k) :=
      le_trans (termShiftVec_le k v) (repeatVec_le_tau
        (le_tau_of _ _ 0 (le_trans (sq2_mono hvP) le_self_add)) k)
    have h := code4_le_tau (le_tau_of' 1 hv') (hY hkP _) (hY hRP _) hv'
    exact le_trans (by simpa [qqNRel] using h) (tau_mono le_rfl (depth_k hkP))
  · rw [shift_verum]
    have h := code2_le_tau (le_tau_of' (Y := ((^⊤ : V) + 2) * ((^⊤ : V) + 2) + 1) (D := 0) 2 (le_tau _ _))
      (le_tau_of' (Y := ((^⊤ : V) + 2) * ((^⊤ : V) + 2) + 1) (D := 0) 0 (le_tau _ _))
    exact le_trans (by simpa [qqVerum] using h) (tau_mono le_rfl (depth2_le _))
  · rw [shift_falsum]
    have h := code2_le_tau (le_tau_of' (Y := ((^⊥ : V) + 2) * ((^⊥ : V) + 2) + 1) (D := 0) 3 (le_tau _ _))
      (le_tau_of' (Y := ((^⊥ : V) + 2) * ((^⊥ : V) + 2) + 1) (D := 0) 0 (le_tau _ _))
    exact le_trans (by simpa [qqFalsum] using h) (tau_mono le_rfl (depth2_le _))
  · intro p q hp hq ihp ihq
    rw [shift_and hp hq]
    set P := p ^⋏ q
    have hp2 := add_two_le_and_left p q; have hq2 := add_two_le_and_right p q
    have hnp : shift ℒₛₑₜ p ≤ tau ((P + 2) * (P + 2) + 1 + 8) (2 * P + 2) :=
      lift_tau_sq hp2 ihp
    have hnq : shift ℒₛₑₜ q ≤ tau ((P + 2) * (P + 2) + 1 + 8) (2 * P + 2) :=
      lift_tau_sq hq2 ihq
    have h := code3_le_tau (le_tau_of' 4 hnp) hnp hnq
    exact le_trans (by simpa [qqAnd] using h) (tau_mono le_rfl (depth_three P))
  · intro p q hp hq ihp ihq
    rw [shift_or hp hq]
    set P := p ^⋎ q
    have hp2 := add_two_le_or_left p q; have hq2 := add_two_le_or_right p q
    have hnp : shift ℒₛₑₜ p ≤ tau ((P + 2) * (P + 2) + 1 + 8) (2 * P + 2) :=
      lift_tau_sq hp2 ihp
    have hnq : shift ℒₛₑₜ q ≤ tau ((P + 2) * (P + 2) + 1 + 8) (2 * P + 2) :=
      lift_tau_sq hq2 ihq
    have h := code3_le_tau (le_tau_of' 5 hnp) hnp hnq
    exact le_trans (by simpa [qqOr] using h) (tau_mono le_rfl (depth_three P))
  · intro p hp ihp
    rw [shift_all hp]
    set P := ^∀ p
    have hp2 := add_two_le_all p
    have hnp : shift ℒₛₑₜ p ≤ tau ((P + 2) * (P + 2) + 1 + 8) (2 * P + 2) :=
      lift_tau_sq hp2 ihp
    have h := code2_le_tau (le_tau_of' 6 hnp) hnp
    exact le_trans (by simpa [qqAll] using h) (tau_mono le_rfl (depth_two P))
  · intro p hp ihp
    rw [shift_exs hp]
    set P := ^∃ p
    have hp2 := add_two_le_exs p
    have hnp : shift ℒₛₑₜ p ≤ tau ((P + 2) * (P + 2) + 1 + 8) (2 * P + 2) :=
      lift_tau_sq hp2 ihp
    have h := code2_le_tau (le_tau_of' 7 hnp) hnp
    exact le_trans (by simpa [qqExs] using h) (tau_mono le_rfl (depth_two P))

/-! ### Substitution -/

/-- `qVec` squares the entries of a parameter, at most. -/
theorem qVec_entries {w X D : V} (hw : ∀ j < len w, w.[j] ≤ tau X D) :
    ∀ j, (qVec ℒₛₑₜ w).[j] ≤ tau X (D + 2) := by
  intro j
  have h1 : (1 : V) ≤ tau X (D + 2) := le_trans (by norm_num) (four_le_tau X (D + 2))
  simp only [qVec]
  rcases zero_or_succ j with rfl | ⟨i, rfl⟩
  · simpa [qqBvar, pair] using h1
  · rw [nth_adjoin_succ]
    by_cases hv : IsUTermVec ℒₛₑₜ (len w) w
    · by_cases hi : i < len w
      · rw [nth_termBShiftVec hv hi]; exact le_trans (termBShift_le _) (sq_le_tau (hw i hi))
      · rw [nth_lt_len (by rw [len_termBShiftVec hv]; exact not_lt.mp hi)]; simp
    · simp [termBShiftVec, hv]

theorem len_qVec_le (w : V) : len (qVec ℒₛₑₜ w) ≤ w + 1 := by
  simp only [qVec, len_adjoin]
  refine add_le_add ?_ le_rfl
  by_cases hv : IsUTermVec ℒₛₑₜ (len w) w
  · rw [len_termBShiftVec hv]; exact len_le w
  · simp [termBShiftVec, hv]

/-- **`qVec` is doubly exponentially bounded.** -/
theorem qVec_le (w : V) : qVec ℒₛₑₜ w ≤ tau w (2 * w + 4) := by
  have he := qVec_entries (w := w) (X := w) (D := 0) (fun j _ => le_trans (nth_le w j) (le_tau w 0))
  have h := len_repeatVec_of_nth_le (v := qVec ℒₛₑₜ w) (m := tau w (0 + 2)) (fun i _ => he i)
  refine le_trans h (le_trans (repeatVec_mono _ _ _ (len_qVec_le w))
    (le_trans (repeatVec_le_tau le_rfl (w + 1)) (tau_mono le_rfl (le_of_eq (by ring)))))

theorem termSubst_entry_le {w t E : V} (hw : ∀ j < len w, w.[j] ≤ E) :
    termSubst ℒₛₑₜ w t ≤ E + t := by
  by_cases ht : IsUTerm ℒₛₑₜ t
  · rcases IsUTerm.case ht with ⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hkf, -, -⟩
    · rw [termSubst_bvar]
      by_cases hz : z < len w
      · exact le_trans (hw z hz) le_self_add
      · rw [nth_lt_len (not_lt.mp hz)]; simp
    · rw [termSubst_fvar]; exact le_add_self
    · exact absurd hkf (not_isFunc k f)
  · simp [termSubst, Language.TermRec.Construction.result_prop_not _ _ _ ht]

theorem termSubstVec_le_entries2 {k w v E F : V} (hw : ∀ j < len w, w.[j] ≤ E)
    (hv : IsUTermVec ℒₛₑₜ k v) (hF : ∀ i < k, v.[i] ≤ F) :
    termSubstVec ℒₛₑₜ k w v ≤ repeatVec (E + F) k := by
  have hl := len_termSubstVec (w := w) hv
  have h := len_repeatVec_of_nth_le (v := termSubstVec ℒₛₑₜ k w v) (m := E + F)
    (fun i hi => by
      rw [hl] at hi
      rw [nth_termSubstVec hv hi]
      exact le_trans (termSubst_entry_le hw) (add_le_add le_rfl (hF i hi)))
  rwa [hl] at h

theorem termSubstVec_le_entries {k w v E : V} (hw : ∀ j < len w, w.[j] ≤ E) :
    termSubstVec ℒₛₑₜ k w v ≤ repeatVec (E + v) k := by
  by_cases hv : IsUTermVec ℒₛₑₜ k v
  · exact termSubstVec_le_entries2 hw hv (fun i _ => nth_le v i)
  · simp [termSubstVec, hv]

theorem sdepth_bin {p P : V} (h : p + 2 ≤ P) (D : V) : D + 4 * p + 6 ≤ D + 4 * P + 2 := by
  calc D + 4 * p + 6 ≤ D + 4 * (p + 2) + 2 := by
        rw [show D + 4 * (p + 2) + 2 = D + 4 * p + 6 + 4 by ring]; exact le_self_add
    _ ≤ D + 4 * P + 2 := add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl h)) le_rfl

theorem sdepth_all {p P : V} (h : p + 2 ≤ P) (D : V) : D + 2 + 4 * p + 6 ≤ D + 4 * P + 4 := by
  calc D + 2 + 4 * p + 6 = D + 4 * (p + 2) := by ring
    _ ≤ D + 4 * P := add_le_add le_rfl (mul_le_mul' le_rfl h)
    _ ≤ D + 4 * P + 4 := le_self_add

theorem sdepth_leaf {k P : V} (hk : k ≤ P) (D : V) :
    D + 2 * P + 2 * k + 2 + 2 + 2 ≤ D + 4 * P + 6 := by
  calc D + 2 * P + 2 * k + 2 + 2 + 2 = D + 2 * P + 2 * k + 6 := by ring
    _ ≤ D + 2 * P + 2 * P + 6 := add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hk)) le_rfl
    _ = D + 4 * P + 6 := by ring

/-- **Substitution is doubly exponentially bounded**, given a bound on the
entries of the substituted vector. -/
theorem subst_le : ∀ p : V, IsUFormula ℒₛₑₜ p → ∀ w X D : V, (∀ j < len w, w.[j] ≤ tau X D) →
    subst ℒₛₑₜ w p ≤ tau (X + p + 8) (D + 4 * p + 6) := by
  refine IsUFormula.ISigma1.pi1_succ_induction (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k R v hR hv w X D hw
    rw [substs_rel hR hv]
    set P := ^rel k R v
    have hkP : k ≤ P := (arity_lt_rel k R v).le
    have hRP : R ≤ P := (r_lt_rel k R v).le
    have hvP : v ≤ P := (v_lt_rel k R v).le
    have hm : tau X D + v ≤ tau (X + P + 8) (D + 2 * P) :=
      le_trans (tau_add_le X D v) (tau_mono (le_trans (add_le_add le_rfl hvP) le_self_add) le_self_add)
    have hv' : termSubstVec ℒₛₑₜ k w v ≤ tau (X + P + 8) (D + 2 * P + 2 * k) :=
      le_trans (termSubstVec_le_entries hw)
        (le_trans (repeatVec_mono_left hm k) (repeatVec_le_tau le_rfl k))
    have hY {c : V} (h : c ≤ P) : c ≤ tau (X + P + 8) (D + 2 * P + 2 * k) :=
      le_tau_of _ c _ (le_trans (le_trans h le_add_self) le_self_add)
    have h := code4_le_tau (le_tau_of' 0 hv') (hY hkP) (hY hRP) hv'
    exact le_trans (by simpa [qqRel] using h) (tau_mono le_rfl (sdepth_leaf hkP D))
  · intro k R v hR hv w X D hw
    rw [substs_nrel hR hv]
    set P := ^nrel k R v
    have hkP : k ≤ P := (arity_lt_nrel k R v).le
    have hRP : R ≤ P := (r_lt_nrel k R v).le
    have hvP : v ≤ P := (v_lt_nrel k R v).le
    have hm : tau X D + v ≤ tau (X + P + 8) (D + 2 * P) :=
      le_trans (tau_add_le X D v) (tau_mono (le_trans (add_le_add le_rfl hvP) le_self_add) le_self_add)
    have hv' : termSubstVec ℒₛₑₜ k w v ≤ tau (X + P + 8) (D + 2 * P + 2 * k) :=
      le_trans (termSubstVec_le_entries hw)
        (le_trans (repeatVec_mono_left hm k) (repeatVec_le_tau le_rfl k))
    have hY {c : V} (h : c ≤ P) : c ≤ tau (X + P + 8) (D + 2 * P + 2 * k) :=
      le_tau_of _ c _ (le_trans (le_trans h le_add_self) le_self_add)
    have h := code4_le_tau (le_tau_of' 1 hv') (hY hkP) (hY hRP) hv'
    exact le_trans (by simpa [qqNRel] using h) (tau_mono le_rfl (sdepth_leaf hkP D))
  · intro w X D hw
    rw [substs_verum]
    exact le_trans (le_trans le_add_self le_self_add) (le_tau _ _)
  · intro w X D hw
    rw [substs_falsum]
    exact le_trans (le_trans le_add_self le_self_add) (le_tau _ _)
  · intro p q hp hq ihp ihq w X D hw
    rw [substs_and hp hq]
    set P := p ^⋏ q
    have hp2 := add_two_le_and_left p q; have hq2 := add_two_le_and_right p q
    have hnp : subst ℒₛₑₜ w p ≤ tau (X + P + 8) (D + 4 * P + 2) :=
      le_trans (ihp w X D hw) (tau_mono (add_le_add (add_le_add le_rfl (le_trans le_self_add hp2)) le_rfl)
        (sdepth_bin hp2 D))
    have hnq : subst ℒₛₑₜ w q ≤ tau (X + P + 8) (D + 4 * P + 2) :=
      le_trans (ihq w X D hw) (tau_mono (add_le_add (add_le_add le_rfl (le_trans le_self_add hq2)) le_rfl)
        (sdepth_bin hq2 D))
    have h := code3_le_tau (le_tau_of' 4 hnp) hnp hnq
    exact le_trans (by simpa [qqAnd] using h) (tau_mono le_rfl (le_of_eq (by ring)))
  · intro p q hp hq ihp ihq w X D hw
    rw [substs_or hp hq]
    set P := p ^⋎ q
    have hp2 := add_two_le_or_left p q; have hq2 := add_two_le_or_right p q
    have hnp : subst ℒₛₑₜ w p ≤ tau (X + P + 8) (D + 4 * P + 2) :=
      le_trans (ihp w X D hw) (tau_mono (add_le_add (add_le_add le_rfl (le_trans le_self_add hp2)) le_rfl)
        (sdepth_bin hp2 D))
    have hnq : subst ℒₛₑₜ w q ≤ tau (X + P + 8) (D + 4 * P + 2) :=
      le_trans (ihq w X D hw) (tau_mono (add_le_add (add_le_add le_rfl (le_trans le_self_add hq2)) le_rfl)
        (sdepth_bin hq2 D))
    have h := code3_le_tau (le_tau_of' 5 hnp) hnp hnq
    exact le_trans (by simpa [qqOr] using h) (tau_mono le_rfl (le_of_eq (by ring)))
  · intro p hp ihp w X D hw
    rw [substs_all hp]
    set P := ^∀ p
    have hp2 := add_two_le_all p
    have hnp : subst ℒₛₑₜ (qVec ℒₛₑₜ w) p ≤ tau (X + P + 8) (D + 4 * P + 4) :=
      le_trans (ihp (qVec ℒₛₑₜ w) X (D + 2) (fun j _ => qVec_entries hw j))
        (tau_mono (add_le_add (add_le_add le_rfl (le_trans le_self_add hp2)) le_rfl) (sdepth_all hp2 D))
    have h := code2_le_tau (le_tau_of' 6 hnp) hnp
    exact le_trans (by simpa [qqAll] using h) (tau_mono le_rfl (le_of_eq (by ring)))
  · intro p hp ihp w X D hw
    rw [substs_ex hp]
    set P := ^∃ p
    have hp2 := add_two_le_exs p
    have hnp : subst ℒₛₑₜ (qVec ℒₛₑₜ w) p ≤ tau (X + P + 8) (D + 4 * P + 4) :=
      le_trans (ihp (qVec ℒₛₑₜ w) X (D + 2) (fun j _ => qVec_entries hw j))
        (tau_mono (add_le_add (add_le_add le_rfl (le_trans le_self_add hp2)) le_rfl) (sdepth_all hp2 D))
    have h := code2_le_tau (le_tau_of' 7 hnp) hnp
    exact le_trans (by simpa [qqExs] using h) (tau_mono le_rfl (le_of_eq (by ring)))

/-! ### The stage of a substitution -/

/-- The fixpoint construction of `subst`. -/
noncomputable abbrev substFix : Fixpoint.Construction V ((Substs.blueprint ℒₛₑₜ).blueprint ℒₛₑₜ) :=
  (Substs.construction ℒₛₑₜ).construction ℒₛₑₜ

/-- The stage bound `tau (X + p + 8) (D + 2ℓ + 8p + 12)`. -/
noncomputable def stage (X D ℓ p : V) : V := tau (X + p + 8) (D + 2 * ℓ + 8 * p + 12)

theorem len_qVec_le_len (w : V) : len (qVec ℒₛₑₜ w) ≤ len w + 1 := by
  simp only [qVec, len_adjoin]
  refine add_le_add ?_ le_rfl
  by_cases hv : IsUTermVec ℒₛₑₜ (len w) w
  · rw [len_termBShiftVec hv]
  · simp [termBShiftVec, hv]

theorem triple_lt_stage {w p y X D ℓ : V} (hw : ∀ j < len w, w.[j] ≤ tau X D) (hl : len w ≤ ℓ)
    (hy : y ≤ tau (X + p + 8) (D + 4 * p + 6)) : ⟪w, p, y⟫ + 1 ≤ stage X D ℓ p := by
  have hE1 : D + 2 * ℓ ≤ D + 2 * ℓ + 4 * p + 6 := le_trans le_self_add le_self_add
  have hE2 : D + 4 * p + 6 ≤ D + 2 * ℓ + 4 * p + 6 := by
    rw [show D + 2 * ℓ + 4 * p + 6 = D + 4 * p + 6 + 2 * ℓ by ring]; exact le_self_add
  have hwE : w ≤ tau (X + p + 8) (D + 2 * ℓ + 4 * p + 6) := by
    have h1 := len_repeatVec_of_nth_le (v := w) (m := tau X D) (fun i hi => hw i hi)
    have h2 := le_trans h1 (le_trans (repeatVec_mono _ _ _ hl) (repeatVec_le_tau le_rfl ℓ))
    exact le_trans h2 (tau_mono (le_trans le_self_add le_self_add) hE1)
  have hyE : y ≤ tau (X + p + 8) (D + 2 * ℓ + 4 * p + 6) := le_trans hy (tau_mono le_rfl hE2)
  have hpE : p ≤ tau (X + p + 8) (D + 2 * ℓ + 4 * p + 6) :=
    le_trans (le_trans le_add_self le_self_add) (le_tau _ _)
  have h := pair_le_tau (le_trans hwE (tau_mono le_rfl le_self_add))
    (le_trans le_self_add (pair_le_tau hpE hyE))
  refine le_trans h (le_of_lt (tau_strict _ ?_))
  calc D + 2 * ℓ + 4 * p + 6 + 2 + 2 = D + 2 * ℓ + 4 * p + 10 := by ring
    _ < D + 2 * ℓ + 4 * p + 10 + (4 * p + 2) := lt_add_of_pos_right _ (by positivity)
    _ = D + 2 * ℓ + 8 * p + 12 := by ring

theorem stage_lt_bin {X D ℓ p P : V} (h : p + 2 ≤ P) : stage X D ℓ p < stage X D ℓ P := by
  unfold stage
  refine lt_of_le_of_lt (tau_mono (add_le_add (add_le_add le_rfl (le_trans le_self_add h)) le_rfl)
    le_rfl) (tau_strict _ ?_)
  have h8 : 8 * p < 8 * P := by
    have : p < P := lt_of_lt_of_le (lt_add_of_pos_right p (by norm_num)) h
    exact mul_lt_mul_of_pos_left this (by norm_num)
  exact add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt le_rfl h8) le_rfl

theorem stage_lt_all {X D ℓ p P : V} (h : p + 2 ≤ P) : stage X (D + 2) (ℓ + 1) p < stage X D ℓ P := by
  unfold stage
  refine lt_of_le_of_lt (tau_mono (add_le_add (add_le_add le_rfl (le_trans le_self_add h)) le_rfl)
    le_rfl) (tau_strict _ ?_)
  calc D + 2 + 2 * (ℓ + 1) + 8 * p + 12 = D + 2 * ℓ + 8 * (p + 2) := by ring
    _ ≤ D + 2 * ℓ + 8 * P := add_le_add le_rfl (mul_le_mul' le_rfl h)
    _ < D + 2 * ℓ + 8 * P + 12 := lt_add_of_pos_right _ (by norm_num)

instance stage_definable : 𝚺₁-Function₄ (stage : V → V → V → V → V) := by
  unfold stage; definability

/-- The `S`-th stage of the substitution fixpoint. -/
noncomputable def substStage (S : V) : V := substFix.limSeq ![] S

instance substStage_definable : 𝚺₁-Function₁ (substStage : V → V) := by
  have h := (substFix (V := V)).limSeq_definable' 𝚺 (m := 0)
  have e : (fun v : Fin 1 → V => substFix.limSeq (fun i => v i.succ) (v 0)) =
      (fun v => substStage (v 0)) := by
    funext v; unfold substStage; congr 1; funext i; exact i.elim0
  show HierarchySymbol.DefinableFunction 𝚺₁ (fun v : Fin 1 → V => substStage (v 0))
  rw [← e]; exact h

theorem mem_stage_of {x S : V} (hx : x + 1 ≤ S)
    (hΦ : ∀ s, S = s + 1 → (Substs.construction ℒₛₑₜ).Phi ℒₛₑₜ {z | z ∈ substFix.limSeq ![] s} x) :
    x ∈ substStage S := by
  obtain ⟨s, rfl⟩ : ∃ s, S = s + 1 :=
    ⟨S - 1, (tsub_add_cancel_of_le (le_trans le_add_self hx)).symm⟩
  exact substFix.mem_limSeq_succ_iff.mpr ⟨le_of_add_le_add_right hx, hΦ s rfl⟩

theorem mem_of_stage_lt {x S S' s : V} (hx : x ∈ substStage S) (hS : S < S') (hs : S' = s + 1) :
    x ∈ substFix.limSeq ![] s :=
  substFix.limSeq_cumulative (lt_succ_iff_le.mp (hs ▸ hS)) hx

/-- **Substitution triples lie in an explicit stage.** -/
theorem subst_stage : ∀ p : V, IsUFormula ℒₛₑₜ p → ∀ w X D ℓ : V, (∀ j < len w, w.[j] ≤ tau X D) →
    len w ≤ ℓ → ⟪w, p, subst ℒₛₑₜ w p⟫ ∈ substStage (stage X D ℓ p) := by
  refine IsUFormula.ISigma1.pi1_succ_induction (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k R v hR hv w X D ℓ hw hl
    have hP : IsUFormula ℒₛₑₜ (^rel k R v) := by simp [hR, hv]
    refine mem_stage_of (triple_lt_stage hw hl (subst_le _ hP w X D hw)) (fun s _ => ?_)
    exact ⟨w, ^rel k R v, _, rfl, hP, Or.inl ⟨k, R, v, rfl, by rw [substs_rel hR hv]; rfl⟩⟩
  · intro k R v hR hv w X D ℓ hw hl
    have hP : IsUFormula ℒₛₑₜ (^nrel k R v) := by simp [hR, hv]
    refine mem_stage_of (triple_lt_stage hw hl (subst_le _ hP w X D hw)) (fun s _ => ?_)
    exact ⟨w, ^nrel k R v, _, rfl, hP, Or.inr (Or.inl ⟨k, R, v, rfl, by rw [substs_nrel hR hv]; rfl⟩)⟩
  · intro w X D ℓ hw hl
    have hP : IsUFormula ℒₛₑₜ (^⊤ : V) := by simp
    refine mem_stage_of (triple_lt_stage hw hl (subst_le _ hP w X D hw)) (fun s _ => ?_)
    exact ⟨w, ^⊤, _, rfl, hP, Or.inr (Or.inr (Or.inl ⟨rfl, by rw [substs_verum]; rfl⟩))⟩
  · intro w X D ℓ hw hl
    have hP : IsUFormula ℒₛₑₜ (^⊥ : V) := by simp
    refine mem_stage_of (triple_lt_stage hw hl (subst_le _ hP w X D hw)) (fun s _ => ?_)
    exact ⟨w, ^⊥, _, rfl, hP, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by rw [substs_falsum]; rfl⟩)))⟩
  · intro p q hp hq ihp ihq w X D ℓ hw hl
    have hP : IsUFormula ℒₛₑₜ (p ^⋏ q) := by simp [hp, hq]
    refine mem_stage_of (triple_lt_stage hw hl (subst_le _ hP w X D hw)) (fun s hs => ?_)
    refine ⟨w, p ^⋏ q, _, rfl, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, _, _, ?_, ?_, rfl, by rw [substs_and hp hq]; rfl⟩))))⟩
    · exact mem_of_stage_lt (ihp w X D ℓ hw hl) (stage_lt_bin (add_two_le_and_left p q)) hs
    · exact mem_of_stage_lt (ihq w X D ℓ hw hl) (stage_lt_bin (add_two_le_and_right p q)) hs
  · intro p q hp hq ihp ihq w X D ℓ hw hl
    have hP : IsUFormula ℒₛₑₜ (p ^⋎ q) := by simp [hp, hq]
    refine mem_stage_of (triple_lt_stage hw hl (subst_le _ hP w X D hw)) (fun s hs => ?_)
    refine ⟨w, p ^⋎ q, _, rfl, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, _, _, ?_, ?_, rfl, by rw [substs_or hp hq]; rfl⟩)))))⟩
    · exact mem_of_stage_lt (ihp w X D ℓ hw hl) (stage_lt_bin (add_two_le_or_left p q)) hs
    · exact mem_of_stage_lt (ihq w X D ℓ hw hl) (stage_lt_bin (add_two_le_or_right p q)) hs
  · intro p hp ihp w X D ℓ hw hl
    have hP : IsUFormula ℒₛₑₜ (^∀ p) := by simp [hp]
    refine mem_stage_of (triple_lt_stage hw hl (subst_le _ hP w X D hw)) (fun s hs => ?_)
    refine ⟨w, ^∀ p, _, rfl, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, _, ?_, rfl, by rw [substs_all hp]; rfl⟩))))))⟩
    exact mem_of_stage_lt (ihp (qVec ℒₛₑₜ w) X (D + 2) (ℓ + 1) (fun j _ => qVec_entries hw j)
      (le_trans (len_qVec_le_len w) (add_le_add hl le_rfl))) (stage_lt_all (add_two_le_all p)) hs
  · intro p hp ihp w X D ℓ hw hl
    have hP : IsUFormula ℒₛₑₜ (^∃ p) := by simp [hp]
    refine mem_stage_of (triple_lt_stage hw hl (subst_le _ hP w X D hw)) (fun s hs => ?_)
    refine ⟨w, ^∃ p, _, rfl, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨p, _, ?_, rfl, by rw [substs_ex hp]; rfl⟩)))))))⟩
    exact mem_of_stage_lt (ihp (qVec ℒₛₑₜ w) X (D + 2) (ℓ + 1) (fun j _ => qVec_entries hw j)
      (le_trans (len_qVec_le_len w) (add_le_add hl le_rfl))) (stage_lt_all (add_two_le_exs p)) hs

/-- **Every substitution-fixpoint element lies in a stage bounded by a
function of the element.** -/
theorem subst_fixpoint_stage {x s : V} (hx : x ∈ substFix.limSeq ![] s) :
    x ∈ substStage (tau (x + x + 8) (10 * x + 12)) := by
  have hfix : substFix.Fixpoint ![] x := ⟨s, hx⟩
  obtain ⟨w, p, y, rfl, hp, -⟩ := substFix.case.mp hfix
  have hy : subst ℒₛₑₜ w p = y := (Substs.construction ℒₛₑₜ).result_eq_of_graph hfix
  subst hy
  have h := subst_stage p hp w w 0 w (fun j _ => le_trans (nth_le w j) (le_tau w 0)) (len_le w)
  refine substFix.limSeq_cumulative ?_ h
  have hw : w ≤ ⟪w, p, subst ℒₛₑₜ w p⟫ := le_pair_left _ _
  have hp' : p ≤ ⟪w, p, subst ℒₛₑₜ w p⟫ := le_trans (le_pair_left p _) (le_pair_right w _)
  unfold stage
  refine tau_mono (add_le_add (add_le_add hw hp') le_rfl) ?_
  calc 0 + 2 * w + 8 * p + 12 ≤ 2 * ⟪w, p, subst ℒₛₑₜ w p⟫ + 8 * ⟪w, p, subst ℒₛₑₜ w p⟫ + 12 := by
        rw [zero_add]; exact add_le_add (add_le_add (mul_le_mul' le_rfl hw) (mul_le_mul' le_rfl hp')) le_rfl
    _ = 10 * ⟪w, p, subst ℒₛₑₜ w p⟫ + 12 := by ring

/-! ### `free`, `substs1` and `setShift` -/

/-- The shared relation-argument bound, for either relation tag. -/
private theorem shifted_rel_bound {k R v w X D P t : V}
    (hv : IsUTermVec ℒₛₑₜ k v) (hw : ∀ j < len w, w.[j] ≤ tau X D)
    (hkP : k ≤ P) (hRP : R ≤ P) (hvP : v ≤ P) (ht : t ≤ 1) :
    ⟪t, k, R, termSubstVec ℒₛₑₜ k w (termShiftVec ℒₛₑₜ k v)⟫ + 1 ≤
      tau (X + ((P + 2) * (P + 2) + 1) + 8) (D + 4 * P + 6) := by
  have hF : ∀ i < k, (termShiftVec ℒₛₑₜ k v).[i] ≤ (P + 2) * (P + 2) + 1 := fun i hi => by
    rw [nth_termShiftVec hv hi]
    exact le_trans (termShift_le _) (sq2_mono (le_trans (nth_le v i) hvP))
  have hm : tau X D + ((P + 2) * (P + 2) + 1) ≤
      tau (X + ((P + 2) * (P + 2) + 1) + 8) (D + 2 * P) :=
    le_trans (tau_add_le X D _) (tau_mono le_self_add le_self_add)
  have hv' : termSubstVec ℒₛₑₜ k w (termShiftVec ℒₛₑₜ k v) ≤
      tau (X + ((P + 2) * (P + 2) + 1) + 8) (D + 2 * P + 2 * k) :=
    le_trans (termSubstVec_le_entries2 hw hv.termShiftVec hF)
      (le_trans (repeatVec_mono_left hm k) (repeatVec_le_tau le_rfl k))
  have hY {c : V} (h : c ≤ P) : c ≤ tau (X + ((P + 2) * (P + 2) + 1) + 8) (D + 2 * P + 2 * k) :=
    le_tau_of _ c _ (le_trans (le_trans (le_trans h (le_sq2 P)) le_add_self) le_self_add)
  have ht' : t ≤ tau (X + ((P + 2) * (P + 2) + 1) + 8) (D + 2 * P + 2 * k) :=
    le_trans ht (by simpa using (le_tau_of' 1 hv'))
  have h := code4_le_tau ht' (hY hkP) (hY hRP) hv'
  exact le_trans h (tau_mono le_rfl (sdepth_leaf hkP D))

/-- **Substitution after shift**, bounded through the unshifted formula. -/
theorem subst_shift_le : ∀ p : V, IsUFormula ℒₛₑₜ p → ∀ w X D : V, (∀ j < len w, w.[j] ≤ tau X D) →
    subst ℒₛₑₜ w (shift ℒₛₑₜ p) ≤ tau (X + ((p + 2) * (p + 2) + 1) + 8) (D + 4 * p + 6) := by
  refine IsUFormula.ISigma1.pi1_succ_induction (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k R v hR hv w X D hw
    rw [shift_rel hR hv, substs_rel hR hv.termShiftVec]
    have h := shifted_rel_bound (t := 0) hv hw (arity_lt_rel k R v).le
      (r_lt_rel k R v).le (v_lt_rel k R v).le (by norm_num)
    simpa [qqRel] using h
  · intro k R v hR hv w X D hw
    rw [shift_nrel hR hv, substs_nrel hR hv.termShiftVec]
    have h := shifted_rel_bound (t := 1) hv hw (arity_lt_nrel k R v).le
      (r_lt_nrel k R v).le (v_lt_nrel k R v).le (by norm_num)
    simpa [qqNRel] using h
  · intro w X D hw
    rw [shift_verum, substs_verum]
    exact le_trans (le_trans (le_trans (le_sq2 _) le_add_self) le_self_add) (le_tau _ _)
  · intro w X D hw
    rw [shift_falsum, substs_falsum]
    exact le_trans (le_trans (le_trans (le_sq2 _) le_add_self) le_self_add) (le_tau _ _)
  · intro p q hp hq ihp ihq w X D hw
    rw [shift_and hp hq, substs_and hp.shift hq.shift]
    set P := p ^⋏ q
    have hp2 := add_two_le_and_left p q; have hq2 := add_two_le_and_right p q
    have hnp : subst ℒₛₑₜ w (shift ℒₛₑₜ p) ≤ tau (X + ((P + 2) * (P + 2) + 1) + 8) (D + 4 * P + 2) :=
      le_trans (ihp w X D hw) (tau_mono (add_le_add (add_le_add le_rfl
        (sq2_mono (le_trans le_self_add hp2))) le_rfl) (sdepth_bin hp2 D))
    have hnq : subst ℒₛₑₜ w (shift ℒₛₑₜ q) ≤ tau (X + ((P + 2) * (P + 2) + 1) + 8) (D + 4 * P + 2) :=
      le_trans (ihq w X D hw) (tau_mono (add_le_add (add_le_add le_rfl
        (sq2_mono (le_trans le_self_add hq2))) le_rfl) (sdepth_bin hq2 D))
    have h := code3_le_tau (le_tau_of' 4 hnp) hnp hnq
    exact le_trans (by simpa [qqAnd] using h) (tau_mono le_rfl (le_of_eq (by ring)))
  · intro p q hp hq ihp ihq w X D hw
    rw [shift_or hp hq, substs_or hp.shift hq.shift]
    set P := p ^⋎ q
    have hp2 := add_two_le_or_left p q; have hq2 := add_two_le_or_right p q
    have hnp : subst ℒₛₑₜ w (shift ℒₛₑₜ p) ≤ tau (X + ((P + 2) * (P + 2) + 1) + 8) (D + 4 * P + 2) :=
      le_trans (ihp w X D hw) (tau_mono (add_le_add (add_le_add le_rfl
        (sq2_mono (le_trans le_self_add hp2))) le_rfl) (sdepth_bin hp2 D))
    have hnq : subst ℒₛₑₜ w (shift ℒₛₑₜ q) ≤ tau (X + ((P + 2) * (P + 2) + 1) + 8) (D + 4 * P + 2) :=
      le_trans (ihq w X D hw) (tau_mono (add_le_add (add_le_add le_rfl
        (sq2_mono (le_trans le_self_add hq2))) le_rfl) (sdepth_bin hq2 D))
    have h := code3_le_tau (le_tau_of' 5 hnp) hnp hnq
    exact le_trans (by simpa [qqOr] using h) (tau_mono le_rfl (le_of_eq (by ring)))
  · intro p hp ihp w X D hw
    rw [shift_all hp, substs_all hp.shift]
    set P := ^∀ p
    have hp2 := add_two_le_all p
    have hnp : subst ℒₛₑₜ (qVec ℒₛₑₜ w) (shift ℒₛₑₜ p) ≤
        tau (X + ((P + 2) * (P + 2) + 1) + 8) (D + 4 * P + 4) :=
      le_trans (ihp (qVec ℒₛₑₜ w) X (D + 2) (fun j _ => qVec_entries hw j))
        (tau_mono (add_le_add (add_le_add le_rfl
          (sq2_mono (le_trans le_self_add hp2))) le_rfl) (sdepth_all hp2 D))
    have h := code2_le_tau (le_tau_of' 6 hnp) hnp
    exact le_trans (by simpa [qqAll] using h) (tau_mono le_rfl (le_of_eq (by ring)))
  · intro p hp ihp w X D hw
    rw [shift_exs hp, substs_ex hp.shift]
    set P := ^∃ p
    have hp2 := add_two_le_exs p
    have hnp : subst ℒₛₑₜ (qVec ℒₛₑₜ w) (shift ℒₛₑₜ p) ≤
        tau (X + ((P + 2) * (P + 2) + 1) + 8) (D + 4 * P + 4) :=
      le_trans (ihp (qVec ℒₛₑₜ w) X (D + 2) (fun j _ => qVec_entries hw j))
        (tau_mono (add_le_add (add_le_add le_rfl
          (sq2_mono (le_trans le_self_add hp2))) le_rfl) (sdepth_all hp2 D))
    have h := code2_le_tau (le_tau_of' 7 hnp) hnp
    exact le_trans (by simpa [qqExs] using h) (tau_mono le_rfl (le_of_eq (by ring)))

theorem singleton_entries {t E : V} (ht : t ≤ E) : ∀ j < len (?[t] : V), (?[t] : V).[j] ≤ E := by
  intro j _
  rcases zero_or_succ j with rfl | ⟨i, rfl⟩
  · simpa using ht
  · simp

/-- **`free` is doubly exponentially bounded.** -/
theorem free_le (p : V) : free ℒₛₑₜ p ≤ tau (0 + ((p + 2) * (p + 2) + 1) + 8) (0 + 4 * p + 6) := by
  unfold free substs1
  by_cases hp : IsUFormula ℒₛₑₜ p
  · refine subst_shift_le p hp _ 0 0 (singleton_entries ?_)
    exact le_trans (by simp [qqFvar, pair]; norm_num) (four_le_tau 0 0)
  · rw [shift_not_uformula hp, substs_not_uformula (by simp)]; simp

/-- **`substs1` is doubly exponentially bounded.** -/
theorem substs1_le (t p : V) : substs1 ℒₛₑₜ t p ≤ tau (t + p + 8) (0 + 4 * p + 6) := by
  unfold substs1
  by_cases hp : IsUFormula ℒₛₑₜ p
  · exact subst_le p hp _ t 0 (singleton_entries (le_tau t 0))
  · rw [substs_not_uformula hp]; simp

theorem exp_six : Exp.exp (6 : V) = 2 * 2 * (2 * 2) * (2 * 2) := by
  rw [show (6 : V) = 2 + 2 + 2 by norm_num, exp_add, exp_add, exp_two_eq]

/-- **`setShift` is doubly exponentially bounded**: the members of `s` are
logarithmically small, `2^x ≤ s`. -/
theorem setShift_le (s : V) :
    setShift ℒₛₑₜ s ≤ Exp.exp (Exp.exp (((s + 2) * (s + 2) + 1 + 8 + 4) * (s * s * 64) + 1)) := by
  set K := ((s + 2) * (s + 2) + 1 + 8 + 4) * (s * s * 64)
  have hel : ∀ y ∈ setShift ℒₛₑₜ s, y < Exp.exp K + 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_setShift_iff.mp hy
    refine lt_succ_iff_le.mpr ?_
    by_cases hxf : IsUFormula ℒₛₑₜ x
    · refine le_trans (shift_le x hxf) (exp_monotone_le.mpr ?_)
      have hxs : x ≤ s := le_of_lt (lt_of_mem hx)
      have hex : Exp.exp x ≤ s := exp_le_of_mem hx
      have h1 : (x + 2) * (x + 2) + 1 + 8 + 4 ≤ (s + 2) * (s + 2) + 1 + 8 + 4 :=
        add_le_add (add_le_add (sq2_mono hxs) le_rfl) le_rfl
      have h2 : Exp.exp (2 * x + 6) ≤ s * s * 64 := by
        rw [show 2 * x + 6 = x + x + 6 by ring, exp_add, exp_add, exp_six]
        have : (2 : V) * 2 * (2 * 2) * (2 * 2) = 64 := by norm_num
        rw [this]; exact mul_le_mul' (mul_le_mul' hex hex) le_rfl
      exact mul_le_mul' h1 h2
    · rw [shift_not_uformula hxf]; simp
  have h := lt_exp_iff.mpr hel
  refine le_trans (le_of_lt h) (exp_monotone_le.mpr ?_)
  have h1 : (1 : V) ≤ Exp.exp K := pos_iff_one_le.mp (exp_pos K)
  calc Exp.exp K + 1 ≤ Exp.exp K + Exp.exp K := add_le_add le_rfl h1
    _ = Exp.exp (K + 1) := by rw [exp_succ]; ring

end DiophantineConsistency.PRAWitnessCodeGrowth
