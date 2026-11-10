import DiophantineConsistency.Nine121.Kron4
import Mathlib.Tactic.FinCases

/-! # Positivity by a dominating top group

A four-variable polynomial is written as `a^{e₀} z^{e₃} P + rest`, where `P` collects the terms of
top degree in `a` and `z` (a polynomial in `c, i` only, but `P` is just a value here) and `rest` is
a term tree. `pos_split`: if

* every monomial of `rest` divides `top = a^{e₀} c^{e₁} i^{e₂} z^{e₃}` and every negative
  coefficient of `rest` sits at `a`-degree `< e₀` or `z`-degree `< e₃` (`restOk`),
* `κ c^{e₁} i^{e₂} ≤ P` for a natural `κ`, and
* `κ M + ν > 0`, with `ν` the sum of the negative coefficients of `rest`,

then the polynomial is positive whenever `a, z ≥ M` and `a, c, i, z ≥ 1`, in every ordered
commutative ring. (Each negative term `c·m` of `rest` has `M·m ≤ top`, because one of the two
exponents is below the top.)

The lower bound `κ c^{e₁} i^{e₂} ≤ P` is supplied by an identity `P − κ c^{e₁} i^{e₂} = Q` where
`Q` is an integer expression built from nonnegative literals and the shifted variables
`x − 1` by sums and products (`NN`); `NN_nonneg` shows `Q ≥ 0` when all variables are `≥ 1`.
Both checks are Boolean, for `decide +kernel`. -/
set_option autoImplicit false
noncomputable section
namespace Nine121.TopDom
open SP4 Kron

/-! ## The dominated rest -/

/-- A term of the rest divides `top`; a negative coefficient needs `a`- or `z`-degree below top. -/
def restOk (top : Mon) (t : Mon × ℤ) : Bool :=
  t.1.le top && (isNonneg t.2 || Nat.blt t.1.e0 top.e0 || Nat.blt t.1.e3 top.e3)

/-- The negative part of a coefficient. -/
def negPart (k : ℤ) : ℤ := bif isNonneg k then 0 else k

/-- The sum of the negative coefficients of a term tree. -/
def negAll (t : TT) : ℤ :=
  TT.rec (motive := fun _ => ℤ) (fun _ k => negPart k) (fun _ _ x y => x + y) t

def negL : List (Mon × ℤ) → ℤ
  | [] => 0
  | t :: p => negPart t.2 + negL p

theorem negL_append (l1 l2 : List (Mon × ℤ)) : negL (l1 ++ l2) = negL l1 + negL l2 := by
  induction l1 with
  | nil => simp [negL]
  | cons t l ih => simp only [List.cons_append, negL, ih]; ring

theorem negAll_eq (t : TT) : negAll t = negL t.toList := by
  induction t with
  | leaf m k => simp [negAll, TT.toList, negL]
  | node l r hl hr =>
    show negAll l + negAll r = _
    rw [TT.toList_node, negL_append, hl, hr]

theorem all_eq (f : Mon × ℤ → Bool) (t : TT) : t.all f = t.toList.all f := by
  induction t with
  | leaf m k => simp [TT.all, TT.toList]
  | node l r hl hr =>
    show (l.all f && r.all f) = _
    rw [TT.toList_node, List.all_append, hl, hr]

theorem negPart_le_zero (k : ℤ) : negPart k ≤ 0 := by
  unfold negPart
  cases h : isNonneg k
  · have := neg_of_not_isNonneg h; simp only [cond_false]; omega
  · simp only [cond_true]; omega

section Order
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Lowering one exponent of `top` by one and multiplying by `M` stays below `top`. -/
theorem M_evM_le {a c i z : R} (M : R) (hM0 : 0 ≤ M) (haM : M ≤ a) (hzM : M ≤ z)
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hi : 1 ≤ i) (hz : 1 ≤ z) (top m : Mon) (hle : m.le top = true)
    (hlow : m.e0 < top.e0 ∨ m.e3 < top.e3) :
    M * evM a c i z m ≤ evM a c i z top := by
  obtain ⟨l0, l1, l2, l3⟩ := Mon.le_spec hle
  rcases hlow with h0 | h3
  · have hm : evM a c i z m ≤ evM a c i z ⟨top.e0 - 1, top.e1, top.e2, top.e3⟩ :=
      evM_le ha hc hi hz (by simp only; omega) l1 l2 l3
    have e : evM a c i z top = a * evM a c i z ⟨top.e0 - 1, top.e1, top.e2, top.e3⟩ := by
      simp only [evM]
      rw [show top.e0 = (top.e0 - 1) + 1 from (Nat.sub_add_cancel (by omega)).symm, pow_succ]
      simp only [Nat.add_sub_cancel]
      ring
    have hQ0 : 0 ≤ evM a c i z ⟨top.e0 - 1, top.e1, top.e2, top.e3⟩ :=
      evM_nonneg (by linarith) (by linarith) (by linarith) (by linarith) _
    rw [e]
    calc M * evM a c i z m ≤ M * evM a c i z ⟨top.e0 - 1, top.e1, top.e2, top.e3⟩ :=
          mul_le_mul_of_nonneg_left hm hM0
      _ ≤ a * evM a c i z ⟨top.e0 - 1, top.e1, top.e2, top.e3⟩ := mul_le_mul_of_nonneg_right haM hQ0
  · have hm : evM a c i z m ≤ evM a c i z ⟨top.e0, top.e1, top.e2, top.e3 - 1⟩ :=
      evM_le ha hc hi hz l0 l1 l2 (by simp only; omega)
    have e : evM a c i z top = z * evM a c i z ⟨top.e0, top.e1, top.e2, top.e3 - 1⟩ := by
      simp only [evM]
      rw [show top.e3 = (top.e3 - 1) + 1 from (Nat.sub_add_cancel (by omega)).symm, pow_succ]
      simp only [Nat.add_sub_cancel]
      ring
    have hQ0 : 0 ≤ evM a c i z ⟨top.e0, top.e1, top.e2, top.e3 - 1⟩ :=
      evM_nonneg (by linarith) (by linarith) (by linarith) (by linarith) _
    rw [e]
    calc M * evM a c i z m ≤ M * evM a c i z ⟨top.e0, top.e1, top.e2, top.e3 - 1⟩ :=
          mul_le_mul_of_nonneg_left hm hM0
      _ ≤ z * evM a c i z ⟨top.e0, top.e1, top.e2, top.e3 - 1⟩ := mul_le_mul_of_nonneg_right hzM hQ0

/-- The rest is at least `ν·top / M`. -/
theorem rest_ge {a c i z : R} (M : R) (hM0 : 0 ≤ M) (haM : M ≤ a) (hzM : M ≤ z)
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hi : 1 ≤ i) (hz : 1 ≤ z) (top : Mon) :
    ∀ p : List (Mon × ℤ), p.all (restOk top) = true →
      (negL p : R) * evM a c i z top ≤ M * evL a c i z p
  | [], _ => by simp [negL, evL]
  | t :: p, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := rest_ge M hM0 haM hzM ha hc hi hz top p h.2
    have hd := h.1
    simp only [restOk, Bool.and_eq_true, Bool.or_eq_true] at hd
    obtain ⟨hle, hcase⟩ := hd
    have hT0 : 0 ≤ evM a c i z top := evM_nonneg (by linarith) (by linarith) (by linarith) (by linarith) _
    have hm0 : 0 ≤ evM a c i z t.1 := evM_nonneg (by linarith) (by linarith) (by linarith) (by linarith) _
    have key : ((negPart t.2 : ℤ) : R) * evM a c i z top ≤ M * ((t.2 : R) * evM a c i z t.1) := by
      unfold negPart
      cases h2 : isNonneg t.2
      · have hneg := neg_of_not_isNonneg h2
        have hlow : t.1.e0 < top.e0 ∨ t.1.e3 < top.e3 := by
          rcases hcase with (h | h) | h
          · rw [h2] at h; exact absurd h (by simp)
          · left; exact Nat.blt_eq.mp h
          · right; exact Nat.blt_eq.mp h
        have hb := M_evM_le M hM0 haM hzM ha hc hi hz top t.1 hle hlow
        have hn : (t.2 : R) < 0 := by exact_mod_cast hneg
        simp only [cond_false]
        nlinarith
      · have hn : (0 : R) ≤ t.2 := by exact_mod_cast nonneg_of_isNonneg h2
        simp only [cond_true, Int.cast_zero, zero_mul]
        exact mul_nonneg hM0 (mul_nonneg hn hm0)
    simp only [negL, evL, Int.cast_add]
    linarith

/-- **Positivity by the dominating top group.** -/
theorem pos_split (top : Mon) (M κ : ℕ) (rest : TT) (hrest : rest.all (restOk top) = true)
    (hpos : 0 < (κ : ℤ) * M + negAll rest) {a c i z P : R} (haM : (M : R) ≤ a) (hzM : (M : R) ≤ z)
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hi : 1 ≤ i) (hz : 1 ≤ z)
    (hP : (κ : R) * (c ^ top.e1 * i ^ top.e2) ≤ P) :
    0 < a ^ top.e0 * z ^ top.e3 * P + evL a c i z rest.toList := by
  rw [all_eq] at hrest
  rw [negAll_eq] at hpos
  have hM0 : (0 : R) ≤ M := Nat.cast_nonneg M
  have hr := rest_ge (M : R) hM0 haM hzM ha hc hi hz top rest.toList hrest
  have hE1 : 1 ≤ evM a c i z top := by
    have := evM_le ha hc hi hz (m := ⟨0, 0, 0, 0⟩) (n := top)
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    simpa [evM] using this
  have hE : evM a c i z top = (a ^ top.e0 * z ^ top.e3) * (c ^ top.e1 * i ^ top.e2) := by
    simp only [evM]; ring
  have haz0 : 0 ≤ a ^ top.e0 * z ^ top.e3 :=
    mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
  have h1 : (κ : R) * evM a c i z top ≤ a ^ top.e0 * z ^ top.e3 * P := by
    rw [hE]
    have := mul_le_mul_of_nonneg_left hP haz0
    linarith [show (κ : R) * ((a ^ top.e0 * z ^ top.e3) * (c ^ top.e1 * i ^ top.e2)) =
      a ^ top.e0 * z ^ top.e3 * ((κ : R) * (c ^ top.e1 * i ^ top.e2)) by ring]
  have hν : negL rest.toList ≤ 0 := by
    have : ∀ p : List (Mon × ℤ), negL p ≤ 0 := by
      intro p
      induction p with
      | nil => simp [negL]
      | cons t p ih => simp only [negL]; linarith [negPart_le_zero t.2]
    exact this _
  have hM1 : (1 : ℤ) ≤ M := by
    by_contra hn
    have : (M : ℤ) = 0 := by omega
    rw [this, mul_zero, zero_add] at hpos
    omega
  have hM1R : (1 : R) ≤ M := by exact_mod_cast hM1
  have hsum : (1 : R) ≤ (κ : R) * M + negL rest.toList := by
    have : (1 : ℤ) ≤ (κ : ℤ) * M + negL rest.toList := hpos
    exact_mod_cast this
  -- `M·X ≥ (κM + ν)·top ≥ top ≥ 1`
  have hX : (1 : R) ≤ (M : R) * (a ^ top.e0 * z ^ top.e3 * P + evL a c i z rest.toList) := by
    have h2 : (M : R) * ((κ : R) * evM a c i z top) ≤ (M : R) * (a ^ top.e0 * z ^ top.e3 * P) :=
      mul_le_mul_of_nonneg_left h1 hM0
    have h3 : evM a c i z top ≤ ((κ : R) * M + negL rest.toList) * evM a c i z top :=
      le_mul_of_one_le_left (by linarith) hsum
    nlinarith
  by_contra hn
  have hn' : a ^ top.e0 * z ^ top.e3 * P + evL a c i z rest.toList ≤ 0 := not_lt.mp hn
  have : (M : R) * (a ^ top.e0 * z ^ top.e3 * P + evL a c i z rest.toList) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hM0 hn'
  linarith

end Order

/-! ## Nonnegative expressions in the shifted variables -/

/-- `x = pw k 1`, `y = lit 1`: the shifted variable `xₖ − 1`. -/
def shiftOk : ZE → ZE → Bool
  | .pw _ n, .lit m => Nat.beq n 1 && decide (m = 1)
  | _, _ => false

/-- Sums and products of nonnegative literals and shifted variables. -/
def NN : ZE → Bool
  | .lit n => isNonneg n
  | .add x y => NN x && NN y
  | .mul x y => NN x && NN y
  | .sub x y => shiftOk x y
  | _ => false

theorem shiftOk_spec {x y : ZE} (h : shiftOk x y = true) : ∃ k, x = .pw k 1 ∧ y = .lit 1 := by
  cases x <;> cases y <;> simp [shiftOk] at h
  rename_i k n m
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨k, rfl, rfl⟩

theorem NN_nonneg {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a c i z : R}
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hi : 1 ≤ i) (hz : 1 ≤ z) :
    ∀ e : ZE, NN e = true → 0 ≤ e.eval a c i z := by
  intro e
  induction e with
  | pw k n => intro h; simp [NN] at h
  | lit n =>
    intro h
    simp only [NN] at h
    rw [zeval_lit]
    exact_mod_cast nonneg_of_isNonneg h
  | add x y hx hy =>
    intro h
    simp only [NN, Bool.and_eq_true] at h
    rw [zeval_add]; exact add_nonneg (hx h.1) (hy h.2)
  | sub x y _ _ =>
    intro h
    simp only [NN] at h
    obtain ⟨k, rfl, rfl⟩ := shiftOk_spec h
    rw [zeval_sub, zeval_pw, zeval_lit, pow_one, Int.cast_one, sub_nonneg]
    fin_cases k <;> simp [sel] <;> assumption
  | mul x y hx hy =>
    intro h
    simp only [NN, Bool.and_eq_true] at h
    rw [zeval_mul]; exact mul_nonneg (hx h.1) (hy h.2)
  | terms t => intro h; simp [NN] at h

end Nine121.TopDom
