theorem castLE_refl (h : n ≤ n) (i : Fin n) : i.castLE h = i := rfl

@[simp, grind =]
theorem castSucc_castLE (h : n ≤ m) (i : Fin n) :
    (i.castLE h).castSucc = i.castLE (by omega) := rfl

@[simp, grind =]
theorem castSucc_natAdd (n : Nat) (i : Fin k) :
    (i.natAdd n).castSucc = (i.castSucc).natAdd n := rfl

/-! ### pred -/

@[simp] theorem val_pred (j : Fin (n + 1)) (h : j ≠ 0) : (j.pred h : Nat) = j - 1 := rfl

grind_pattern val_pred => j.pred h

@[deprecated val_pred (since := "2025-11-21")]
theorem coe_pred (j : Fin (n + 1)) (h : j ≠ 0) : (j.pred h : Nat) = j - 1 := rfl

@[simp] theorem succ_pred : ∀ (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ = i
  | ⟨0, _⟩, hi => by simp only [mk_zero, ne_eq, not_true] at hi
  | ⟨_ + 1, _⟩, _ => rfl

@[simp]
theorem pred_succ (i : Fin n) {h : i.succ ≠ 0} : i.succ.pred h = i := by
  cases i
  rfl

theorem pred_eq_iff_eq_succ {n : Nat} {i : Fin (n + 1)} (hi : i ≠ 0) {j : Fin n} :
    i.pred hi = j ↔ i = j.succ :=
  ⟨fun h => by simp only [← h, Fin.succ_pred], fun h => by simp only [h, Fin.pred_succ]⟩

theorem pred_mk_succ (i : Nat) (h : i < n + 1) :
    Fin.pred ⟨i + 1, Nat.add_lt_add_right h 1⟩ (ne_of_val_ne (Nat.ne_of_gt (mk_succ_pos i h))) =
      ⟨i, h⟩ := by
  simp only [Fin.ext_iff, val_pred, Nat.add_sub_cancel]

@[simp] theorem pred_mk_succ' (i : Nat) (h₁ : i + 1 < n + 1 + 1) (h₂) :
    Fin.pred ⟨i + 1, h₁⟩ h₂ = ⟨i, Nat.lt_of_succ_lt_succ h₁⟩ := pred_mk_succ i _

-- This is not a simp theorem by default, because `pred_mk_succ` is nicer when it applies.
theorem pred_mk {n : Nat} (i : Nat) (h : i < n + 1) (w) : Fin.pred ⟨i, h⟩ w =
    ⟨i - 1, Nat.sub_lt_right_of_lt_add (Nat.pos_iff_ne_zero.2 (Fin.val_ne_of_ne w)) h⟩ :=
  rfl

@[simp] theorem pred_le_pred_iff {n : Nat} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
    a.pred ha ≤ b.pred hb ↔ a ≤ b := by rw [← succ_le_succ_iff, succ_pred, succ_pred]

@[simp] theorem pred_lt_pred_iff {n : Nat} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
    a.pred ha < b.pred hb ↔ a < b := by rw [← succ_lt_succ_iff, succ_pred, succ_pred]

@[simp] theorem pred_inj :
    ∀ {a b : Fin (n + 1)} {ha : a ≠ 0} {hb : b ≠ 0}, a.pred ha = b.pred hb ↔ a = b
  | ⟨0, _⟩, _, ha, _ => by simp only [mk_zero, ne_eq, not_true] at ha
