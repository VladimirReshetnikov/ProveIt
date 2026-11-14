import ConPACommandFrame

/-!
# Gadget words

The command words of `pa194-diagonal-selector/PA194Words.lean` and
`pa194-derivation-compiler`, executed inside a model of `𝗜𝚺₁`: an AX followed by SHIFTs slides
a window over the ten pushed entries (`ax_shifts`), POP removes one stack entry and keeps the
top, PUSH saves the top, DISCARD clears it.

A word is built from the empty word `0` by `snoc`; `shifts k W` appends `k` SHIFTs.
-/
set_option autoImplicit false
noncomputable section
namespace ConPA.Words
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor (cantor first second triangle)

section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (S : Sem V)

/-! ## Arithmetic facts -/

lemma add_ne_one {a b : V} (ha : a ≠ 1) (hb : b ≠ 1) : a + b ≠ 1 := by
  intro h
  have hle : a ≤ 1 := by
    rw [← h]
    exact le_add_of_nonneg_right (by simp)
  rcases le_one_iff_eq_zero_or_one.mp hle with (rfl | rfl)
  · exact hb (by simpa using h)
  · exact ha rfl

lemma two_le_add (x t : V) : (2 : V) ≤ 4 * x + 2 + t :=
  le_trans (le_add_of_nonneg_left (by simp)) (le_add_of_nonneg_right (by simp))

lemma allV_add_ne_one (x t : V) : 4 * x + 2 + t ≠ 1 := by
  intro h
  have h2 := two_le_add x t
  rw [h] at h2
  exact absurd h2 (not_le.mpr one_lt_two)

lemma allV_ne_one (x : V) : 4 * x + 2 ≠ 1 := by
  simpa using allV_add_ne_one x 0

lemma allV_ne_zero (x : V) : 4 * x + 2 ≠ 0 := by
  intro h
  have h2 := two_le_add x 0
  rw [add_zero, h] at h2
  exact absurd h2 (not_le.mpr zero_lt_two)

lemma four_mul_ne (x y : V) : 4 * x ≠ 4 * y + 2 := by
  intro h
  rcases le_or_gt x y with hxy | hxy
  · have h1 : 4 * x ≤ 4 * y := mul_le_mul_of_nonneg_left hxy (by simp)
    have h2 : 4 * y < 4 * y + 2 := lt_add_of_pos_right _ zero_lt_two
    exact absurd h (ne_of_lt (lt_of_le_of_lt h1 h2))
  · have h1 : y + 1 ≤ x := lt_iff_succ_le.mp hxy
    have h2 : 4 * (y + 1) ≤ 4 * x := mul_le_mul_of_nonneg_left h1 (by simp)
    have h3 : 4 * y + 2 < 4 * (y + 1) := by
      have h24 : (2 : V) < 4 := by norm_num
      rw [mul_add, mul_one]
      exact add_lt_add_right h24 (4 * y)
    exact absurd h.symm (ne_of_lt (lt_of_lt_of_le h3 h2))

lemma cantor_ne_zero_right {a b : V} (hb : b ≠ 0) : cantor a b ≠ 0 := by
  intro h
  have hle := (SetTheory.BusyBeaver.ZFC.ArithmeticCantor.components_le a b).2
  rw [h] at hle
  exact hb (nonpos_iff_eq_zero.mp hle)

lemma cantor_ne_zero_left {a b : V} (ha : a ≠ 0) : cantor a b ≠ 0 := by
  intro h
  have hle := (SetTheory.BusyBeaver.ZFC.ArithmeticCantor.components_le a b).1
  rw [h] at hle
  exact ha (nonpos_iff_eq_zero.mp hle)

lemma four_mul_ne_zero {c : V} (hc : c ≠ 0) : 4 * c ≠ 0 :=
  ne_of_gt (mul_pos (by norm_num) (pos_iff_ne_zero.mpr hc))

/-! ## Commands and words -/

def SH : V := ⟪0, 0, 0⟫
def MP (y : V) : V := ⟪1, y, 0⟫
def AX (A y x : V) : V := ⟪A + 1 + 1, y, x⟫

/-- The word `W` followed by the command `c`. -/
def snoc (W c : V) : V := c ∷ W

@[simp] lemma texec_snoc (W c τ : V) : texec S (snoc W c) τ = tstep S c (texec S W τ) := by
  simp [snoc]

/-- `W` followed by `k` SHIFTs. -/
def shifts : ℕ → V → V
  | 0, W => W
  | k + 1, W => shifts k (snoc W SH)

lemma tstep_SH (a b c w d δ : V) (hh : a + b ≠ 1) :
    tstep S SH ⟪⟪a, cantor c w, d, b⟫, δ + 1, 0⟫ = ⟪⟪b, w, d, c⟫, δ, 0⟫ := by
  unfold SH
  rw [tstep_shift S 0 0 a (cantor c w) d b δ hh]
  simp

lemma tstep_SH_halt (a b w d δ : V) (hh : a + b = 1) :
    tstep S SH ⟪⟪a, w, d, b⟫, δ, 0⟫ = ⟪⟪a, w, d, b⟫, δ, 1⟫ := by
  unfold SH
  exact tstep_shift_halt S 0 0 a w d b δ hh

lemma tstep_MP_yes (y t w d h δ : V) (hm : 4 * cantor t (d + y) = h) :
    tstep S (MP y) ⟪⟪t, w, d, h⟫, δ, 0⟫ = ⟪⟪d + y, cantor 0 w, d + y, 0⟫, δ + 1, 0⟫ := by
  unfold MP
  exact tstep_mp_yes S y 0 t w d h δ hm

lemma tstep_MP_no (y t w d h δ : V) (hm : 4 * cantor t (d + y) ≠ h) :
    tstep S (MP y) ⟪⟪t, w, d, h⟫, δ, 0⟫ = ⟪⟪0, w, d + y, 0⟫, δ, 0⟫ := by
  unfold MP
  exact tstep_mp_no S y 0 t w d h δ hm

/-- The ten entries pushed by AX, top first. -/
def items (f : ℕ → V) (g t : V) : List V := [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, g, t]

lemma stack10_eq (f : ℕ → V) (g t w : V) : stack10 f g t w = (items f g t).foldr cantor w := rfl

lemma tstep_AX (A y x t w d h δ : V) :
    tstep S (AX A y x) ⟪⟪t, w, d, h⟫, δ, 0⟫ =
      ⟪⟪S.axT (h + y) (d + x) A,
          (items (fun i => S.leaf i (d + x) (h + y) A d) (4 * cantor h d + 2) t).foldr cantor w,
          0, 0⟫, δ + ((10 : ℕ) : V), 0⟫ := by
  unfold AX
  rw [tstep_ax S A y x t w d h δ, stack10_eq]
  have he : δ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = δ + ((10 : ℕ) : V) := by
    push_cast
    ring
  rw [he]

/-- The two registers after shifting through a list. -/
def last2 : V → V → List V → V × V
  | a, b, [] => (a, b)
  | _, b, x :: xs => last2 b x xs

/-- No SHIFT of the window halts. -/
def NoHalt : V → V → List V → Prop
  | _, _, [] => True
  | a, b, x :: xs => a + b ≠ 1 ∧ NoHalt b x xs

/-- SHIFTs through the entries `xs` on top of the stack. -/
lemma shifts_run (xs : List V) : ∀ (a b w d δ W τ : V), NoHalt a b xs →
    texec S W τ = ⟪⟪a, xs.foldr cantor w, d, b⟫, δ + (xs.length : V), 0⟫ →
    texec S (shifts xs.length W) τ =
      ⟪⟪(last2 a b xs).1, w, d, (last2 a b xs).2⟫, δ, 0⟫ := by
  induction xs with
  | nil =>
    intro a b w d δ W τ _ h
    simpa [shifts, last2] using h
  | cons x xs ih =>
    intro a b w d δ W τ hn h
    have h1 : texec S (snoc W SH) τ =
        ⟪⟪b, xs.foldr cantor w, d, x⟫, δ + (xs.length : V), 0⟫ := by
      rw [texec_snoc, h]
      have he : δ + ((x :: xs).length : V) = δ + (xs.length : V) + 1 := by
        simp [add_assoc]
      rw [he, List.foldr_cons]
      exact tstep_SH S a b x _ d _ hn.1
    exact ih b x w d δ (snoc W SH) τ hn.2 h1

/-- AX followed by SHIFTs through the first entries `xs` of the ten. -/
lemma ax_shifts (A y x t w d h δ : V) (xs ys : List V)
    (hsplit : items (fun i => S.leaf i (d + x) (h + y) A d) (4 * cantor h d + 2) t = xs ++ ys)
    (hn : NoHalt (S.axT (h + y) (d + x) A) 0 xs) (W τ : V)
    (hW : texec S W τ = ⟪⟪t, w, d, h⟫, δ, 0⟫) :
    texec S (shifts xs.length (snoc W (AX A y x))) τ =
      ⟪⟪(last2 (S.axT (h + y) (d + x) A) 0 xs).1, ys.foldr cantor w, 0,
          (last2 (S.axT (h + y) (d + x) A) 0 xs).2⟫, δ + (ys.length : V), 0⟫ := by
  apply shifts_run S xs _ _ _ _ _ _ _ hn
  rw [texec_snoc, hW, tstep_AX, hsplit, List.foldr_append]
  have hl : ((10 : ℕ) : V) = (ys.length : V) + (xs.length : V) := by
    have h10 := congrArg List.length hsplit
    simp only [items, List.length_cons, List.length_nil, List.length_append] at h10
    have h10' : (10 : ℕ) = ys.length + xs.length := by omega
    rw [← Nat.cast_add, ← h10']
  rw [hl, add_assoc]

/-- The ten-shift identity: the generalization in `t`, the old top in `h`, the stack restored. -/
lemma ax_all (A y x t w d h δ W τ : V) (hW : texec S W τ = ⟪⟪t, w, d, h⟫, δ, 0⟫) :
    texec S (shifts 10 (snoc W (AX A y x))) τ = ⟪⟪4 * cantor h d + 2, w, 0, t⟫, δ, 0⟫ := by
  have h := ax_shifts S A y x t w d h δ
    (items (fun i => S.leaf i (d + x) (h + y) A d) (4 * cantor h d + 2) t) [] (by simp)
    (by simp [NoHalt, items, add_ne_one, S.leaf_ne_one, S.axT_ne_one, allV_ne_one]) W τ hW
  simpa [items, last2] using h

/-- Nine shifts: the last leaf in `t`, the generalization in `h`, the old top pushed. -/
lemma ax_nine (A y x t w d h δ W τ : V) (hW : texec S W τ = ⟪⟪t, w, d, h⟫, δ, 0⟫) :
    texec S (shifts 9 (snoc W (AX A y x))) τ =
      ⟪⟪S.leaf 7 (d + x) (h + y) A d, cantor t w, 0, 4 * cantor h d + 2⟫, δ + 1, 0⟫ := by
  have h := ax_shifts S A y x t w d h δ
    [S.leaf 0 (d + x) (h + y) A d, S.leaf 1 (d + x) (h + y) A d, S.leaf 2 (d + x) (h + y) A d,
      S.leaf 3 (d + x) (h + y) A d, S.leaf 4 (d + x) (h + y) A d, S.leaf 5 (d + x) (h + y) A d,
      S.leaf 6 (d + x) (h + y) A d, S.leaf 7 (d + x) (h + y) A d, 4 * cantor h d + 2] [t] rfl
    (by simp [NoHalt, add_ne_one, S.leaf_ne_one, S.axT_ne_one, allV_ne_one]) W τ hW
  simpa [last2] using h

lemma shifts_succ' (k : ℕ) : ∀ W : V, shifts (k + 1) W = snoc (shifts k W) SH := by
  induction k with
  | zero => intro W; rfl
  | succ k ih =>
    intro W
    show shifts (k + 1) (snoc W SH) = snoc (shifts k (snoc W SH)) SH
    exact ih (snoc W SH)

/-! ## POP, PUSH, DISCARD -/

/-- Remove the top stack entry into `h`; the top `t` is kept, `d` is cleared. -/
def POP : V := shifts 11 (snoc 0 (AX 0 0 0))

lemma pop_run (t a w d h δ : V) :
    texec S POP ⟪⟪t, cantor a w, d, h⟫, δ + 1, 0⟫ = ⟪⟪t, w, 0, a⟫, δ, 0⟫ := by
  rw [POP, shifts_succ', texec_snoc,
    ax_all S 0 0 0 t (cantor a w) d h (δ + 1) 0 _ (by simp)]
  exact tstep_SH S _ t a w 0 δ (allV_add_ne_one _ _)

/-- `W` followed by `k` POPs. -/
def pops : ℕ → V → V
  | 0, W => W
  | k + 1, W => pops k (W ⧺ POP)

lemma pops_run (xs : List V) : ∀ (t a w d h δ W τ : V),
    texec S W τ = ⟪⟪t, (xs ++ [a]).foldr cantor w, d, h⟫, δ + ((xs.length + 1 : ℕ) : V), 0⟫ →
    texec S (pops (xs.length + 1) W) τ = ⟪⟪t, w, 0, a⟫, δ, 0⟫ := by
  induction xs with
  | nil =>
    intro t a w d h δ W τ hW
    show texec S (W ⧺ POP) τ = _
    rw [texec_seqApp, hW]
    simpa using pop_run S t a w d h δ
  | cons x xs ih =>
    intro t a w d h δ W τ hW
    show texec S (pops (xs.length + 1) (W ⧺ POP)) τ = _
    apply ih t a w 0 x δ
    rw [texec_seqApp, hW]
    have he : δ + (((x :: xs).length + 1 : ℕ) : V) = δ + ((xs.length + 1 : ℕ) : V) + 1 := by
      push_cast [List.length_cons]
      ring
    rw [he]
    simp only [List.cons_append, List.foldr_cons]
    exact pop_run S t x _ d h _

/-- Save the top on the stack; the top becomes `0`. -/
def PUSH : V := snoc (shifts 9 (snoc 0 (AX 0 0 0))) (MP 0)

lemma push_run (t w δ : V) :
    texec S PUSH ⟪⟪t, w, 0, 0⟫, δ, 0⟫ = ⟪⟪0, cantor t w, 0, 0⟫, δ + 1, 0⟫ := by
  rw [PUSH, texec_snoc, ax_nine S 0 0 0 t w 0 0 δ 0 _ (by simp),
    tstep_MP_no S 0 _ _ 0 _ _ (four_mul_ne _ _)]
  simp

/-- Replace the top by `0`. -/
def DISCARD : V := snoc (shifts 10 (snoc (snoc 0 (MP 1)) (AX 1 0 0))) (MP 0)

lemma discard_run (t w δ : V) :
    texec S DISCARD ⟪⟪t, w, 0, 0⟫, δ, 0⟫ = ⟪⟪0, w, 0, 0⟫, δ, 0⟫ := by
  have h1 : texec S (snoc 0 (MP 1)) ⟪⟪t, w, 0, 0⟫, δ, 0⟫ = ⟪⟪0, w, 0 + 1, 0⟫, δ, 0⟫ := by
    rw [texec_snoc, texec_nil]
    exact tstep_MP_no S 1 t w 0 0 δ (four_mul_ne_zero (cantor_ne_zero_right (by simp)))
  rw [DISCARD, texec_snoc, ax_all S 1 0 0 0 w (0 + 1) 0 δ _ _ h1,
    tstep_MP_no S 0 _ _ 0 _ _ (four_mul_ne_zero (cantor_ne_zero_left (allV_ne_zero _)))]
  simp

/-- Set the cache `d` to `d` when top and caches are `0`. -/
def offset (d W : V) : V := if d = 0 then W else snoc W (MP d)

lemma offset_run (d w δ W τ : V) (hW : texec S W τ = ⟪⟪0, w, 0, 0⟫, δ, 0⟫) :
    texec S (offset d W) τ = ⟪⟪0, w, d, 0⟫, δ, 0⟫ := by
  unfold offset
  by_cases hd : d = 0
  · rw [if_pos hd, hW, hd]
  · rw [if_neg hd, texec_snoc, hW,
      tstep_MP_no S d 0 w 0 0 δ (four_mul_ne_zero (cantor_ne_zero_right (by simpa using hd)))]
    simp

/-- A halted state stays halted under any word. -/
lemma halted_exec (W τ : V) (h : flg(τ) = 1) : flg(texec S W τ) = 1 := by
  rw [texec_of_flag S W τ (by rw [h]; simp)]
  exact h

end model
end ConPA.Words
