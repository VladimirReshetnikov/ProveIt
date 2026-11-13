import DiophantineConsistency.ArithmeticWangTable
import DiophantineConsistency.ArithmeticMachineRun215

/-! The periodic plane of an internal marked cyclic word, and the encoded
machine row colours, inside every model of IΣ1.

A word `a` on `Z/N` (internal, possibly nonstandard `N`) is pulled back to the
quadrant by `address(X,t) = (N-1)·(X + s·t) mod N`; column `X` stands for the
external column `X - N`. Horizontal and temporal matching, both periods and
the Start origin are elementary residue arithmetic. Machine configurations are
the codes of `ArithmeticMachineRun215`: `P(state, P(left, right))`, least
significant bit nearest the head, with an absolute head column carried
separately. `Colored` is the row colour of a configuration at a column. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticWangPlane
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticWangTable ArithmeticCantor

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance first_definable' : 𝚺₀-Function₁[V] first := first_defined.to_definable
instance second_definable' : 𝚺₀-Function₁[V] second := second_defined.to_definable

/-! ## Marked words and their plane -/

/-- A marked cyclic word on `Z/N` with internal stride `s`. Index `j'` is the
east neighbour of `j` when `j' + 1 ≡ j`, and lies one row below `j` when
`j' + s ≡ j`. -/
structure MarkedWord (a : V → V) (N s : V) : Prop where
  pos : 0 < N
  tile_lt : ∀ j < N, a j < 942
  marker : a 0 = 0
  east : ∀ j < N, ∀ j' < N, (j' + 1) % N = j → eastC (a j) = westC (a j')
  south : ∀ j < N, ∀ j' < N, (j' + s) % N = j → southC (a j) = northC (a j')

def adr (N s X t : V) : V := ((N - 1) * X + (N - 1) * s * t) % N

def pl (a : V → V) (N s X t : V) : V := a (adr N s X t)

instance pl_definable (a : V → V) [𝚺₁-Function₁ a] (N s : V) :
    𝚺₁-Function₂ (pl a N s) := by
  unfold pl adr; definability

theorem mod_add_mod {N : V} (x y : V) (hN : 0 < N) : (x % N + y) % N = (x + y) % N := by
  rw [mod_add hN, mod_eq_self_of_lt (mod_lt x hN), ← mod_add hN]

section plane
variable {a : V → V} {N s : V} (h : MarkedWord a N s)
include h

theorem adr_lt (X t : V) : adr N s X t < N := mod_lt _ h.pos

theorem pl_lt (X t : V) : pl a N s X t < 942 := h.tile_lt _ (adr_lt h X t)

theorem one_le : 1 ≤ N := pos_iff_one_le.mp h.pos

theorem pl_east (X t : V) : eastC (pl a N s X t) = westC (pl a N s (X + 1) t) := by
  apply h.east _ (adr_lt h X t) _ (adr_lt h (X + 1) t)
  unfold adr
  rw [mod_add_mod _ _ h.pos]
  have he : (N - 1) * (X + 1) + (N - 1) * s * t + 1 =
      ((N - 1) * X + (N - 1) * s * t) + N * 1 := by
    have := sub_add_self_of_le (one_le h)
    calc _ = ((N - 1) * X + (N - 1) * s * t) + (N - 1 + 1) := by ring
      _ = _ := by rw [this, mul_one]
  rw [he, mod_add_mul' _ _ h.pos]

theorem pl_south (X t : V) : southC (pl a N s X t) = northC (pl a N s X (t + 1)) := by
  apply h.south _ (adr_lt h X t) _ (adr_lt h X (t + 1))
  unfold adr
  rw [mod_add_mod _ _ h.pos]
  have he : (N - 1) * X + (N - 1) * s * (t + 1) + s =
      ((N - 1) * X + (N - 1) * s * t) + N * s := by
    have := sub_add_self_of_le (one_le h)
    calc _ = ((N - 1) * X + (N - 1) * s * t) + (N - 1 + 1) * s := by ring
      _ = _ := by rw [this]
  rw [he, mod_add_mul' _ _ h.pos]

theorem pl_period_x (X t : V) : pl a N s (X + N) t = pl a N s X t := by
  unfold pl adr
  have he : (N - 1) * (X + N) + (N - 1) * s * t =
      ((N - 1) * X + (N - 1) * s * t) + N * (N - 1) := by ring
  rw [he, mod_add_mul' _ _ h.pos]

theorem pl_period_t (X t : V) : pl a N s X (t + N) = pl a N s X t := by
  unfold pl adr
  have he : (N - 1) * X + (N - 1) * s * (t + N) =
      ((N - 1) * X + (N - 1) * s * t) + N * ((N - 1) * s) := by ring
  rw [he, mod_add_mul' _ _ h.pos]

theorem pl_origin : pl a N s N 0 = 0 := by
  unfold pl adr
  have he : (N - 1) * N + (N - 1) * s * 0 = 0 + N * (N - 1) := by ring
  rw [he, mod_add_mul' _ _ h.pos, zero_mod, h.marker]

theorem pl_zero : pl a N s 0 0 = 0 := by
  unfold pl adr
  simp [h.marker]

theorem pl_origin_N : pl a N s N N = 0 := by
  simpa only [zero_add, pl_origin h] using pl_period_t h N 0

end plane

/-! ## Binary tape halves -/

theorem fbit_zero_eq (x : V) : fbit x 0 = x % 2 := by
  rcases even_or_odd' x with hx | hx
  · rw [hx]; simp
  · rw [hx, fbit_two_mul_add_one_zero_eq_one, mod_mul_add' _ _ (by simp : (0:V) < 2),
      mod_eq_self_of_lt (by simp : (1:V) < 2)]

theorem fbit_succ (x i : V) : fbit x (i + 1) = fbit (x / 2) i := by
  rcases even_or_odd' x with hx | hx
  · rw [hx]; simp
  · rw [hx, two_mul_add_one_div_two]; simp

theorem bit_cases {w : V} (hw : w ≤ 1) : w = 0 ∨ w = 1 := le_one_iff_eq_zero_or_one.mp hw

theorem fbit_push_succ (x w i : V) (hw : w ≤ 1) : fbit (2 * x + w) (i + 1) = fbit x i := by
  rcases bit_cases hw with rfl | rfl <;> simp

theorem fbit_push_zero (x w : V) (hw : w ≤ 1) : fbit (2 * x + w) 0 = w := by
  rcases bit_cases hw with rfl | rfl <;> simp

theorem push_div (x w : V) (hw : w ≤ 1) : (w + 2 * x) / 2 = x := by
  have hw2 : w < 2 := lt_of_le_of_lt hw (by norm_num)
  rw [show w + 2*x = x*2 + w by ring, div_mul_add _ _ hw2]

theorem push_mod (x w : V) (hw : w ≤ 1) : (w + 2 * x) % 2 = w := by
  have hw2 : w < 2 := lt_of_le_of_lt hw (by norm_num)
  rw [mod_add_mul' _ _ (by norm_num : (0:V) < 2), mod_eq_self_of_lt hw2]

/-- The tape bit at column `X` of halves `l, r` with head column `H`. -/
def tb (l r H X : V) : V := if H ≤ X then fbit r (X - H) else fbit l (H - X - 1)

theorem tb_le (l r H X : V) : tb l r H X ≤ 1 := by
  unfold tb; split <;> simp

theorem tb_head (l r H : V) : tb l r H H = r % 2 := by
  simp [tb, fbit_zero_eq]

/-- A right move: the written bit is pushed onto the left half. -/
theorem tb_right (l r w H X : V) (hw : w ≤ 1) (hX : X ≠ H) :
    tb (2 * l + w) (r / 2) (H + 1) X = tb l r H X := by
  unfold tb
  rcases lt_or_gt_of_ne hX with hlt | hgt
  · have h1 : ¬ H + 1 ≤ X := by
      intro h; exact absurd (lt_of_lt_of_le (lt_add_one H) h) (not_lt.mpr hlt.le)
    have h2 : ¬ H ≤ X := not_le.mpr hlt
    rw [if_neg h1, if_neg h2]
    obtain ⟨i, rfl⟩ : ∃ i, H = X + 1 + i := ⟨H - (X + 1), by
      rw [add_tsub_cancel_of_le (lt_iff_succ_le.mp hlt)]⟩
    have e1 : X + 1 + i + 1 - X - 1 = i + 1 := by
      rw [show X + 1 + i + 1 = X + (i + 1 + 1) by ring, add_tsub_cancel_left,
        add_tsub_cancel_right]
    have e2 : X + 1 + i - X - 1 = i := by
      rw [show X + 1 + i = X + (i + 1) by ring, add_tsub_cancel_left, add_tsub_cancel_right]
    rw [e1, e2, fbit_push_succ _ _ _ hw]
  · have h1 : H + 1 ≤ X := lt_iff_succ_le.mp hgt
    rw [if_pos h1, if_pos hgt.le]
    obtain ⟨i, rfl⟩ : ∃ i, X = H + 1 + i := ⟨X - (H + 1), by rw [add_tsub_cancel_of_le h1]⟩
    rw [add_tsub_cancel_left, show H + 1 + i = H + (i + 1) by ring, add_tsub_cancel_left,
      fbit_succ]

theorem tb_right_old (l r w H : V) (hw : w ≤ 1) : tb (2 * l + w) (r / 2) (H + 1) H = w := by
  unfold tb
  rw [if_neg (by simp), show H + 1 - H - 1 = 0 by simp, fbit_push_zero _ _ hw]

/-- A left move: the left half's nearest bit and the written bit are pushed
onto the right half. -/
theorem le_add_self' (x y : V) : x ≤ x + y := le_add_of_nonneg_right (Arithmetic.zero_le y)

theorem tb_left (l r w H X : V) (hw : w ≤ 1) (hX : X ≠ H + 1) :
    tb (l / 2) (l % 2 + 2 * (w + 2 * (r / 2))) H X = tb l r (H + 1) X := by
  have hm : l % 2 ≤ 1 := lt_two_iff_le_one.mp (by simp)
  unfold tb
  rcases lt_trichotomy X H with hlt | heq | hgt
  · rw [if_neg (not_le.mpr hlt), if_neg (not_le.mpr (lt_trans hlt (lt_add_one H)))]
    obtain ⟨i, rfl⟩ : ∃ i, H = X + 1 + i := ⟨H - (X + 1), by
      rw [add_tsub_cancel_of_le (lt_iff_succ_le.mp hlt)]⟩
    have e1 : X + 1 + i - X - 1 = i := by
      rw [show X + 1 + i = X + (i + 1) by ring, add_tsub_cancel_left, add_tsub_cancel_right]
    have e2 : X + 1 + i + 1 - X - 1 = i + 1 := by
      rw [show X + 1 + i + 1 = X + (i + 1 + 1) by ring, add_tsub_cancel_left,
        add_tsub_cancel_right]
    rw [e1, e2, fbit_succ l i]
  · subst heq
    rw [if_pos le_rfl, if_neg (by simp), tsub_self, fbit_zero_eq,
      show X + 1 - X - 1 = 0 by simp, fbit_zero_eq, push_mod _ _ hm]
  · have h1 : H + 1 < X := lt_of_le_of_ne (lt_iff_succ_le.mp hgt) (Ne.symm hX)
    obtain ⟨i, rfl⟩ : ∃ i, X = H + 1 + 1 + i := ⟨X - (H + 1 + 1), by
      rw [add_tsub_cancel_of_le (lt_iff_succ_le.mp h1)]⟩
    rw [if_pos (by rw [add_assoc, add_assoc]; exact le_add_self' _ _),
      if_pos (by rw [add_assoc (H + 1)]; exact le_add_self' _ _)]
    rw [show H + 1 + 1 + i - H = (i + 1) + 1 by
      rw [show H + 1 + 1 + i = H + (i + 1 + 1) by ring, add_tsub_cancel_left],
      show H + 1 + 1 + i - (H + 1) = i + 1 by
      rw [show H + 1 + 1 + i = (H + 1) + (i + 1) by ring, add_tsub_cancel_left]]
    rw [fbit_succ _ (i + 1), push_div _ _ hm, fbit_succ (w + 2 * (r / 2)) i, push_div _ _ hw,
      fbit_succ r i]

theorem tb_left_old (l r w H : V) (hw : w ≤ 1) :
    tb (l / 2) (l % 2 + 2 * (w + 2 * (r / 2))) H (H + 1) = w := by
  unfold tb
  have hm : l % 2 ≤ 1 := lt_two_iff_le_one.mp (by simp)
  rw [if_pos (by simp), add_tsub_cancel_left, show (1 : V) = 0 + 1 by simp, fbit_succ,
    push_div _ _ hm, fbit_zero_eq, push_mod _ _ hw]

/-! ## Row colours of configurations -/

def colorV (c H X : V) : V :=
  if X = H then hcV (first c) (second (second c) % 2)
  else tb (first (second c)) (second (second c)) H X

/-- A first-order form of `n = colorV c H X`, used in induction motives. -/
def Colored (n c H X : V) : Prop :=
  (X = H ∧ ((first c = 0 ∧ n = 432 + second (second c) % 2) ∨
    (first c ≠ 0 ∧ n = 2 * first c + second (second c) % 2))) ∨
  (H < X ∧ n = fbit (second (second c)) (X - H)) ∨
  (X < H ∧ n = fbit (first (second c)) (H - X - 1))

instance colored_definable : 𝚺₁-Relation₄[V] Colored := by
  unfold Colored; definability

theorem colored_iff (n c H X : V) : Colored n c H X ↔ n = colorV c H X := by
  unfold Colored colorV tb hcV
  rcases lt_trichotomy X H with hlt | rfl | hgt
  · have h1 : X ≠ H := ne_of_lt hlt
    have h2 : ¬ H ≤ X := not_le.mpr hlt
    simp [h1, h2, hlt, not_lt.mpr hlt.le]
  · by_cases h0 : first c = 0 <;> simp [h0]
  · have h1 : X ≠ H := ne_of_gt hgt
    simp [h1, hgt, hgt.le, not_lt.mpr hgt.le]

theorem colorV_le {c H X : V} (hc : first c ≤ 215) : colorV c H X ≤ 433 := by
  unfold colorV
  split
  · unfold hcV
    have hb : second (second c) % 2 ≤ 1 := by
      rcases mod_two (second (second c)) with h | h <;> simp [h]
    split
    · calc 432 + second (second c) % 2 ≤ 432 + 1 := add_le_add le_rfl hb
        _ = 433 := by norm_num
    · calc 2 * first c + second (second c) % 2 ≤ 2 * 215 + 1 :=
            add_le_add (mul_le_mul_left' hc 2) hb
        _ ≤ 433 := by norm_num
  · exact le_trans (tb_le _ _ _ _) (by norm_num)

/-! ## The represented step from an operating configuration -/

theorem step_apply (c st' d w : V) (hd : d ≤ 1) (hw : w ≤ 1)
    (hA : ArithmeticMachineGraph215.actionLookup (first c) (second (second c) % 2) =
      1 + 4 * st' + 2 * d + w) :
    ArithmeticMachineStep215.stepValue c =
      if d = 0 then
        cantor st' (cantor (first (second c) / 2)
          (first (second c) % 2 + 2 * (w + 2 * (second (second c) / 2))))
      else cantor st' (cantor (2 * first (second c) + w) (second (second c) / 2)) := by
  unfold ArithmeticMachineStep215.stepValue ArithmeticMachineStepPerm252.genericStepValue
  dsimp only
  have hpos : (0 : V) < 1 + 4 * st' + 2 * d + w := by positivity
  rw [hA, if_neg (ne_of_gt hpos)]
  unfold ArithmeticMachineStepPerm252.applyValue
  dsimp only
  have hz : 1 + 4 * st' + 2 * d + w - 1 = 4 * st' + (2 * d + w) := by
    rw [show 1 + 4 * st' + 2 * d + w = (4 * st' + (2 * d + w)) + 1 by ring,
      add_tsub_cancel_right]
  have h24 : 2 * d + w < 4 := by
    calc 2 * d + w ≤ 2 * 1 + 1 := add_le_add (mul_le_mul_left' hd 2) hw
      _ < 4 := by norm_num
  have hw2 : w < 2 := lt_of_le_of_lt hw (by norm_num)
  have hd2 : d < 2 := lt_of_le_of_lt hd (by norm_num)
  have e4 : (4 * st' + (2 * d + w)) / 4 = st' := div_mul_add' st' 4 h24
  have e2' : 4 * st' + (2 * d + w) = 2 * (2 * st' + d) + w := by ring
  have e2 : (4 * st' + (2 * d + w)) / 2 = 2 * st' + d := by
    rw [e2']; exact div_mul_add' _ 2 hw2
  have em : (2 * st' + d) % 2 = d := by
    rw [mod_mul_add' _ _ (by norm_num : (0:V) < 2), mod_eq_self_of_lt hd2]
  have ew : (4 * st' + (2 * d + w)) % 2 = w := by
    rw [e2', mod_mul_add' _ _ (by norm_num : (0:V) < 2), mod_eq_self_of_lt hw2]
  rw [hz, e4, e2, em, ew]

open ArithmeticMachineRun215 (run run_succ run_zero)
open ArithmeticMachinePerm252 ArithmeticMachineGraphPerm252

/-- The blank configuration reads the initial K215 action. -/
theorem initial_action :
    ArithmeticMachineGraph215.actionLookup (first (1 : V)) (second (second (1 : V)) % 2) =
      1 + 4 * 2 + 2 * 1 + 1 := by
  have hzero : cantor (0 : V) 0 = 0 := by simp [cantor, triangle]
  have hone : cantor (1 : V) 0 = 1 := by simp [cantor, triangle, one_add_one_eq_two]
  have hcode : actCode 0 = 12 := by decide +kernel
  have h1 : (1 : V) = cantor 1 (cantor 0 0) := by rw [hzero, hone]
  have f1 : first (1 : V) = 1 := by
    have := first_cantor (1 : V) (cantor 0 0); rwa [← h1] at this
  have s1 : second (1 : V) = 0 := by
    have := second_cantor (1 : V) (cantor 0 0); rwa [← h1, hzero] at this
  have s0 : second (0 : V) = 0 := by
    have := second_cantor (0 : V) 0; rwa [hzero] at this
  have hl : lookupNat ArithmeticMachineGraph215.literalRows 0 1 0 = 12 := by
    have := lookup_eq_actCode 0 0 (by norm_num) (by norm_num)
    simpa [hcode] using this
  rw [f1, s1, s0, zero_mod]
  have := lookupValue_cast (V := V) ArithmeticMachineGraph215.literalRows 0 1 0
  rw [hl] at this
  simp only [Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat] at this
  simp only [ArithmeticMachineGraph215.actionLookup]
  rw [this]; norm_num

/-- The first blank machine step, shared by the row and trace proofs. -/
theorem initial_run_one : run (1 : V) = cantor 2 (cantor 1 0) := by
  have hzero : cantor (0 : V) 0 = 0 := by simp [cantor, triangle]
  have hone : cantor (1 : V) 0 = 1 := by simp [cantor, triangle, one_add_one_eq_two]
  have h1 : (1 : V) = cantor 1 (cantor 0 0) := by rw [hzero, hone]
  have s1 : second (1 : V) = 0 := by
    have := second_cantor (1 : V) (cantor 0 0); rwa [← h1, hzero] at this
  have f0 : first (0 : V) = 0 := by
    have := first_cantor (0 : V) 0; rwa [hzero] at this
  have s0 : second (0 : V) = 0 := by
    have := second_cantor (0 : V) 0; rwa [hzero] at this
  have hs := step_apply (1 : V) 2 1 1 le_rfl le_rfl (initial_action (V := V))
  have hr := run_succ (0 : V)
  rw [zero_add, run_zero] at hr
  rw [hr, hs, if_neg _root_.one_ne_zero, s1, f0, s0]
  simp

end DiophantineConsistency.ArithmeticWangPlane
