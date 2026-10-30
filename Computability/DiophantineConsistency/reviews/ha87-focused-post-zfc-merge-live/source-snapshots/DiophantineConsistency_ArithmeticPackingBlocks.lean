import DiophantineConsistency.ArithmeticCyclicWord

/-! **K3a — represented block sums** `Σ_{j<n} 2^{wj}·f j` at arbitrary internal
length, in every model of IΣ1 (construction spec §5 P3 and §11.3, the generic
base-`B` block library).

For a Σ1-definable family `f` with `f j < 2^w` for `j < n`, `bsum w f n` is the
unique number below `2^{wn}` whose radix-`2^w` digits are `f 0, …, f (n-1)`
(`Blocks`). It is defined by choice from an internal existence proof, so no
primitive-recursive blueprint is needed per family; all laws are proved by
internal Σ1 induction:
* `bsum_succ` — `bsum (n+1) = bsum n + f n·2^{wn}`; `bsum_lt`; `dig_bsum`;
* `bsum_unique` — any number with the same digits is `bsum`;
* `bsum_add`, `bsum_mul_const` — linearity under digitwise bounds;
* `bsum_noCarry` — blockwise `NoCarry` concatenates;
* `bsum_cyc` — the cyclic re-indexing `j ↦ f (cyc n j e)` is the rotation
  `rot w n (bsum f n) e`, hence `≡ 2^{we}·bsum f n (mod 2^{wn}-1)`;
* `bsum_const_rep` — the constant family is the repunit multiple;
* `bsum_add_origin`, `bsum_sub_origin` — changing only block `0`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.ArithmeticPackingBlocks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry ArithmeticRepunit

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Concatenation of digits and bits -/

/-- `Y` has radix-`2^w` digits `f 0, …, f (n-1)` and is below `2^{wn}`. -/
def Blocks (w : V) (f : V → V) (n Y : V) : Prop :=
  Y < Exp.exp (w * n) ∧ ∀ j < n, dig w Y j = f j

instance blocks_definable (w : V) (f : V → V) [𝚺₁-Function₁ f] :
    𝚺₁-Relation (Blocks w f) := by
  unfold Blocks; definability

theorem blocks_succ {w n Y : V} {f : V → V} (h : Blocks w f n Y) (hf : f n < Exp.exp w) :
    Blocks w f (n + 1) (Y + f n * Exp.exp (w * n)) := by
  obtain ⟨hY, hd⟩ := h
  refine ⟨?_, fun j hj => ?_⟩
  · calc Y + f n * Exp.exp (w * n) < Exp.exp (w * n) + f n * Exp.exp (w * n) :=
          add_lt_add_of_lt_of_le hY le_rfl
      _ = (f n + 1) * Exp.exp (w * n) := by ring
      _ ≤ Exp.exp w * Exp.exp (w * n) :=
          mul_le_mul_of_nonneg_right (lt_iff_succ_le.mp hf) (by simp)
      _ = Exp.exp (w * (n + 1)) := by rw [exp_mul_succ, mul_comm]
  · rcases lt_or_eq_of_le (lt_iff_succ_le.mp hj |> fun h => le_of_add_le_add_right h) with h | h
    · rw [dig_add_mul_high _ _ _ _ _ h]; exact hd j h
    · subst h
      rw [add_comm, dig_mul_add_high _ _ _ _ _ hY le_rfl, tsub_self, dig_zero_index,
        mod_eq_self_of_lt hf]

theorem blocks_zero (w : V) (f : V → V) : Blocks w f 0 0 :=
  ⟨by simp, fun j hj => absurd hj (by simp)⟩

theorem blocks_mod_eq {w n Y Y' : V} {f : V → V} (h : Blocks w f n Y) (h' : Blocks w f n Y')
    (m : V) : m ≤ n → Y % Exp.exp (w * m) = Y' % Exp.exp (w * m) := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; simp
  case succ m ih =>
    intro hm
    have hm' : m < n := lt_of_lt_of_le (lt_add_one m) hm
    rw [mod_exp_succ, mod_exp_succ, ih hm'.le, h.2 m hm', h'.2 m hm']

theorem blocks_unique {w n Y Y' : V} {f : V → V} (h : Blocks w f n Y) (h' : Blocks w f n Y') :
    Y = Y' := by
  have := blocks_mod_eq h h' n le_rfl
  rwa [mod_eq_self_of_lt h.1, mod_eq_self_of_lt h'.1] at this

theorem blocks_exists (w : V) (f : V → V) [𝚺₁-Function₁ f] (n : V)
    (hf : ∀ j < n, f j < Exp.exp w) : ∃ Y, Blocks w f n Y := by
  induction n using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => exact ⟨0, blocks_zero w f⟩
  | succ n ih =>
    obtain ⟨Y, hY⟩ := ih (fun j hj => hf j (lt_trans hj (lt_add_one n)))
    exact ⟨_, blocks_succ hY (hf n (lt_add_one n))⟩

/-! ## The block sum -/

/-- `Σ_{j<n} 2^{wj}·f j`, as the number with these radix-`2^w` digits. -/
def bsum (w : V) (f : V → V) (n : V) : V :=
  open Classical in if h : ∃ Y, Blocks w f n Y then h.choose else 0

section
variable {w : V} {f : V → V} [𝚺₁-Function₁ f]

theorem bsum_blocks {n : V} (hf : ∀ j < n, f j < Exp.exp w) : Blocks w f n (bsum w f n) := by
  have h := blocks_exists w f n hf
  unfold bsum
  rw [dif_pos h]
  exact h.choose_spec

theorem bsum_lt {n : V} (hf : ∀ j < n, f j < Exp.exp w) : bsum w f n < Exp.exp (w * n) :=
  (bsum_blocks hf).1

theorem dig_bsum {n j : V} (hf : ∀ j < n, f j < Exp.exp w) (hj : j < n) :
    dig w (bsum w f n) j = f j := (bsum_blocks hf).2 j hj

theorem bsum_unique {n Y : V} (hf : ∀ j < n, f j < Exp.exp w) (h : Blocks w f n Y) :
    bsum w f n = Y := blocks_unique (bsum_blocks hf) h

@[simp] theorem bsum_zero : bsum w f 0 = 0 :=
  bsum_unique (fun j hj => absurd hj (by simp)) (blocks_zero w f)

theorem bsum_succ {n : V} (hf : ∀ j < n + 1, f j < Exp.exp w) :
    bsum w f (n + 1) = bsum w f n + f n * Exp.exp (w * n) := by
  have hf' : ∀ j < n, f j < Exp.exp w := fun j hj => hf j (lt_trans hj (lt_add_one n))
  exact bsum_unique hf (blocks_succ (bsum_blocks hf') (hf n (lt_add_one n)))

theorem bsum_graph {n : V} (hf : ∀ j < n, f j < Exp.exp w) (y : V) :
    y = bsum w f n ↔ Blocks w f n y :=
  ⟨fun e => e ▸ bsum_blocks hf, fun h => (bsum_unique hf h).symm⟩

end

/-- Under a global digit bound, the block sum is a Σ1 function of the length. -/
theorem bsum_definable (w : V) (f : V → V) [𝚺₁-Function₁ f] (hf : ∀ j, f j < Exp.exp w) :
    𝚺₁-Function₁ (bsum w f) := by
  have hR : 𝚺₁.Definable (fun v : Fin 2 → V => Blocks w f (v 1) (v 0)) := by
    unfold Blocks; definability
  exact hR.of_iff fun v => bsum_graph (fun j _ => hf j) (v 0)

/-! ## Linearity -/

section linear
variable {w : V} {f g h : V → V} [𝚺₁-Function₁ f] [𝚺₁-Function₁ g] [𝚺₁-Function₁ h]

theorem blocks_add {n : V} (hfg : ∀ j < n, f j + g j < Exp.exp w)
    (hh : ∀ j < n, h j = f j + g j) :
    ∀ m, m ≤ n → ∃ Yf Yg, Blocks w f m Yf ∧ Blocks w g m Yg ∧ Blocks w h m (Yf + Yg) := by
  intro m
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro _; exact ⟨0, 0, blocks_zero w f, blocks_zero w g, by simpa using blocks_zero w h⟩
  case succ m ih =>
    intro hm
    have hm' : m < n := lt_of_lt_of_le (lt_add_one m) hm
    obtain ⟨Yf, Yg, hYf, hYg, hYh⟩ := ih hm'.le
    have hlt := hfg m hm'
    have hf : f m < Exp.exp w :=
      lt_of_le_of_lt (le_add_of_nonneg_right (Arithmetic.zero_le _)) hlt
    have hg : g m < Exp.exp w :=
      lt_of_le_of_lt (le_add_of_nonneg_left (Arithmetic.zero_le _)) hlt
    have hY := blocks_succ hYh (by rw [hh m hm']; exact hlt)
    refine ⟨_, _, blocks_succ hYf hf, blocks_succ hYg hg, ?_⟩
    rw [hh m hm'] at hY
    convert hY using 1
    ring

/-- `Σ 2^{wj}(f j + g j) = Σ 2^{wj} f j + Σ 2^{wj} g j` when every `f j + g j < 2^w`. -/
theorem bsum_add {n : V} (hfg : ∀ j < n, f j + g j < Exp.exp w) (hh : ∀ j < n, h j = f j + g j) :
    bsum w h n = bsum w f n + bsum w g n := by
  have hf : ∀ j < n, f j < Exp.exp w := fun j hj =>
    lt_of_le_of_lt (le_add_of_nonneg_right (Arithmetic.zero_le _)) (hfg j hj)
  have hg : ∀ j < n, g j < Exp.exp w := fun j hj =>
    lt_of_le_of_lt (le_add_of_nonneg_left (Arithmetic.zero_le _)) (hfg j hj)
  have hh' : ∀ j < n, h j < Exp.exp w := fun j hj => by rw [hh j hj]; exact hfg j hj
  obtain ⟨Yf, Yg, hYf, hYg, hYh⟩ := blocks_add hfg hh n le_rfl
  rw [bsum_unique hh' hYh, bsum_unique hf hYf, bsum_unique hg hYg]

/-- A scalar multiple split blockwise as `K·f j = lo j + 2^w·hi j`. -/
theorem bsum_mul_split (K : V) {lo hi : V → V} [𝚺₁-Function₁ lo] [𝚺₁-Function₁ hi] {n : V}
    (hf : ∀ j < n, f j < Exp.exp w) (hlo : ∀ j < n, lo j < Exp.exp w)
    (hhi : ∀ j < n, hi j < Exp.exp w) (hs : ∀ j < n, K * f j = lo j + Exp.exp w * hi j) :
    K * bsum w f n = bsum w lo n + Exp.exp w * bsum w hi n := by
  have key : ∀ m, m ≤ n → ∃ X L H, Blocks w f m X ∧ Blocks w lo m L ∧ Blocks w hi m H ∧
      K * X = L + Exp.exp w * H := by
    intro m
    induction m using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      intro _; exact ⟨0, 0, 0, blocks_zero w f, blocks_zero w lo, blocks_zero w hi, by simp⟩
    case succ m ih =>
      intro hm
      have hm' : m < n := lt_of_lt_of_le (lt_add_one m) hm
      obtain ⟨X, L, H, hX, hL, hH, e⟩ := ih hm'.le
      refine ⟨_, _, _, blocks_succ hX (hf m hm'), blocks_succ hL (hlo m hm'),
        blocks_succ hH (hhi m hm'), ?_⟩
      calc K * (X + f m * Exp.exp (w * m)) = K * X + (K * f m) * Exp.exp (w * m) := by ring
        _ = (L + Exp.exp w * H) + (lo m + Exp.exp w * hi m) * Exp.exp (w * m) := by
          rw [e, hs m hm']
        _ = _ := by ring
  obtain ⟨X, L, H, hX, hL, hH, e⟩ := key n le_rfl
  rw [bsum_unique hf hX, bsum_unique hlo hL, bsum_unique hhi hH, e]

end linear

/-! ## Bits of a concatenation and blockwise `NoCarry` -/

theorem fbit_concat_low (m a A r : V) (hA : A < Exp.exp m) (hr : r < m) :
    fbit (a * Exp.exp m + A) r = fbit A r := by
  have h := fbit_dig m (a * Exp.exp m + A) 0 r hr
  rw [mul_zero, zero_add, dig_zero_index, mod_mul_add _ _ (exp_pos m), mod_eq_self_of_lt hA] at h
  exact h.symm

theorem fbit_concat_high (m a A r : V) (hA : A < Exp.exp m) (hr : m ≤ r) :
    fbit (a * Exp.exp m + A) r = fbit a (r - m) := by
  conv_lhs => rw [show r = m + (r - m) from (add_tsub_cancel_of_le hr).symm]
  rw [← fbit_div_exp, div_mul_add _ _ hA]

theorem noCarry_concat {m a b A B : V} (hA : A < Exp.exp m) (hB : B < Exp.exp m)
    (hl : NoCarry A B) (hh : NoCarry a b) :
    NoCarry (a * Exp.exp m + A) (b * Exp.exp m + B) := by
  rw [noCarry_iff] at hl hh ⊢
  intro r
  by_cases hr : r < m
  · rw [fbit_concat_low _ _ _ _ hA hr, fbit_concat_low _ _ _ _ hB hr]; exact hl r
  · have e : r = m + (r - m) := (add_tsub_cancel_of_le (not_lt.mp hr)).symm
    rw [e, ← fbit_div_exp, ← fbit_div_exp, div_mul_add _ _ hA, div_mul_add _ _ hB]
    exact hh _

theorem bsum_noCarry {w : V} {f g : V → V} [𝚺₁-Function₁ f] [𝚺₁-Function₁ g] {n : V}
    (hf : ∀ j < n, f j < Exp.exp w) (hg : ∀ j < n, g j < Exp.exp w)
    (h : ∀ j < n, NoCarry (f j) (g j)) : NoCarry (bsum w f n) (bsum w g n) := by
  have key : ∀ m, m ≤ n → ∃ Yf Yg, Blocks w f m Yf ∧ Blocks w g m Yg ∧ NoCarry Yf Yg := by
    intro m
    induction m using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      intro _
      exact ⟨0, 0, blocks_zero w f, blocks_zero w g, by rw [noCarry_iff]; intro i; simp⟩
    case succ m ih =>
      intro hm
      have hm' : m < n := lt_of_lt_of_le (lt_add_one m) hm
      obtain ⟨Yf, Yg, hYf, hYg, hc⟩ := ih hm'.le
      refine ⟨_, _, blocks_succ hYf (hf m hm'), blocks_succ hYg (hg m hm'), ?_⟩
      rw [add_comm Yf, add_comm Yg]
      exact noCarry_concat hYf.1 hYg.1 hc (h m hm')
  obtain ⟨Yf, Yg, hYf, hYg, hc⟩ := key n le_rfl
  rw [bsum_unique hf hYf, bsum_unique hg hYg]; exact hc

/-! ## Cyclic re-indexing -/

/-- Re-indexing by `j ↦ j - e (mod n)` is the rotation of the block sum. -/
theorem bsum_cyc {w : V} {f : V → V} [𝚺₁-Function₁ f] {n e : V} (he : e < n)
    (hf : ∀ j < n, f j < Exp.exp w) :
    bsum w (fun j => f (cyc n j e)) n = rot w n (bsum w f n) e := by
  have hn : 0 < n := lt_of_le_of_lt (Arithmetic.zero_le e) he
  haveI : 𝚺₁-Function₁ (fun j => f (cyc n j e)) := by definability
  have hf' : ∀ j < n, f (cyc n j e) < Exp.exp w := fun j _ => hf _ (cyc_lt hn j e)
  apply bsum_unique hf'
  refine ⟨rot_lt w n _ e he.le (bsum_lt hf), fun j hj => ?_⟩
  rw [dig_rot w n _ e j he hj (bsum_lt hf), dig_bsum hf (cyc_lt hn j e)]

/-- **Cyclic shift congruence**: `2^{we}·Σ 2^{wj} f j ≡ Σ 2^{wj} f (j-e mod n)`
modulo `2^{wn}-1`. -/
theorem bsum_cyc_mod {w : V} {f : V → V} [𝚺₁-Function₁ f] {n e : V} (he : e < n)
    (hf : ∀ j < n, f j < Exp.exp w) (hM : 0 < Exp.exp (w * n) - 1) :
    (Exp.exp (w * e) * bsum w f n) % (Exp.exp (w * n) - 1) =
      bsum w (fun j => f (cyc n j e)) n % (Exp.exp (w * n) - 1) := by
  rw [bsum_cyc he hf]
  exact rot_mod w n _ e he.le hM

/-! ## Constant families and the origin block -/

theorem blocks_const_rep (w c : V) (hc : c < Exp.exp w) (m : V) :
    Blocks w (fun _ => c) m (c * rep w m) := by
  haveI : 𝚺₁-Function₁ (fun _ : V => c) := by definability
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using blocks_zero w (fun _ => c)
  case succ m ih =>
    have := blocks_succ ih hc
    rw [rep_succ_add, mul_add]
    exact this

theorem bsum_const_rep {w c : V} (hc : c < Exp.exp w) (n : V) :
    bsum w (fun _ => c) n = c * rep w n :=
  haveI : 𝚺₁-Function₁ (fun _ : V => c) := by definability
  bsum_unique (fun _ _ => hc) (blocks_const_rep w c hc n)

theorem one_sub_succ (i : V) : (1 : V) - (i + 1) = 0 :=
  tsub_eq_zero_of_le (le_add_of_nonneg_left (Arithmetic.zero_le i))

/-- Adding `c` to block `0` only (`1 - j` is the indicator of `j = 0`). -/
theorem bsum_add_origin {w : V} {f : V → V} [𝚺₁-Function₁ f] {n c : V} (hn : 0 < n)
    (hf : ∀ j < n, f j < Exp.exp w) (h0 : f 0 + c < Exp.exp w) :
    bsum w (fun j => f j + c * (1 - j)) n = bsum w f n + c := by
  haveI : 𝚺₁-Function₁ (fun j : V => c * (1 - j)) := by definability
  haveI : 𝚺₁-Function₁ (fun j => f j + c * (1 - j)) := by definability
  have hc : c < Exp.exp w := lt_of_le_of_lt (le_add_of_nonneg_left (Arithmetic.zero_le _)) h0
  have hsum : ∀ j < n, f j + c * (1 - j) < Exp.exp w := by
    intro j hj
    rcases zero_or_succ j with rfl | ⟨i, rfl⟩
    · simpa using h0
    · simpa [one_sub_succ] using hf _ hj
  have hc' : c < Exp.exp (w * n) := by
    apply lt_of_lt_of_le hc
    apply exp_monotone_le.mpr
    simpa using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hn) (Arithmetic.zero_le w)
  have hblock : Blocks w (fun j => c * (1 - j)) n c := by
    refine ⟨hc', fun j hj => ?_⟩
    rcases zero_or_succ j with rfl | ⟨i, rfl⟩
    · simp [mod_eq_self_of_lt hc]
    · have h := dig_succ_pos w 0 c (i + 1) hc (by simp)
      simpa [dig, one_sub_succ] using h
  have hconst : bsum w (fun j => c * (1 - j)) n = c :=
    bsum_unique (fun j hj => by simpa only [hblock.2 j hj] using dig_lt w c j) hblock
  rw [bsum_add hsum (fun _ _ => rfl), hconst]

/-- Subtracting `c ≤ f 0` from block `0` only. -/
theorem bsum_sub_origin {w : V} {f : V → V} [𝚺₁-Function₁ f] {n c : V} (hn : 0 < n)
    (hf : ∀ j < n, f j < Exp.exp w) (h0 : c ≤ f 0) :
    bsum w (fun j => f j - c * (1 - j)) n = bsum w f n - c := by
  haveI : 𝚺₁-Function₁ (fun j => f j - c * (1 - j)) := by definability
  haveI : 𝚺₁-Function₁ (fun j => f j - c * (1 - j) + c * (1 - j)) := by definability
  have hg : ∀ j < n, f j - c * (1 - j) < Exp.exp w := fun j hj =>
    lt_of_le_of_lt tsub_le_self (hf j hj)
  have hfun : ∀ j < n, f j - c * (1 - j) + c * (1 - j) = f j := by
    intro j _
    rcases zero_or_succ j with rfl | ⟨i, rfl⟩
    · simp [tsub_add_cancel_of_le h0]
    · simp [one_sub_succ]
  have e := bsum_add_origin (f := fun j => f j - c * (1 - j)) (c := c) hn hg
    (by have := hfun 0 hn; simp only [tsub_zero, mul_one] at this ⊢; rw [this]; exact hf 0 hn)
  have e2 : bsum w (fun j => f j - c * (1 - j) + c * (1 - j)) n = bsum w f n := by
    have hb := bsum_blocks (f := fun j => f j - c * (1 - j) + c * (1 - j)) (n := n)
      (fun j hj => by rw [hfun j hj]; exact hf j hj)
    exact (bsum_unique hf ⟨hb.1, fun j hj => by rw [hb.2 j hj]; exact hfun j hj⟩).symm
  rw [e2] at e
  rw [e, add_tsub_cancel_right]

end DiophantineConsistency.ArithmeticPackingBlocks
