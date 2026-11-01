import DiophantineConsistency.ArithmeticLocalNormalizationCell

/-! **Cell blocks of a normalized word** (Matrix-free).

For an assembled word on `ZMod (N·2011)` and a normalization with vanishing
carries at both cell boundaries, the radix-`2^47` number formed by the 2011
digits of cell `j` equals the block of raw columns, and that block splits as
`Lo(cell j) + Hi(cell j-1) + Cell(cell j-s)`. Here `Lo`, `Hi` are the two
halves of the kernel product `K·Cell = Lo + B·Hi` (`kernel_split`). The
identities are exact finite-sum identities over `ℕ`. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000

namespace DiophantineConsistency.MF.ArithmeticLocalNormalizationBlock

open DiophantineConsistency.MF.NativeCyclicConvolution DiophantineConsistency.MF.NativeBooleanRotation
  DiophantineConsistency.MF.NativeCyclicRotation
  DiophantineConsistency.MF.CurrentMasks2011 DiophantineConsistency.CurrentMasks2011
  DiophantineConsistency.MF.CurrentCellConstruction2011 DiophantineConsistency.MF.CurrentWordConstruction2011
  DiophantineConsistency.MF.CurrentWordClause2011 DiophantineConsistency.MF.CurrentWordCopies2011
  DiophantineConsistency.MF.CurrentWordTopBounds2011 DiophantineConsistency.WangTiles942
open DiophantineConsistency.CurrentKernel2011 (Term coefficient exponent K rawWord)
open scoped BigOperators

/-! ## Pure finite sums -/

/-- The part of the shifted cell staying in the same cell. -/
def G (x : ℕ) (c : ℕ → ℕ) (e : ℕ) : ℕ := if x ≤ e then c (e - x) else 0
/-- The part of the shifted cell carried into the next cell. -/
def H (x : ℕ) (c : ℕ → ℕ) (e : ℕ) : ℕ := if x ≤ e + 2011 then c (e + 2011 - x) else 0

theorem sum_trunc (c g : ℕ → ℕ) (hc : ∀ f, 1005 ≤ f → c f = 0) (n : ℕ) (hn : 1005 ≤ n) :
    ∑ q ∈ Finset.range n, c q * g q = ∑ q ∈ Finset.range 1005, c q * g q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 1005 + m := ⟨n - 1005, by omega⟩
  rw [Finset.sum_range_add (fun q => c q * g q) 1005 m]
  have h0 : ∑ q ∈ Finset.range m, c (1005 + q) * g (1005 + q) = 0 :=
    Finset.sum_eq_zero fun q _ => by rw [hc _ (by omega), zero_mul]
  rw [h0, add_zero]

theorem shift_split (c : ℕ → ℕ) (hc : ∀ f, 1005 ≤ f → c f = 0) (x : ℕ) (hx : x ≤ 2020) (ρ : ℕ) :
    (∑ f ∈ Finset.range 2011, c f * ρ ^ f) * ρ ^ x =
      ∑ e ∈ Finset.range 2011, G x c e * ρ ^ e +
        ρ ^ 2011 * ∑ e ∈ Finset.range 2011, H x c e * ρ ^ e := by
  have hF : ∑ p ∈ Finset.range (2011 + 2011), G x c p * ρ ^ p =
      ∑ q ∈ Finset.range 1005, c q * ρ ^ (x + q) := by
    obtain ⟨m, hm⟩ : ∃ m, 2011 + 2011 = x + m := ⟨2011 + 2011 - x, by omega⟩
    rw [hm, Finset.sum_range_add (fun p => G x c p * ρ ^ p) x m]
    have h1 : ∑ p ∈ Finset.range x, G x c p * ρ ^ p = 0 :=
      Finset.sum_eq_zero fun p hp => by
        have := Finset.mem_range.mp hp
        simp [G, show ¬ x ≤ p by omega]
    have h2 : ∀ q, G x c (x + q) = c q := fun q => by simp [G]
    simp only [h1, h2, zero_add]
    exact sum_trunc c (fun q => ρ ^ (x + q)) hc m (by omega)
  have hL : (∑ f ∈ Finset.range 2011, c f * ρ ^ f) * ρ ^ x =
      ∑ q ∈ Finset.range 1005, c q * ρ ^ (x + q) := by
    rw [Finset.sum_mul]
    rw [show ∑ i ∈ Finset.range 2011, c i * ρ ^ i * ρ ^ x =
        ∑ i ∈ Finset.range 2011, c i * ρ ^ (x + i) from
      Finset.sum_congr rfl (fun i _ => by ring)]
    exact sum_trunc c (fun q => ρ ^ (x + q)) hc 2011 (by norm_num)
  rw [hL, ← hF, Finset.sum_range_add (fun p => G x c p * ρ ^ p) 2011 2011, Finset.mul_sum,
    Nat.add_left_cancel_iff]
  apply Finset.sum_congr rfl
  intro e _
  have hg : G x c (2011 + e) = H x c e := by
    unfold G H; rw [show 2011 + e = e + 2011 by ring]
  rw [hg, pow_add]; ring

theorem exponent_le (t : Term) : exponent t ≤ 2020 := by
  rcases t with j | e
  · fin_cases j <;> simp [exponent]
  · simp only [exponent]; omega

/-- The low half of the kernel product of a cell. -/
def Lo (c : ℕ → ℕ) : ℕ :=
  ∑ t : Term, coefficient t * ∑ e ∈ Finset.range 2011, G (exponent t) c e * radix ^ e
/-- The high half of the kernel product of a cell. -/
def Hi (c : ℕ → ℕ) : ℕ :=
  ∑ t : Term, coefficient t * ∑ e ∈ Finset.range 2011, H (exponent t) c e * radix ^ e

theorem kernel_split (c : ℕ → ℕ) (hc : ∀ f, 1005 ≤ f → c f = 0) :
    K * ∑ f ∈ Finset.range 2011, c f * radix ^ f = Lo c + radix ^ 2011 * Hi c := by
  unfold K rawWord Lo Hi
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  have h := shift_split c hc (exponent t) (exponent_le t) radix
  calc coefficient t * radix ^ exponent t * ∑ f ∈ Finset.range 2011, c f * radix ^ f
      = coefficient t * ((∑ f ∈ Finset.range 2011, c f * radix ^ f) * radix ^ exponent t) := by ring
    _ = _ := by rw [h]; ring

/-- Radix-`ρ` numbers with small digits are small. -/
theorem digits_sum_lt (d : ℕ → ℕ) (ρ : ℕ) (hd : ∀ e, d e < ρ) (n : ℕ) :
    ∑ e ∈ Finset.range n, d e * ρ ^ e < ρ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 : d n + 1 ≤ ρ := hd n
    calc ∑ e ∈ Finset.range n, d e * ρ ^ e + d n * ρ ^ n
        < ρ ^ n + d n * ρ ^ n := by omega
      _ = (d n + 1) * ρ ^ n := by ring
      _ ≤ ρ * ρ ^ n := Nat.mul_le_mul_right _ h1
      _ = ρ ^ n * ρ := by ring

/-! ## The cell digits -/

/-- The digit `f` of a cell with tile `i`, dummy `d` and marker `u`. -/
def cdig (i : Fin 942) (d u f : ℕ) : ℕ :=
  if f = 977 then d else if f = 1004 then u else localDigit i f

theorem cdig_high (i : Fin 942) (d u f : ℕ) (hf : 1005 ≤ f) : cdig i d u f = 0 := by
  unfold cdig
  rw [if_neg (by omega), if_neg (by omega)]
  apply localDigit_support
  simp only [lowSupport_def, Finset.mem_union, Finset.mem_range, Finset.mem_Ico,
    Finset.mem_singleton]
  omega

variable {N : ℕ} [NeZero N]

/-- The digits of cell `j` of the assembled word. -/
def cellDigits (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ) (j : ZMod N) : ℕ → ℕ :=
  cdig (a j) (dummy j) (marker j)

theorem word_cell (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ) (j : ZMod N) (f : ℕ)
    (hf : f < 2011) :
    word a dummy marker (base j+(f : ZMod (N*2011))) = cellDigits a dummy marker j f := by
  rw [word_at_base a dummy marker j f hf]; rfl

theorem word_shift_split (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ) (j : ZMod N)
    (e x : ℕ) (he : e < 2011) (hx : x ≤ 2020) :
    word a dummy marker (base j+(e : ZMod (N*2011))-(x : ZMod (N*2011))) =
      G x (cellDigits a dummy marker j) e + H x (cellDigits a dummy marker (j-1)) e := by
  by_cases h1 : x ≤ e
  · have hb : base j+(e : ZMod (N*2011))-(x : ZMod (N*2011)) =
        base j+((e - x : ℕ) : ZMod (N*2011)) := by
      rw [Nat.cast_sub h1]; ring
    rw [hb, word_cell a dummy marker j _ (by omega)]
    simp only [G, H, if_pos h1, if_pos (show x ≤ e + 2011 by omega)]
    rw [show cellDigits a dummy marker (j-1) (e + 2011 - x) = 0 from
      cdig_high _ _ _ _ (by omega), add_zero]
  by_cases h2 : x ≤ e + 2011
  · have hb : base j+(e : ZMod (N*2011))-(x : ZMod (N*2011)) =
        base (j-1)+((e + 2011 - x : ℕ) : ZMod (N*2011)) := by
      have hs := base_sub_stride j 1
      simp only [Nat.cast_one, Nat.mul_one] at hs
      rw [hs, Nat.cast_sub h2]; push_cast; ring
    rw [hb, word_cell a dummy marker (j-1) _ (by omega)]
    simp only [G, H, if_neg h1, if_pos h2, zero_add]
  · have hb : base j+(e : ZMod (N*2011))-(x : ZMod (N*2011)) =
        base (j-2)+((e + 4022 - x : ℕ) : ZMod (N*2011)) := by
      have hs := base_sub_stride j 2
      simp only [Nat.cast_ofNat] at hs
      rw [hs, Nat.cast_sub (by omega)]; push_cast; ring
    rw [hb, word_cell a dummy marker (j-2) _ (by omega)]
    simp only [G, H, if_neg h1, if_neg h2, add_zero]
    exact cdig_high _ _ _ _ (by omega)

/-- The convolution block of cell `j`. -/
theorem convolution_block (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ) (j : ZMod N) :
    ∑ e ∈ Finset.range 2011,
      convolution DiophantineConsistency.MF.CurrentKernel2011.folded (word a dummy marker)
        (base j+(e : ZMod (N*2011))) * radix ^ e =
      Lo (cellDigits a dummy marker j) + Hi (cellDigits a dummy marker (j-1)) := by
  simp only [DiophantineConsistency.MF.CurrentKernel2011.convolution_terms]
  unfold Lo Hi
  rw [← Finset.sum_add_distrib]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [word_shift_split a dummy marker j e (exponent t) (Finset.mem_range.mp he) (exponent_le t)]
  ring

/-- The rotation block of cell `j` is the whole cell `j - s`. -/
theorem rotation_block (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (j : ZMod N) :
    ∑ e ∈ Finset.range 2011,
      binaryRotation 47 (displacement s) (word a dummy marker) (base j+(e : ZMod (N*2011))) *
        radix ^ e =
      ∑ e ∈ Finset.range 2011, cellDigits a dummy marker (j-(s : ZMod N)) e * radix ^ e := by
  apply Finset.sum_congr rfl
  intro e he
  rw [rotation_whole a dummy marker hd hm s]
  have hb : base j+(e : ZMod (N*2011))-((2011*s : ℕ) : ZMod (N*2011)) =
      base (j-(s : ZMod N))+(e : ZMod (N*2011)) := by
    rw [base_sub_stride j s]; ring
  rw [hb, word_cell a dummy marker _ e (Finset.mem_range.mp he)]

/-- The raw block of cell `j`. -/
theorem raw_block (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (j : ZMod N) :
    ∑ e ∈ Finset.range 2011,
      CurrentCarryConstruction2011.raw (word a dummy marker) (displacement s)
        (base j+(e : ZMod (N*2011))) * radix ^ e =
      Lo (cellDigits a dummy marker j) + Hi (cellDigits a dummy marker (j-1)) +
        ∑ e ∈ Finset.range 2011, cellDigits a dummy marker (j-(s : ZMod N)) e * radix ^ e := by
  simp only [CurrentCarryConstruction2011.raw, add_mul, Finset.sum_add_distrib]
  rw [convolution_block, rotation_block a dummy marker hd hm s j]

/-- With vanishing boundary carries the digits of cell `j` spell its raw block. -/
theorem digit_block (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (word a dummy marker) (displacement s) k digits)
    (j : ZMod N) :
    ∑ e ∈ Finset.range 2011, digits (base j+(e : ZMod (N*2011))) * radix ^ e =
      ∑ e ∈ Finset.range 2011,
        CurrentCarryConstruction2011.raw (word a dummy marker) (displacement s)
          (base j+(e : ZMod (N*2011))) * radix ^ e := by
  have hin := (top_carry_digits a dummy marker hd hm s k digits hf (j-1)).2.1
  have he : base (j-1)+(2010 : ZMod (N*2011)) = base j-1 := by
    have hb : base (j-1) = base j-2011 := by
      simpa only [Nat.mul_one,Nat.cast_one,Nat.cast_ofNat] using base_sub_stride j 1
    rw [hb]; ring
  rw [he] at hin
  have hout := (top_carry_digits a dummy marker hd hm s k digits hf j).2.1
  have key : ∀ n, n ≤ 2011 →
      ∑ e ∈ Finset.range n,
        CurrentCarryConstruction2011.raw (word a dummy marker) (displacement s)
          (base j+(e : ZMod (N*2011))) * radix ^ e =
      ∑ e ∈ Finset.range n, digits (base j+(e : ZMod (N*2011))) * radix ^ e +
        radix ^ n * k (base j+(n : ZMod (N*2011))-1) := by
    intro n hn
    induction n with
    | zero => simp [hin]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih (by omega)]
      have hdec := hf.decomposition (base j+(n : ZMod (N*2011)))
      have hc : base j+((n+1 : ℕ) : ZMod (N*2011))-1 = base j+(n : ZMod (N*2011)) := by
        push_cast; ring
      rw [hc]
      calc _ = ∑ e ∈ Finset.range n, digits (base j+(e : ZMod (N*2011))) * radix ^ e +
            radix ^ n * (CurrentCarryConstruction2011.raw (word a dummy marker) (displacement s)
              (base j+(n : ZMod (N*2011))) + k (base j+(n : ZMod (N*2011))-1)) := by ring
        _ = _ := by rw [hdec, pow_succ]; ring
  have h := key 2011 le_rfl
  have hc : base j+((2011 : ℕ) : ZMod (N*2011))-1 = base j+2010 := by push_cast; ring
  rw [hc, hout, mul_zero, add_zero] at h
  exact h.symm

end DiophantineConsistency.MF.ArithmeticLocalNormalizationBlock
