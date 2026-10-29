import DiophantineConsistency.ArithmeticStandardCasts
import DiophantineConsistency.ArithmeticModularCancellation
import DiophantineConsistency.ArithmeticCyclicWord
import DiophantineConsistency.ArithmeticCellLabels

/-! **S9 — the cast transfer of per-cell facts** (soundness spec §0), in every model
`V` of IΣ1.

Values of `V` below a standard bound are numerals, and `Nat.cast` commutes with
`+ * / %`, powers of two, `fbit` and `NoCarry`. Using these, `snapshot` turns the
window equations at one cell base `b` (a hypothesis `CellInput`, which is the
window interface (W1)–(W7) of `ArithmeticWindowInterface.Window`, spelled with an
explicit carry function) into a standard ℕ snapshot satisfying
`ArithmeticCellLocal.Local`, together with the identifications of every snapshot
entry with the internal digit, carry, temporal bit and phase it came from. The
finite decoding theorems of `ArithmeticCellLocal`/`ArithmeticCellLabels` then hold
of the internal data.

The cyclic index arithmetic needed (all of it global, proved by IΣ1-free algebra
on `%`) is the characterization `cyc_unique` of `cyc n k e` as the unique residue
`r < n` with `r + e ≡ k (mod n)`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticCellTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Casts of standard numerals -/

theorem natCast_exp (n : ℕ) : Exp.exp (n:V) = ((2^n : ℕ) : V) := by
  exact ArithmeticStandardCasts.cast_exp n

theorem natCast_mod (a b : ℕ) : ((a % b : ℕ) : V) = (a:V) % (b:V) := by
  exact ArithmeticStandardCasts.cast_mod a b

theorem natCast_div (a b : ℕ) : ((a / b : ℕ) : V) = (a:V) / (b:V) := by
  exact ArithmeticStandardCasts.cast_div a b

/-- The low support `S = [0,951) ∪ [960,986) ∪ {1004}` as an internal Σ0 predicate
(the same predicate as `ArithmeticMaskConstants.inS`). -/
def inSupport (j : V) : Prop := j < 951 ∨ (960 ≤ j ∧ j < 986) ∨ j = 1004

theorem inSupport_cast (j : ℕ) : inSupport (j:V) ↔ j ∈ CurrentMasks2011.lowSupport := by
  rw [CurrentMasks2011.lowSupport_def]
  simp only [inSupport, Finset.mem_union, Finset.mem_range, Finset.mem_Ico, Finset.mem_singleton, or_assoc]
  norm_cast

/-! ### Modular arithmetic -/

theorem mod_add_mod' {n : V} (hn : 0 < n) (x y : V) : (x % n + y) % n = (x + y) % n := by
  rw [mod_add hn, mod_eq_self_of_lt (mod_lt x hn), ← mod_add hn]

theorem mod_mod_of_dvd' {m n : V} (hm : 0 < m) (h : m ∣ n) (a : V) : a % n % m = a % m :=
  ArithmeticModularCancellation.mod_mod_of_dvd hm h a

theorem eq_of_add_mod_eq {n x y e : V} (hx : x < n) (hy : y < n)
    (h : (x + e) % n = (y + e) % n) : x = y := by
  have hn : 0 < n := lt_of_le_of_lt (Arithmetic.zero_le x) hx
  have he := ArithmeticModularCancellation.add_cancel hn h
  simpa only [mod_eq_self_of_lt hx, mod_eq_self_of_lt hy] using he

theorem mod_add_cancel {n a c d : V} (hn : 0 < n) (h : (a + d) % n = (c + d) % n) :
    a % n = c % n := ArithmeticModularCancellation.add_cancel hn h

theorem cyc_add_mod {n : V} (hn : 0 < n) (k e : V) : (cyc n k e + e) % n = k % n := by
  unfold cyc
  rw [mod_add_mod' hn]
  have hle : e % n ≤ k + n := le_trans (le_of_lt (mod_lt e hn)) le_add_self
  have he : k + n - e % n + e = (k + n) + n * (e / n) := by
    calc k + n - e % n + e = k + n - e % n + (n * (e / n) + e % n) := by rw [div_add_mod]
      _ = (k + n - e % n + e % n) + n * (e / n) := by ring
      _ = _ := by rw [tsub_add_cancel_of_le hle]
  rw [he, mod_add_mul' _ _ hn, mod_add_remove_right hn]

theorem cyc_unique {n r k e : V} (hr : r < n) (h : (r + e) % n = k % n) : cyc n k e = r := by
  have hn : 0 < n := lt_of_le_of_lt (Arithmetic.zero_le r) hr
  apply eq_of_add_mod_eq (cyc_lt hn k e) hr
  rw [cyc_add_mod hn, h]

/-- A cell base below `n = 2011·N` leaves room for the whole cell. -/
theorem cell_room {N b : V} (hb : b < 2011 * N) (hb0 : b % 2011 = 0) : b + 2011 ≤ 2011 * N := by
  have hd := div_add_mod b 2011
  rw [hb0, add_zero] at hd
  rw [← hd] at hb ⊢
  have hlt : b / 2011 < N := lt_of_mul_lt_mul_left hb (by simp)
  simpa only [mul_add, mul_one] using
    mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hlt) (Arithmetic.zero_le (2011:V))

/-! ### Window positions of a cell -/

/-- The snapshot position `b - 4022 + p (mod n)`. -/
abbrev win (n b : V) (p : ℕ) : V := cyc n (b + (p:V)) 4022

theorem win_self {n b : V} {q : ℕ} (hq : b + (q:V) < n) : win n b (4022 + q) = b + q := by
  apply cyc_unique hq
  congr 1
  push_cast
  ring

/-- Every kernel source of a cell offset is a snapshot position. -/
theorem source_eq {n b : V} (hn : 0 < n) {h e : ℕ} (he : e ≤ 4022 + h) :
    cyc n (b + (h:V)) (e:V) = win n b (4022 + h - e) := by
  apply cyc_unique (cyc_lt hn _ _)
  apply mod_add_cancel (d := ((4022 + h - e : ℕ) : V)) hn
  have h1 := cyc_add_mod hn (b + ((4022 + h - e : ℕ) : V)) 4022
  have hc : (e:V) + ((4022 + h - e : ℕ) : V) = 4022 + (h:V) := by
    rw [← Nat.cast_add, Nat.add_sub_cancel' he]; push_cast; ring
  calc (cyc n (b + ((4022 + h - e : ℕ) : V)) 4022 + (e:V) + ((4022 + h - e : ℕ) : V)) % n
      = ((cyc n (b + ((4022 + h - e : ℕ) : V)) 4022 + 4022) + (h:V)) % n := by
        rw [add_assoc, hc, add_assoc]
    _ = ((cyc n (b + ((4022 + h - e : ℕ) : V)) 4022 + 4022) % n + (h:V)) % n :=
        (mod_add_mod' hn _ _).symm
    _ = ((b + ((4022 + h - e : ℕ) : V)) % n + (h:V)) % n := by rw [h1]
    _ = (b + (h:V) + ((4022 + h - e : ℕ) : V)) % n := by rw [mod_add_mod' hn, add_right_comm]

theorem win_mod {N b : V} (hN : 0 < N) (hb0 : b % 2011 = 0) (p : ℕ) :
    win (2011 * N) b p % 2011 = ((p % 2011 : ℕ) : V) := by
  have hn : (0:V) < 2011 * N := mul_pos (by norm_num) hN
  have h1 := cyc_add_mod hn (b + (p:V)) 4022
  have h2 := congrArg (· % (2011:V)) h1
  rw [mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _),
    mod_mod_of_dvd' (by norm_num) (dvd_mul_right _ _)] at h2
  rw [mod_add_remove_right_of_dvd (show (2011:V) ∣ 4022 from ⟨2, by norm_num⟩) (by norm_num)] at h2
  have hb : (2011:V) ∣ b := mod_eq_zero_iff_dvd.mp hb0
  rw [mod_add_remove_left_of_dvd hb (by norm_num)] at h2
  show cyc (2011 * N) (b + (p:V)) 4022 % 2011 = _
  rw [h2, natCast_mod]
  simp

/-! ### Casts of bit tests -/

theorem cast_two : ((2:ℕ):V) = 2 := by simp

theorem fbit_cast (a i : ℕ) : fbit (a:V) (i:V) = ((a / 2 ^ i % 2 : ℕ) : V) := by
  rw [fbit_eq_div, natCast_exp, ← natCast_div, ← cast_two, ← natCast_mod]

theorem noCarry_cast {a b : ℕ} (h : NoCarry (a:V) (b:V)) : a &&& b = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit]
  have hv := (noCarry_iff _ _).mp h (i:V)
  rw [fbit_cast, fbit_cast, ← Nat.cast_add] at hv
  have hv' : a / 2 ^ i % 2 + b / 2 ^ i % 2 ≤ 1 := by exact_mod_cast hv
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  by_cases ha : a / 2 ^ i % 2 = 1
  · have : b / 2 ^ i % 2 ≠ 1 := by omega
    simp [this]
  · simp [ha]

theorem std_of_le {x : V} {m : ℕ} (h : x ≤ (m:V)) : ∃ k : ℕ, x = k := by
  exact eq_nat_of_lt_nat (n := m + 1) (by
    have : (m:V) < ((m + 1 : ℕ) : V) := by exact_mod_cast Nat.lt_succ_self m
    exact lt_of_le_of_lt h this)

theorem exponent_le (t : CurrentKernel2011.Term) : CurrentKernel2011.exponent t ≤ 2020 := by
  rcases t with j | e
  · fin_cases j <;> decide
  · simp only [CurrentKernel2011.exponent]; omega

/-! ### The window equations at a cell, and the snapshot -/

/-- The raw column at position `k` (identical to `ArithmeticWindowInterface.rawDigit`). -/
def rawV (n W C k : V) : V :=
  (∑ t : CurrentKernel2011.Term, (CurrentKernel2011.coefficient t : V) *
      dig 47 C (cyc n k (CurrentKernel2011.exponent t))) +
    Exp.exp (W % 47) * dig 47 C (cyc n k (W / 47))

/-- The window interface (W1)–(W7) with an explicit carry function `κ`
(`ArithmeticWindowInterface.Window` with `κ = carryDigit N W C`). -/
structure CellInput (N W C F : V) (κ : V → V) : Prop where
  N_pos : 0 < N
  boolean : ∀ k < 2011*N, dig 47 C k ≤ 1
  origin : dig 47 C 0 = 1
  support : ∀ k < 2011*N, ¬ inSupport (k % 2011) → dig 47 C k = 0
  carry_bound : ∀ k < 2011*N, κ k ≤ 57
  carry_equation : ∀ k < 2011*N,
    rawV (2011*N) W C k + κ (cyc (2011*N) k 1) = dig 47 F k + Exp.exp 47 * κ k
  mask_tests : ∀ k < 2011*N, 0 < k →
    NoCarry (dig 47 F k) (dig 47 (CurrentMasks2011.highPort:V) (k % 2011))
  /-- The standard digits of `highPort` (`ArithmeticMaskConstants.highPort_digit`). -/
  high_digit : ∀ j : ℕ, j < 2011 →
    dig 47 (CurrentMasks2011.highPort:V) (j:V) = ((CurrentMasks2011.highDigits.getD j 0 : ℕ) : V)

/-- **The cell snapshot.** At each cell base the window equations are a standard
`Local` snapshot, every entry of which is identified with its internal source. -/
theorem snapshot {N W C F : V} {κ : V → V} (H : CellInput N W C F κ) {b : V}
    (hb : b < 2011 * N) (hb0 : b % 2011 = 0) :
    ∃ (cw tw kw dw : ℕ → ℕ) (kin φ : ℕ), ArithmeticCellLocal.Local cw tw kw dw kin φ ∧
      (∀ p : ℕ, p < 6033 → dig 47 C (win (2011 * N) b p) = cw p) ∧
      (∀ q : ℕ, q < 2011 → dig 47 C (cyc (2011 * N) (b + q) (W / 47)) = tw q) ∧
      (∀ q : ℕ, q < 2011 → κ (b + q) = kw q) ∧
      (∀ q : ℕ, q < 2011 → dig 47 F (b + q) = dw q) ∧
      W % 47 = φ := by
  have hn : (0:V) < 2011 * N := mul_pos (by norm_num) H.N_pos
  have hroom := cell_room hb hb0
  have hq_lt : ∀ q : ℕ, q < 2011 → b + (q:V) < 2011 * N := fun q hq =>
    lt_of_lt_of_le ((add_lt_add_iff_left b).mpr (by exact_mod_cast hq)) hroom
  have h47 : Exp.exp (47:V) = ((2 ^ 47 : ℕ) : V) := by
    simpa only [Nat.cast_ofNat] using natCast_exp (V:=V) 47
  -- standard values
  have ex_cw : ∀ p : ℕ, ∃ m : ℕ, dig 47 C (win (2011 * N) b p) = m := fun p =>
    std_of_le (m := 1) (by simpa using H.boolean (win (2011 * N) b p) (cyc_lt hn _ _))
  have ex_tw : ∀ q : ℕ, ∃ m : ℕ, dig 47 C (cyc (2011 * N) (b + q) (W / 47)) = m := fun q =>
    std_of_le (m := 1) (by simpa using H.boolean (cyc (2011 * N) (b + q) (W / 47)) (cyc_lt hn _ _))
  have ex_kw : ∀ q : ℕ, ∃ m : ℕ, q < 2011 → κ (b + q) = m := fun q => by
    by_cases hq : q < 2011
    · obtain ⟨m, hm⟩ := std_of_le (m := 57) (by simpa using H.carry_bound _ (hq_lt q hq))
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => absurd h hq⟩
  have ex_dw : ∀ q : ℕ, ∃ m : ℕ, dig 47 F (b + q) = m := fun q =>
    std_of_le (m := 2 ^ 47) (by rw [← h47]; exact le_of_lt (dig_lt 47 F (b + q)))
  choose cw hcw using ex_cw
  choose tw htw using ex_tw
  choose kw hkw using ex_kw
  choose dw hdw using ex_dw
  obtain ⟨kin, hkin⟩ := std_of_le (m := 57) (by simpa using H.carry_bound _ (cyc_lt hn b 1))
  obtain ⟨φ, hφ⟩ := std_of_le (m := 46) (x := W % 47) (by
    have h := mod_lt W (show (0:V) < 47 by norm_num)
    have h' : W % 47 < (46:V) + 1 := by rw [show (46:V) + 1 = 47 by norm_num]; exact h
    simpa using lt_succ_iff_le.mp h')
  have hφ47 : φ < 47 := by
    have h := mod_lt W (show (0:V) < 47 by norm_num)
    rw [hφ] at h
    exact_mod_cast h
  -- the raw column
  have hraw : ∀ q : ℕ, q < 2011 →
      rawV (2011 * N) W C (b + q) = ((ArithmeticCellLocal.raw cw q + 2 ^ φ * tw q : ℕ) : V) := by
    intro q hq
    unfold rawV ArithmeticCellLocal.raw
    rw [hφ, natCast_exp, htw q]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [source_eq hn (h := q) (e := CurrentKernel2011.exponent t)
      (by have := exponent_le t; omega), hcw]
  -- incoming carries
  have hinc0 : κ (cyc (2011 * N) (b + ((0:ℕ):V)) 1) = (kin:V) := by simpa using hkin
  have hinc : ∀ g : ℕ, g + 1 < 2011 →
      κ (cyc (2011 * N) (b + ((g + 1 : ℕ) : V)) 1) = (kw g : V) := by
    intro g hg
    have hc : cyc (2011 * N) (b + ((g + 1 : ℕ) : V)) 1 = b + (g:V) :=
      cyc_unique (hq_lt g (by omega)) (by congr 1; push_cast; ring)
    rw [hc, hkw g (by omega)]
  refine ⟨cw, tw, kw, dw, kin, φ, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hφ47⟩,
    fun p _ => hcw p, fun q _ => htw q, fun q hq => hkw q hq, fun q _ => hdw q, hφ⟩
  · intro p _
    have h := H.boolean _ (cyc_lt hn (b + (p:V)) 4022)
    rw [show cyc (2011 * N) (b + (p:V)) 4022 = win (2011 * N) b p from rfl, hcw] at h
    exact_mod_cast h
  · intro q _
    have h := H.boolean _ (cyc_lt hn (b + (q:V)) (W / 47))
    rw [htw] at h
    exact_mod_cast h
  · intro p _ hp
    have hz := H.support _ (cyc_lt hn (b + (p:V)) 4022) (by
      change ¬ inSupport (win (2011 * N) b p % 2011)
      rw [win_mod H.N_pos hb0, inSupport_cast]
      exact hp)
    rw [show cyc (2011 * N) (b + (p:V)) 4022 = win (2011 * N) b p from rfl, hcw] at hz
    exact_mod_cast hz
  · have h := H.carry_bound _ (cyc_lt hn b 1)
    rw [hkin] at h
    exact_mod_cast h
  · intro q hq
    have h := H.carry_bound _ (hq_lt q hq)
    rw [hkw q hq] at h
    exact_mod_cast h
  · have h := H.carry_equation _ (hq_lt 0 (by omega))
    rw [hraw 0 (by omega), hinc0, hdw, hkw 0 (by omega), h47] at h
    exact_mod_cast h
  · intro g hg
    have h := H.carry_equation _ (hq_lt (g + 1) hg)
    rw [hraw (g + 1) hg, hinc g hg, hdw, hkw (g + 1) hg, h47] at h
    exact_mod_cast h
  · intro q hq1 hq
    have hpos : (0:V) < b + (q:V) :=
      lt_of_lt_of_le (by exact_mod_cast hq1) le_add_self
    have h := H.mask_tests _ (hq_lt q hq) hpos
    have hm : (b + (q:V)) % 2011 = (q:V) := by
      have hb' : (2011:V) ∣ b := mod_eq_zero_iff_dvd.mp hb0
      rw [mod_add_remove_left_of_dvd hb' (by norm_num)]
      exact mod_eq_self_of_lt (by exact_mod_cast hq)
    rw [hm, H.high_digit q hq, hdw] at h
    exact noCarry_cast h

end DiophantineConsistency.ArithmeticCellTransfer
