import DiophantineConsistency.ArithmeticWindowInterface
import DiophantineConsistency.Adm942.Adm942CarrierRadix
import DiophantineConsistency.Adm942.Adm942MaskConstants

/-! # The internal arithmetic window at the admissible942 ports

The counterpart of `ArithmeticWindowInterface` (soundness spec §3 Stage A,
§4 interface; `PROOF.md` §4 and §6). In every model of IΣ1, a positive zero of
the literal Carrier65 expression at the admissible942 ports whose rank has
population at least `3u+2` (`u = 189269·N`, supplied by `Adm942HalfBinomial`)
yields the window: Boolean radix-`2^47` digits `c_k = dig 47 C k` of
`C = q-F-α` with origin 1 and the support `Es`, explicit end-around carries
`κ_k ≤ 57`, the digits `d_k = dig 47 F k`, the cyclic carry equation against the
raw column of the fixed 1955-term kernel plus the temporal rotation by
`W = R - u`, and the high-mask tests.

The carry bound 57 is the 2011 one: the coefficient mass `7659829036801887` is
the same (`Adm942Kernel.coefficient_mass`). The cyclic length is `4027·N`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Adm942WindowInterface
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
  ArithmeticCyclicWord ArithmeticWindowCarry ArithmeticWindowBits
  Adm942MaskConstants Adm942CarrierRadix
open ArithmeticCarrierSoundness2011 (Equations)
open ArithmeticMaskConstants (cast_exp)
attribute [local irreducible] Adm942Kernel.K Adm942MaskData.beta
  Adm942MaskData.lowPort Adm942MaskData.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Terms of the raw column: the 1955 kernel terms and the temporal rotation. -/
abbrev Index := Option Adm942Kernel.Term

/-- Coefficients: the kernel coefficients, and `2^{W mod 47}` for the rotation. -/
def coeff (W : V) : Index → V
  | none => Exp.exp (W % 47)
  | some t => (Adm942Kernel.coefficient t : V)

/-- Radix exponents: the kernel exponents, and `⌊W/47⌋` for the rotation. -/
def shift (W : V) : Index → V
  | none => W / 47
  | some t => (Adm942Kernel.exponent t : V)

/-- The rotated copies of `C`, one per term. -/
def word (N W C : V) (i : Index) : V := rot 47 (4027*N) C (shift W i % (4027*N))

/-- The raw column at position `k` (spec §4). -/
def rawDigit (N W C k : V) : V :=
  (∑ t : Adm942Kernel.Term, (Adm942Kernel.coefficient t : V) *
      dig 47 C (cyc (4027*N) k (Adm942Kernel.exponent t))) +
    Exp.exp (W % 47) * dig 47 C (cyc (4027*N) k (W / 47))

/-- The explicit end-around carry out of position `k`. -/
def carryDigit (N W C k : V) : V := carry 47 (4027*N) (coeff W) (word N W C) k

/-- **The window interface** (W1)–(W7) of spec §4, on the cyclic length `n = 4027·N`.
Here `HP = MF_native = highPort`; its standard digits are `highDigits`
(`Adm942MaskConstants.highPort_digit`). -/
structure Window (N W C F : V) : Prop where
  N_pos : 0 < N
  boolean : ∀ k < 4027*N, dig 47 C k ≤ 1
  origin : dig 47 C 0 = 1
  support : ∀ k < 4027*N, ¬ inS (k % 4027) → dig 47 C k = 0
  carry_bound : ∀ k < 4027*N, carryDigit N W C k ≤ 57
  digit_bound : ∀ k < 4027*N, dig 47 F k < Exp.exp 47
  carry_recurrence : ∀ k < 4027*N, carryDigit N W C k =
    (rawDigit N W C k + carryDigit N W C (cyc (4027*N) k 1)) / Exp.exp 47
  carry_equation : ∀ k < 4027*N, rawDigit N W C k + carryDigit N W C (cyc (4027*N) k 1) =
    dig 47 F k + Exp.exp 47 * carryDigit N W C k
  mask_origin : NoCarry (dig 47 F 0) (dig 47 (Adm942MaskData.highPort:V) 0 - 1)
  mask_tests : ∀ k < 4027*N, 0 < k →
    NoCarry (dig 47 F k) (dig 47 (Adm942MaskData.highPort:V) (k % 4027))

private theorem raw_eq {N W C : V} (hn : 0 < 4027*N) (hC : C < Exp.exp (47*(4027*N)))
    {k : V} (hk : k < 4027*N) :
    raw 47 (coeff W) (word N W C) k = rawDigit N W C k := by
  have hd : ∀ e : V, dig 47 (rot 47 (4027*N) C (e % (4027*N))) k = dig 47 C (cyc (4027*N) k e) :=
    fun e => by rw [dig_rot 47 _ C _ k (mod_lt e hn) hk hC, cyc_mod _ _ _ hn]
  unfold raw rawDigit
  rw [Fintype.sum_option, add_comm]
  simp only [coeff, word, shift, hd]

private theorem mass_bound (W : V) :
    (∑ i, coeff W i) + 1 ≤ (57+1) * (Exp.exp (47:V) - 1) := by
  rw [Fintype.sum_option]
  simp only [coeff]
  rw [kernel_mass]
  have h47 : W % 47 ≤ 46 := lt_succ_iff_le.mp (by
    simpa only [show (46 : V) + 1 = 47 by norm_num] using mod_lt W (show (0 : V) < 47 by norm_num))
  have hE46 : Exp.exp (46:V) = ((2^46:ℕ):V) := by
    have := cast_exp (V:=V) 46
    rwa [Nat.cast_ofNat] at this
  have hE47 : Exp.exp (47:V) = ((2^47:ℕ):V) := by
    have := cast_exp (V:=V) 47
    rwa [Nat.cast_ofNat] at this
  have hφ : Exp.exp (W % 47) ≤ ((2^46:ℕ):V) := by
    rw [← hE46]; exact exp_monotone_le.mpr h47
  have hcast : ((58 * (2^47 - 1) : ℕ) : V) = (57+1) * (((2^47:ℕ):V) - 1) := by
    have h1 : ((2^47 - 1 : ℕ) : V) + 1 = ((2^47 : ℕ) : V) := by
      have := Nat.sub_add_cancel (Nat.one_le_two_pow (n := 47))
      exact_mod_cast this
    rw [← h1, add_tsub_cancel_right, Nat.cast_mul]
    norm_num
  have hnat : ((2^46 + 7659829036801887 + 1 : ℕ) : V) ≤ ((58 * (2^47 - 1) : ℕ) : V) :=
    Nat.cast_le.mpr (by norm_num)
  rw [hE47]
  calc Exp.exp (W % 47) + 7659829036801887 + 1
      ≤ ((2^46:ℕ):V) + 7659829036801887 + 1 :=
        (add_le_add_iff_right 1).mpr ((add_le_add_iff_right _).mpr hφ)
    _ = ((2^46 + 7659829036801887 + 1 : ℕ) : V) := by push_cast; ring
    _ ≤ _ := hnat
    _ = _ := hcast

/-- **The internal arithmetic window**, from the five internal equations and the radix,
given the population lower bound of the rank as a hypothesis. -/
theorem window_of_equations (u : Fin 14 → V) (hu : ∀ j, 0 < u j)
    (he : Equations (Adm942MaskData.beta:V) (Adm942Kernel.K:V)
      (Adm942MaskData.lowPort:V) ((Adm942MaskData.highPort+Adm942MaskData.beta:ℕ):V) u)
    (hr : Radix u)
    (hσ : ∀ N : V, q u = Exp.exp (189269*N) → 3*(189269*N) + 2 ≤ population (rank u)) :
    ∃ N : V, q u = Exp.exp (189269*N) ∧
      Window N (rank u - 189269*N) (q u - u 1 - u 2) (u 1) := by
  obtain ⟨L, hL, hq, -, hw8, -, -⟩ := hr
  obtain ⟨ht, -, -, -, -⟩ := he
  obtain ⟨hb, hl, hh⟩ := Adm942Ports.current_bounds (V:=V)
  have hwid : (Adm942MaskData.width:V) = 189269 := (current_width (V:=V)).1
  rw [hwid] at hq hw8
  refine ⟨L, hq, ?_⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = rank u - 189269*L := ⟨_, rfl⟩
  rw [← hWdef] at hw8 ⊢
  have ht' : ((Adm942Kernel.K:V) + u 8) * q u + q u = ((Adm942Kernel.K:V) + u 8) * (u 1 + u 2) + u 1 + u 3 * (q u - 1) + 1 := ht
  have hβ1 : 1 ≤ (Adm942MaskData.beta:V) := le_trans (by norm_num) hb
  have hq2 : 2 ≤ q u := by
    show 2 ≤ (Adm942MaskData.beta:V) * u 0 + 1
    have := one_le_mul_of_one_le_of_one_le hβ1 (pos_iff_one_le.mp (hu 0))
    calc (2:V) = 1 + 1 := by norm_num
      _ ≤ _ := (add_le_add_iff_right 1).mpr this
  have hgap := (ArithmeticPellFirstIndex.scalar_window (q u) (Adm942MaskData.beta:V) (Adm942Kernel.K:V) (Adm942MaskData.lowPort:V)
      ((Adm942MaskData.highPort+Adm942MaskData.beta:ℕ):V)
      (u 0) (u 1) (u 2) (u 3) (u 8) (u 7) (lt_of_lt_of_le (by norm_num) hb) (hu 0) (hu 1)
      (hu 2) (hu 3) (hu 8) (hu 7) hl hh rfl ht').1
  have hlt : u 1 + u 2 < q u := tsub_pos_iff_lt.mp (by simpa only [tsub_tsub] using hgap)
  have hfour := ArithmeticSaturation.four_block (q u) (Adm942MaskData.beta:V) (u 0) (u 1) (u 2)
    (Adm942MaskData.lowPort:V) (Adm942MaskData.highPort:V) rfl hgap (one_le_mul_of_one_le_of_one_le
      (pos_iff_one_le.mp highPort_pos)
      (pos_iff_one_le.mp (hu 0)))
  obtain ⟨C, hCdef⟩ : ∃ C, C = q u - u 1 - u 2 := ⟨_, rfl⟩
  rw [← hCdef]
  rw [← hCdef] at hgap hfour
  have hsum : u 1 + u 2 + C = q u := by
    rw [hCdef, tsub_tsub]; exact add_tsub_cancel_of_le (le_of_lt hlt)
  have hC1 : 1 ≤ C := pos_iff_one_le.mp hgap
  have hn : (0:V) < 4027*L := mul_pos (by norm_num) hL
  have hqP : q u = Exp.exp (47*(4027*L)) := by rw [hq]; congr 1; ring
  have hM : (0:V) < Exp.exp (47*(4027*L)) - 1 := by
    rw [← hqP]; exact tsub_pos_of_lt (lt_of_lt_of_le one_lt_two hq2)
  have hCq : C < q u :=
    lt_of_lt_of_le (lt_add_of_pos_left C (add_pos (hu 1) (hu 2))) (le_of_eq hsum)
  have hCP : C < Exp.exp (47*(4027*L)) := by rw [← hqP]; exact hCq
  have hFM : u 1 < q u - 1 := by
    apply lt_iff_succ_le.mpr
    apply le_tsub_of_add_le_right
    calc u 1 + 1 + 1 ≤ u 1 + u 2 + C :=
          add_le_add ((add_le_add_iff_left _).mpr (pos_iff_one_le.mp (hu 2))) hC1
      _ = q u := hsum
  -- the repunit
  have hβ : (Adm942MaskData.beta:V) = Exp.exp (47*4027) - 1 := by
    rw [current_beta_exp, hwid]; norm_num
  have hJ : u 0 = rep (47*4027) L := by
    apply eq_rep_of_identity (by norm_num)
    rw [← hβ]
    calc (Adm942MaskData.beta:V) * u 0 + 1 = q u := rfl
      _ = Exp.exp (47*4027*L) := by rw [hq]; congr 1; norm_num
  -- the four-block rank and saturation
  have hrank : rank u = C - 1 + ((Adm942MaskData.lowPort:V) * u 0 + 1) + Exp.exp (189269*L) * (u 1 + ((Adm942MaskData.highPort:V) * u 0 - 1)) +
      Exp.exp (189269*L) ^ 2 * (Exp.exp (189269*L) - 1 - (C - 1)) +
        Exp.exp (189269*L) ^ 3 * (Exp.exp (189269*L) - 1 - u 1) := by
    rw [← hq, ← hfour, rank, Nat.cast_add]
  have hMH : population ((Adm942MaskData.lowPort:V) * u 0 + 1) + population ((Adm942MaskData.highPort:V) * u 0 - 1) ≤ 189269*L + 2 := by
    rw [hJ, ArithmeticMaskPopulation.repeated_mask_population (47*4027) L (Adm942MaskData.lowPort:V) (Adm942MaskData.highPort:V) (by norm_num) hL
      lowPort_lt_exp highPort_lt_exp lowPort_even highPort_mod_eight
      (by rw [ports_population]; norm_num)]
    norm_num
  obtain ⟨hncC, hncF⟩ := ArithmeticSaturation.saturation (189269*L) (C - 1) (u 1)
    ((Adm942MaskData.lowPort:V) * u 0 + 1) ((Adm942MaskData.highPort:V) * u 0 - 1) (rank u)
    (lt_of_le_of_lt tsub_le_self (by rw [← hq]; exact hCq))
    (by rw [← hq]; exact lt_of_lt_of_le hFM tsub_le_self)
    hrank hMH (hσ L hq)
  rw [hJ] at hncC hncF
  -- the two mask tests
  have low := low_mask_decode 47 4027 L C (Adm942MaskData.lowPort:V) inS (by norm_num) (by norm_num) hL lowPort_lt_exp
    lowPort_digit_in lowPort_digit_out inS_zero hC1 hncC
  have hmask := high_mask_digits 47 4027 L (u 1) (Adm942MaskData.highPort:V) (by norm_num) hL highPort_lt_exp
    (by rw [highPort_digit_zero]; norm_num) hncF
  -- transport and the cyclic word identity
  obtain ⟨z, hz⟩ : ∃ z, u 3 = z + 1 :=
    ⟨u 3 - 1, (tsub_add_cancel_of_le (pos_iff_one_le.mp (hu 3))).symm⟩
  have hQ : q u - 1 + 1 = q u := tsub_add_cancel_of_le (le_trans (by norm_num) hq2)
  have htrans : ((Adm942Kernel.K:V) + u 8) * C = u 1 + z * (q u - 1) := by
    have h1 : ((Adm942Kernel.K:V) + u 8) * (u 1 + u 2) + (((Adm942Kernel.K:V) + u 8) * C + (q u - 1) + 1) =
        ((Adm942Kernel.K:V) + u 8) * (u 1 + u 2) + (u 1 + z * (q u - 1) + (q u - 1) + 1) := by
      calc _ = ((Adm942Kernel.K:V) + u 8) * (u 1 + u 2 + C) + (q u - 1 + 1) := by ring
        _ = ((Adm942Kernel.K:V) + u 8) * q u + q u := by rw [hsum, hQ]
        _ = ((Adm942Kernel.K:V) + u 8) * (u 1 + u 2) + u 1 + u 3 * (q u - 1) + 1 := ht'
        _ = _ := by rw [hz]; ring
    exact add_right_cancel (add_right_cancel (add_left_cancel h1))
  have hKsum : (Adm942Kernel.K:V) + u 8 = ∑ i, coeff W i * Exp.exp (47 * shift W i) := by
    rw [Fintype.sum_option, kernel_sum, hw8]
    simp only [coeff, shift]
    have hW : Exp.exp W = Exp.exp (W % 47) * Exp.exp (47 * (W / 47)) := by
      conv_lhs => rw [← div_add_mod W 47]
      rw [exp_add, mul_comm]
    rw [hW, add_comm]
  have hcongr : (∑ i, coeff W i * word L W C i) % (Exp.exp (47*(4027*L)) - 1) =
      u 1 % (Exp.exp (47*(4027*L)) - 1) := by
    have h := kernel_rotation_congr 47 (4027*L) C (coeff W) (shift W) hn hM
    rw [← hKsum, htrans, hqP, mod_add_mul _ _ hM] at h
    exact h.symm
  have hin : CarryInput 47 (4027*L) (u 1) 57 (coeff W) (word L W C) :=
    { n_pos := hn
      M_pos := hM
      word_lt := fun i => rot_lt 47 _ C _ (le_of_lt (mod_lt _ hn)) hCP
      boolean := fun i => rot_boolean 47 _ C _ (mod_lt _ hn) hCP low.boolean
      F_lt := by rw [← hqP]; exact hFM
      congr := hcongr
      mass := mass_bound W }
  have hcar := end_around_carry hin
  refine ⟨hL, low.boolean, low.origin, low.support, fun k hk => (hcar k hk).1,
    fun k hk => (hcar k hk).2.1, fun k hk => ?_, fun k hk => ?_, hmask.1, hmask.2⟩
  · have h := (hcar k hk).2.2.2
    rw [raw_eq hn hCP hk] at h
    exact h
  · have h := (hcar k hk).2.2.1
    rw [raw_eq hn hCP hk] at h
    exact h

/-- **The internal window of a positive zero of the literal natural polynomial**
(the maintained single positive shift), given the population lower bound. -/
theorem natural_zero_window (v : Fin 14 → V)
    (hz : Adm942Ports.naturalExpression.splitNatural.1.evalSemiring v =
      Adm942Ports.naturalExpression.splitNatural.2.evalSemiring v)
    (hσ : ∀ N : V, q (fun j => v j + 1) = Exp.exp (189269*N) →
      3*(189269*N) + 2 ≤ population (rank (fun j => v j + 1))) :
    ∃ N : V, q (fun j => v j + 1) = Exp.exp (189269*N) ∧
      Window N (rank (fun j => v j + 1) - 189269*N)
        (q (fun j => v j + 1) - (v 1 + 1) - (v 2 + 1)) (v 1 + 1) :=
  window_of_equations _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    (Adm942Ports.current_natural_equations v hz) (current_natural_radix v hz).2 hσ

end Adm942WindowInterface

#print axioms Adm942WindowInterface.window_of_equations
#print axioms Adm942WindowInterface.natural_zero_window
