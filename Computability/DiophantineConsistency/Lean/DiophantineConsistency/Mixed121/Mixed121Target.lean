import DiophantineConsistency.Mixed121.Mixed121FieldParity
import DiophantineConsistency.Mixed121.Mixed121Uniform

/-! # The clause targets of the constructed word, at 121x8801

The 121x8801 counterpart of Compact44's `CompactWordTargetNoCarry`,
`CompactWordProductColumn`, `CompactMarkedTargetColumn` and
`CompactMarkedTargetHighNoCarry`.

Here the target digit depends on the tile, unlike Compact44's constant
`1 + 2^51`. At a clause target `T ∈ {4393, 5495}`, block `j` of the
constructed word with tile `i₀` has physical digit equal to its selected
band (the other band, the bare part and the temporal term vanish):

    decoderBand = (1 + 2^10·D) + 2^10·D = 2·clause(i₀) − 1,

where `D = Σ_k d_k(i₀)·4^k` is the radix-four sum of the tile's 44 digits.
Its bits sit at `0` and `11 + 2k`, while those of the high-mask digit
`μ = 1022 + Σ_k 2^(10+2k)` sit at `1..9` and `10 + 2k`. So it is carry-free
against `μ`. That is checked once over the 943 rows (`rows_disjoint`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace Mixed121Target
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticStandardCasts ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking
  ArithmeticBinaryCarry CompactHeterogeneousCarry
open CompactMarkedTransport CompactForwardCellInputs CompactWordCellClient CompactGenericAlignedMass
open DiophantineConsistency.ModelDigitTransfer (dsum)
open Mixed121Kernel Mixed121Rotation Mixed121Flatten Mixed121Temporal Mixed121Cell Mixed121Word
  Mixed121Block Mixed121Column

/-- The target value of every tile is disjoint from `μ`. -/
theorem rows_disjoint : Compact943Data.rows.all
    (fun t => (2 * clause t - 1) &&& 105637550019019116791391934462 == 0) = true := by
  decide +kernel

theorem row_disjoint (i : Fin 943) :
    (2 * clause (Compact943Data.row i) - 1) &&& Mixed121Ports.mu = 0 := by
  have hm : Compact943Data.row i ∈ Compact943Data.rows := List.get_mem Compact943Data.rows _
  have h := (List.all_eq_true.mp rows_disjoint) _ hm
  rw [Mixed121Masks.mu_eq]
  simpa using h

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem fbit_cast (a i : ℕ) : fbit (a : V) (i : V) = ((a / 2^i % 2 : ℕ) : V) := by
  rw [fbit_eq_div, cast_exp, ← cast_div]
  exact (cast_mod (a / 2^i) 2).symm

theorem noCarry_cast {a b : ℕ} (h : a &&& b = 0) : NoCarry (a : V) (b : V) := by
  intro i hi
  have hi' : i < ((a + b + 1 : ℕ) : V) := by push_cast; exact hi
  obtain ⟨k, rfl⟩ := eq_nat_of_lt_nat hi'
  rw [fbit_cast, fbit_cast]
  have hk : a / 2^k % 2 + b / 2^k % 2 ≤ 1 := by
    have h1 := Nat.testBit_and a b k
    rw [h, Nat.zero_testBit, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at h1
    rcases Nat.mod_two_eq_zero_or_one (a / 2^k) with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one (b / 2^k) with hb | hb <;> simp_all
  exact_mod_cast hk

/-- A selected standard tile with its own copy digits has band `2·clause − 1`. -/
theorem band_value (n C k : V) (T : ℕ) (i0 : Fin 943)
    (hsel : ∀ i, Mixed121Band.selDigit n C k T i = selector (i0.val : V) i)
    (hcopy : ∀ j < 44, Mixed121Band.copyDigit n C k T j =
      (Mixed121Digits.digit (Compact943Data.row i0) j : V)) :
    Mixed121Single.decoderBand T n C k =
      ((2 * clause (Compact943Data.row i0) - 1 : ℕ) : V) := by
  unfold Mixed121Single.decoderBand
  simp_rw [hsel]
  have hw := selector_weighted (V:=V) i0 (fun i => 1 + Exp.exp 10 * dsum (Exp.exp 2)
    (fun d => (Mixed121Digits.digit (Compact943Data.row i) d : V)) 44)
  have hcomm : (∑ i, selector (i0.val : V) i * (1 + Exp.exp 10 * dsum (Exp.exp 2)
      (fun d => (Mixed121Digits.digit (Compact943Data.row i) d : V)) 44)) =
      ∑ i, (1 + Exp.exp 10 * dsum (Exp.exp 2)
        (fun d => (Mixed121Digits.digit (Compact943Data.row i) d : V)) 44) * selector (i0.val : V) i := by
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hcomm, hw]
  have hd : dsum (Exp.exp 2) (Mixed121Band.copyDigit n C k T) 44 =
      dsum (Exp.exp 2) (fun d => (Mixed121Digits.digit (Compact943Data.row i0) d : V)) 44 := by
    unfold dsum
    apply Finset.sum_congr rfl
    intro d hd
    rw [hcopy d (Finset.mem_range.mp hd)]
  rw [hd]
  have hc1 : 1 ≤ clause (Compact943Data.row i0) := by
    rw [Mixed121Digits.clause_digits]; omega
  have hcast : ((2 * clause (Compact943Data.row i0) - 1 : ℕ) : V) =
      2 * ((clause (Compact943Data.row i0) : ℕ) : V) - 1 := by
    apply eq_tsub_of_add_eq
    have hn : 2 * clause (Compact943Data.row i0) - 1 + 1 = 2 * clause (Compact943Data.row i0) := by omega
    have hv : (((2 * clause (Compact943Data.row i0) - 1 : ℕ)) : V) + 1 =
        ((2 * clause (Compact943Data.row i0) : ℕ) : V) := by exact_mod_cast hn
    rw [hv, Nat.cast_mul, Nat.cast_ofNat]
  rw [hcast, Mixed121Digits.clause_cast]
  set D := dsum (Exp.exp (2:V)) (fun d => (Mixed121Digits.digit (Compact943Data.row i0) d : V)) 44
  have he : 2 * (1 + Exp.exp 10 * D) = (1 + Exp.exp 10 * D + Exp.exp 10 * D) + 1 := by ring
  rw [he, add_tsub_cancel_right]

attribute [local irreducible] paramKernel rho Compact943Data.rows Mixed121Ports.lowNat
  Mixed121Ports.highNat

/-- The physical target digit of a constructed block is its tile's target value. -/
theorem marked_target (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : CompactWord row N s) (hN : 1 < N) (hs : s < N)
    (hbool : ∀ j, dummy j ≤ 1) (j : V) (hj : j < N) (T : ℕ) (hT : T = 4393 ∨ T = 5495) :
    ∃ i0 : Fin 943, row j = (i0.val : V) ∧
      dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) (T:V) =
        ((2 * clause (Compact943Data.row i0) - 1 : ℕ) : V) := by
  obtain ⟨i0, hi0⟩ := standard_row (hw.tile_lt j hj)
  refine ⟨i0, hi0, ?_⟩
  let C : V := packedWord row dummy N
  let n : V := 8801*N
  let k : V := 8801*j+(T:V)
  have hn : 0 < n := mul_pos (by norm_num) hw.pos
  have hTq : (T:V) < 8801 := by exact_mod_cast (show T < 8801 by omega)
  have hidx := Mixed121Copy.index N j (T:V) hj hTq
  have hk : k < n := hidx.1
  have hp : k % 8801 = (T:V) := hidx.2
  have hC : C < Exp.exp (121*n) := by
    simpa only [C, n, mul_assoc] using packedWord_lt row dummy N
  have hzero : ∀ y<8801*N, ¬Mixed121Clean.Bad (y%8801) → dig 121 C y=0 :=
    fun y hy hb => word_outside_bad row dummy hw y hy hb
  have he121 : (121*(8801*s)) % 121 = (0:V) := mod_eq_zero_iff_dvd.mpr ⟨8801*s, rfl⟩
  have hcell : ((121*(8801*s))/121 % (8801*N)) % 8801 = (0:V) := by
    rw [show (121:V)*(8801*s)/121 = 8801*s from div_mul_right _ (by norm_num),
      ArithmeticModularCancellation.mul_mod_mul (by norm_num) hw.pos]
    exact mod_eq_zero_iff_dvd.mpr ⟨s%N, rfl⟩
  have hpp : k%8801=2195 ∨ k%8801=3296 ∨ k%8801=4393 ∨ k%8801=5495 := by
    rw [hp]; rcases hT with rfl | rfl <;> norm_num
  obtain ⟨hpred, hT0⟩ := Mixed121Uniform.target_and_predecessor N C (121*(8801*s)) k hw.pos hk hC
    he121 hcell hzero hpp
  have hT0' : dig 121 (temporalWord (8801*N) (121*(8801*s)) C) k = 0 := by
    apply hT0; rw [hp]; rcases hT with rfl | rfl <;> norm_num
  have he1 : (1 : V) ≤ 121*n := pos_iff_one_le.mp (mul_pos (by norm_num) hn)
  have htwo : (2 : V) ≤ Exp.exp (121*n) := by simpa using exp_monotone_le.mpr he1
  have hM : 0 < Exp.exp (121*n)-1 := tsub_pos_of_lt (lt_of_lt_of_le (by norm_num) htwo)
  have hcap3 : ∀ y < n, dig 121 C y ≤ 3 := fun y hy => le_trans (word_cap row dummy N y hy) (by norm_num)
  have hcarry := temporal_product_carry n (121*(8801*s)) C hn hM hC hcap3
  have hdec : dig 121 (((((paramKernel rho : ℕ) : V) + Exp.exp (121*(8801*s)))*C) % (Exp.exp (121*n)-1)) k =
      Mixed121Single.decoderBand T n C k := by
    rcases hT with rfl | rfl
    · exact Mixed121Uniform.clean_column_at4393 N C _ _ k hw.pos hk hC hzero hp hcarry hT0' hpred
    · exact Mixed121Uniform.clean_column_at5495 N C _ _ k hw.pos hk hC hzero hp hcarry hT0' hpred
  have hphys := (marked_physical_column row dummy hw hN hs hbool j hj (T:V) hTq).2
  have hF := (packed_word_zero_carry row dummy N (8801*s) hw.pos k hk).2
  have hdig : dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) (T:V) =
      Mixed121Single.decoderBand T n C k := by
    rw [hphys, ← hF]; exact hdec
  rw [hdig]
  apply band_value
  · intro i
    unfold Mixed121Band.selDigit
    have hiT : i.val ≤ T := by have := i.isLt; omega
    have hd : (((T - i.val : ℕ)) : V) ≤ (T:V) := by exact_mod_cast (Nat.sub_le T i.val)
    have hsum : (i.val:V)+(((T-i.val):ℕ):V)=(T:V) := by exact_mod_cast (Nat.add_sub_of_le hiT)
    rw [Mixed121Copy.reflected N j _ _ hj hTq hd, (eq_tsub_of_add_eq hsum).symm,
      word_selector row dummy N j hj i]
    simp only [wordSelector, hi0]
  · intro j' hj'
    unfold Mixed121Band.copyDigit
    have hpos : Mixed121Band.extraPosN j' = Mixed121Kernel.extraPos ⟨j', hj'⟩ :=
      (Mixed121Band.extraPos_eq ⟨j', hj'⟩).symm
    have hlt := Mixed121KernelFiniteCert.reflected_range _ (Mixed121KernelFiniteCert.extra_allowed ⟨j', hj'⟩)
    have hle : Mixed121Kernel.extraPos ⟨j', hj'⟩ ≤ T := by omega
    have hd : (((T - Mixed121Kernel.extraPos ⟨j', hj'⟩ : ℕ)) : V) ≤ (T:V) := by
      exact_mod_cast (Nat.sub_le T _)
    have hsum : (Mixed121Kernel.extraPos ⟨j', hj'⟩ : V) +
        (((T - Mixed121Kernel.extraPos ⟨j', hj'⟩) : ℕ) : V) = (T:V) := by
      exact_mod_cast (Nat.add_sub_of_le hle)
    rw [hpos, Mixed121Copy.reflected N j _ _ hj hTq hd, (eq_tsub_of_add_eq hsum).symm,
      word_digit row dummy N j _ hj (by exact_mod_cast (show Mixed121Kernel.extraPos ⟨j', hj'⟩ < 8801 by omega)),
      hi0]
    exact extra_digit i0 _ ⟨j', hj'⟩

/-- Both actual target digits avoid the exact high-mask digit `μ`. -/
theorem marked_targets_noCarry (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : CompactWord row N s) (hN : 1 < N) (hs : s < N)
    (hbool : ∀ j, dummy j ≤ 1) (j : V) (hj : j < N) (T : ℕ) (hT : T = 4393 ∨ T = 5495) :
    NoCarry (dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) (T:V))
      (dig 121 ((Mixed121Ports.highNat : ℕ) : V) (T:V)) := by
  obtain ⟨i0, _, hd⟩ := marked_target row dummy hw hN hs hbool j hj T hT
  have hm : dig 121 ((Mixed121Ports.highNat : ℕ) : V) (T:V) = ((Mixed121Ports.mu : ℕ) : V) := by
    rw [Mixed121Selected.mu_model]
    apply Mixed121Selected.model_target
    rcases hT with rfl | rfl
    · exact Mixed121Selected.high_target4393
    · exact Mixed121Selected.high_target5495
  rw [hd, hm]
  exact noCarry_cast (row_disjoint i0)

#print axioms Mixed121Target.rows_disjoint
#print axioms Mixed121Target.band_value
#print axioms Mixed121Target.marked_target
#print axioms Mixed121Target.marked_targets_noCarry
end Mixed121Target
