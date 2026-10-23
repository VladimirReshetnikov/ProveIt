import DiophantineConsistency.NativeQuadraticPositions
import DiophantineConsistency.LowMaskCoding
import DiophantineConsistency.PolynomialRangeBounds

/-!
# The literal package-52 quadratic source and its central-binomial contract

All integer words below are computed from the literal four-port coefficient
families. Polynomial semantics are used only to prove their arithmetic
identities and carry bounds. No compiler or consistency endpoint is assumed.
-/

namespace DiophantineConsistency.NativeQuadraticSource52

open Polynomial Finset Jones1982
open NativeQuadraticParent NativeQuadraticPositions SelectiveQuadraticCoding
open scoped BigOperators

set_option maxRecDepth 16000
set_option maxHeartbeats 200000

/-- The actual variable positions, excluding the dummy coordinate at 81. -/
def inputWeights (i : Fin 31) : ℕ := SelectiveCertificate52.weights i.succ

theorem inputWeights_injective : Function.Injective inputWeights := by decide

theorem inputWeights_bound (i : Fin 31) : inputWeights i < 175 :=
  lt_of_le_of_lt (SelectiveCertificate52.maximum_weight i.succ) (by decide)

def code (B : ℕ) (x : Fin 31 → ℕ) : ℕ := LowMaskCoding.indexedCode B inputWeights x

def lowMask (B b : ℕ) : ℕ := LowMaskCoding.indexedMask B b 175 inputWeights

/-- A finite computable integer expression for the complete kernel evaluation. -/
def kernelValue (ports : Fin 4 → ℤ) (B : ℤ) : ℤ :=
  ∑ k, ∑ p ∈ rowSupport k,
    QuadraticCoding.correction p * rowCoefficient ports k p *
      B ^ (target k - pairWeight SelectiveCertificate52.weights p)

theorem kernelValue_eq_eval (ports : Fin 4 → ℤ) (B : ℤ) :
    kernelValue ports B = (kernel ports).eval B := by
  simp only [kernelValue, kernel, combined, complementary, eval_finsetSum, eval_monomial]

/-- The dummy's literal monomial is `B^81`; an actual input occupies weight 0. -/
theorem encoded_padded_eval (B : ℕ) (x : Fin 31 → ℕ) :
    (encoded SelectiveCertificate52.weights (padded (fun i => (x i : ℤ)))).eval (B : ℤ) =
      (B : ℤ) ^ 81 + (code B x : ℤ) := by
  rw [encoded, eval_finsetSum]
  simp only [eval_monomial]
  rw [Fin.sum_univ_succ]
  simp only [padded,
    Fin.cases_zero, Fin.cases_succ, SelectiveCertificate52.dummy_weight, one_mul]
  unfold code LowMaskCoding.indexedCode inputWeights
  push_cast
  rfl

theorem product_eval (ports : Fin 4 → ℤ) (B : ℕ) (x : Fin 31 → ℕ) :
    (product ports (fun i => (x i : ℤ))).eval (B : ℤ) =
      ((B : ℤ) ^ 81 + (code B x : ℤ)) ^ 2 * kernelValue ports B := by
  change (encoded _ _ ^ 2 * kernel ports).eval (B : ℤ) = _
  rw [eval_mul, eval_pow, encoded_padded_eval, ← kernelValue_eq_eval]

attribute [local irreducible] product kernel kernelValue rowCoefficient

/-- The literal dense-padded high word, before taking its natural value. -/
def highIntAt (ports : Fin 4 → ℤ) (B g : ℤ) : ℤ :=
  2 * (B ^ 81 + g) ^ 2 * kernelValue ports B +
    B * ∑ i ∈ range 7865, B ^ i

def highInt (ports : Fin 4 → ℤ) (B g : ℕ) : ℤ := highIntAt ports B g

def highWord (ports : Fin 4 → ℤ) (B g : ℕ) : ℕ := (highInt ports B g).toNat

def highMask (B : ℕ) : ℕ := (B - 2) * ∑ k : Fin 22, B ^ target k

def N0 (B : ℕ) : ℕ := B ^ 175

def N1 (B : ℕ) : ℕ := 4 * B ^ 7865

def N (B : ℕ) : ℕ := N0 B * N1 B

def S (ports : Fin 4 → ℤ) (B g : ℕ) : ℕ :=
  SelectiveCarry.packTwo (N0 B) g (highWord ports B g)

def T (B b : ℕ) : ℕ := SelectiveCarry.packTwo (N0 B) (lowMask B b) (highMask B)

def rank (ports : Fin 4 → ℤ) (B b g : ℕ) : ℕ := centralCode (N B) (S ports B g) (T B b)

theorem target_injective : Function.Injective target := by
  intro k l h
  apply Fin.ext
  dsimp [target] at h
  omega

theorem highMask_eq_doubled {t : ℕ} (ht : 1 ≤ t) :
    highMask (2 ^ t) =
      2 * MultiTargetCarry.selectedMask t 7865 (univ.image target) := by
  rw [MultiTargetCarry.doubledMask_eq ht (univ.image target)
    (by intro i hi; obtain ⟨k, _, rfl⟩ := mem_image.mp hi; exact target_lt_span k)]
  unfold highMask
  rw [Finset.sum_image (fun k _ l _ h => target_injective h)]

/-- After low decoding, the literal high word is the exact shifted full polynomial. -/
theorem highWord_eq_doubled (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    {H : ℤ} (hH : 0 < H)
    (hc : ∀ k p, p ∈ rowSupport k → |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ H)
    {b t : ℕ} (hb : 0 < b) (ht : 1 ≤ t) (hx : ∀ i, x i < b)
    (hbase : (2 : ℤ) ^ t = 4096 * H * (b : ℤ) ^ 2) :
    highWord ports (2 ^ t) (code (2 ^ t) x) =
      2 * MultiTargetCarry.shiftedValue t 7865 (product ports (fun i => (x i : ℤ))).coeff := by
  have h := doubled_full_polynomial ports (fun i => (x i : ℤ)) ht
    (fun i hi => product_half_base_bound ports x hH hc hb ht hx hbase i)
  have hpow : ((2 ^ t : ℕ) : ℤ) = (2 : ℤ) ^ t := by norm_cast
  have heval := product_eval ports (2 ^ t) x
  simp only [hpow] at heval
  rw [heval] at h
  have he : highInt ports (2 ^ t) (code (2 ^ t) x) =
      ((2 * MultiTargetCarry.shiftedValue t 7865 (product ports (fun i => (x i : ℤ))).coeff : ℕ) : ℤ) := by
    change highIntAt ports ((2 ^ t : ℕ) : ℤ) (code (2 ^ t) x : ℤ) = _
    calc
      _ = highIntAt ports ((2 : ℤ) ^ t) (code (2 ^ t) x : ℤ) :=
        congrArg (fun z => highIntAt ports z (code (2 ^ t) x : ℤ)) hpow
      _ = _ := by simpa only [highIntAt, mul_assoc] using h.symm
  unfold highWord
  rw [he, Int.toNat_natCast]

theorem highInt_eq_rangeWord (ports : Fin 4 → ℤ) (B g : ℕ) :
    highInt ports B g = PolynomialRangeBounds.highWord (kernel ports) B g 81 7516 174 := by
  unfold highInt highIntAt PolynomialRangeBounds.highWord
  rw [kernelValue_eq_eval]

/-- Positivity is independent of the weak cap and of any digit decoding. -/
theorem highInt_pos (ports : Fin 4 → ℤ) {H : ℤ} {B : ℕ}
    (hB : 2 ≤ (B : ℤ)) (hBH : H ≤ (B : ℤ) - 1)
    (hc : ∀ k p, p ∈ rowSupport k → |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ H)
    (g : ℕ) : 0 < highInt ports B g := by
  rw [highInt_eq_rangeWord]
  exact PolynomialRangeBounds.highWord_pos hB hBH (Int.natCast_nonneg g)
    (kernel ports) (kernel_degree_le ports) (kernel_coefficient_bound ports (by
      have h := hc 21 (SelectiveCertificate52.activePair 0)
        (by exact Finset.mem_image.mpr ⟨0, by decide, rfl⟩)
      exact (abs_nonneg _).trans h) hc) (kernel_top_coefficient ports)

theorem highInt_pos_of_scale (ports : Fin 4 → ℤ) {H : ℤ} (hH : 0 < H)
    (hc : ∀ k p, p ∈ rowSupport k → |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ H)
    {B b : ℕ} (hb : 1 ≤ b)
    (hbase : (B : ℤ) = 4096 * H * (b : ℤ) ^ 2) (g : ℕ) :
    0 < highInt ports B g := by
  have hbZ : 1 ≤ (b : ℤ) := by exact_mod_cast hb
  have hH1 : 1 ≤ H := by omega
  have hb2 : 1 ≤ (b : ℤ) ^ 2 := by nlinarith
  have hHb : H ≤ H * (b : ℤ) ^ 2 := by
    nlinarith [mul_nonneg hH.le (sub_nonneg.mpr hb2)]
  have hB : 2 ≤ (B : ℤ) := by nlinarith [hbase]
  have hBH : H ≤ (B : ℤ) - 1 := by nlinarith [hbase]
  exact highInt_pos ports hB hBH hc g

/-- The toNat in the numerical word is exact for every natural g, before
ratio soundness supplies the weak upper cap. -/
theorem highWord_cast_of_scale (ports : Fin 4 → ℤ) {H : ℤ} (hH : 0 < H)
    (hc : ∀ k p, p ∈ rowSupport k → |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ H)
    {B b : ℕ} (hb : 1 ≤ b)
    (hbase : (B : ℤ) = 4096 * H * (b : ℤ) ^ 2) (g : ℕ) :
    (highWord ports B g : ℤ) = highInt ports B g := by
  exact Int.toNat_of_nonneg (highInt_pos_of_scale ports hH hc hb hbase g).le

theorem lowMask_lt {B b : ℕ} (hB : 1 < B) (hb : 1 ≤ b) (hbB : b ≤ B) :
    lowMask B b < N0 B := by
  have hS := LowMaskCoding.positions_subset inputWeights_bound
  unfold lowMask LowMaskCoding.indexedMask N0
  rw [← LowMaskCoding.ofDigits_maskList hb hbB hS]
  have h := Nat.ofDigits_lt_base_pow_length hB
    (fun z hz => LowMaskCoding.maskList_lt hb hB.le hz
      : ∀ z ∈ LowMaskCoding.maskList B b 175 (LowMaskCoding.positions inputWeights), z < B)
  simpa only [LowMaskCoding.maskList_length] using h

/-- Exact integer form of the complete sparse low mask. -/
theorem lowMask_cast {B b : ℕ} (hb : 1 ≤ b) (hbB : b ≤ B) :
    (lowMask B b : ℤ) = (B : ℤ) ^ 175 - 1 -
      ((b : ℤ) - 1) * ∑ i : Fin 31, (B : ℤ) ^ inputWeights i := by
  have h := LowMaskCoding.mask_int_eq hb hbB
    (LowMaskCoding.positions_subset inputWeights_bound)
  have hs : LowMaskCoding.supportValue B (LowMaskCoding.positions inputWeights) =
      ∑ i : Fin 31, B ^ inputWeights i := by
    unfold LowMaskCoding.supportValue LowMaskCoding.positions
    rw [Finset.sum_image (fun i _ j _ hij => inputWeights_injective hij)]
  rw [hs] at h
  push_cast at h
  exact h.symm

theorem highMask_cast {B : ℕ} (hB : 2 ≤ B) :
    (highMask B : ℤ) = ((B : ℤ) - 2) * ∑ k : Fin 22, (B : ℤ) ^ target k := by
  simp only [highMask, Nat.cast_mul, Nat.cast_sub hB, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_pow]

theorem S_cast_of_scale (ports : Fin 4 → ℤ) {H : ℤ} (hH : 0 < H)
    (hc : ∀ k p, p ∈ rowSupport k → |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ H)
    {B b : ℕ} (hb : 1 ≤ b)
    (hbase : (B : ℤ) = 4096 * H * (b : ℤ) ^ 2) (g : ℕ) :
    (S ports B g : ℤ) = g + (B : ℤ) ^ 175 * highInt ports B g := by
  simp only [S, SelectiveCarry.packTwo, N0, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  rw [highWord_cast_of_scale ports hH hc hb hbase g]
  ring

theorem T_cast {B b : ℕ} (hB : 2 ≤ B) (hb : 1 ≤ b) (hbB : b ≤ B) :
    (T B b : ℤ) =
      ((B : ℤ) ^ 175 - 1 - ((b : ℤ) - 1) * ∑ i : Fin 31, (B : ℤ) ^ inputWeights i) +
        (B : ℤ) ^ 175 * (((B : ℤ) - 2) * ∑ k : Fin 22, (B : ℤ) ^ target k) := by
  simp only [T, SelectiveCarry.packTwo, N0, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  rw [lowMask_cast hb hbB, highMask_cast hB]
  ring

theorem N_eq_packedBase (B : ℕ) : N B = 4 * B ^ 8040 := by
  unfold N N0 N1
  rw [← mul_assoc, mul_comm (B ^ 175) 4, mul_assoc, ← pow_add]

theorem rank_cast (ports : Fin 4 → ℤ) (B b g : ℕ) (hN : 1 ≤ N B) :
    (rank ports B b g : ℤ) =
      ((N B : ℤ) - 1) * (((S ports B g : ℤ) + T B b + 1) * N B + T B b + 1) :=
  SelectiveCarry.centralCode_factorization hN (S ports B g) (T B b)

/-- These inequalities hold before decoding g into any coordinates. -/
theorem prebinary_bounds (ports : Fin 4 → ℤ) {H : ℤ} (hH : 0 < H)
    (hc : ∀ k p, p ∈ rowSupport k → |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ H)
    {B b g : ℕ} (hb : 1 ≤ b)
    (hbase : (B : ℤ) = 4096 * H * (b : ℤ) ^ 2)
    (hcap : g < 4 * b * B ^ 174) :
    1 < B ∧ b < B ∧ g < N0 B ∧ lowMask B b < N0 B ∧
      0 < highInt ports B g ∧ highWord ports B g < N1 B := by
  have hbZ : 1 ≤ (b : ℤ) := by exact_mod_cast hb
  have hscale : 4 * (b : ℤ) < B := by
    rw [hbase]
    exact PolynomialRangeBounds.scale_gt_four_digits hH hbZ
  have hB : 2 ≤ (B : ℤ) := by linarith
  have hBnat : 1 < B := by exact_mod_cast hB
  have hbB : b < B := by exact_mod_cast (show (b : ℤ) < B by linarith)
  have hgZ : (g : ℤ) < 4 * (b : ℤ) * (B : ℤ) ^ 174 := by exact_mod_cast hcap
  have hg : g < N0 B := by
    unfold N0
    exact_mod_cast PolynomialRangeBounds.weak_cap_lt_low_block hB hscale 174 hgZ
  have hw := PolynomialRangeBounds.highWord_bounds hB hH hbZ hbase
    (show 0 ≤ (g : ℤ) by positivity) (kernel ports)
    (kernel_degree_le ports) (kernel_coefficient_bound ports hH.le hc)
    (kernel_top_coefficient ports) (by decide : 81 ≤ 174) hgZ
  simp only [← highInt_eq_rangeWord] at hw
  refine ⟨hBnat, hbB, hg, lowMask_lt hBnat hb hbB.le, hw.1, ?_⟩
  unfold highWord
  apply (Int.toNat_lt hw.1.le).mpr
  simpa only [N1, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hw.2

theorem N0_power (t : ℕ) : N0 (2 ^ t) = 2 ^ (175 * t) := by
  simp only [N0, ← pow_mul, Nat.mul_comm]

theorem N1_power (t : ℕ) : N1 (2 ^ t) = 2 ^ (2 + 7865 * t) := by
  rw [N1, ← pow_mul, Nat.mul_comm t 7865, pow_add]
  rfl

theorem N_power (t : ℕ) : N (2 ^ t) = 2 ^ (175 * t + (2 + 7865 * t)) := by
  rw [N, N0_power, N1_power]
  exact (pow_add 2 (175 * t) (2 + 7865 * t)).symm

theorem highMask_lt {t : ℕ} (ht : 1 ≤ t) : highMask (2 ^ t) < N1 (2 ^ t) := by
  rw [highMask_eq_doubled ht]
  have h := SelectiveCarry.selectedMask_lt (n := 7865) ht (univ.image target)
  have hp : 0 < (2 ^ t) ^ 7865 := by positivity
  dsimp [N1]
  omega

/-- The literal four words fit their two blocks before using low-digit recovery. -/
theorem central_divisibility_iff (ports : Fin 4 → ℤ) {H : ℤ} (hH : 0 < H)
    (hc : ∀ k p, p ∈ rowSupport k → |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ H)
    {b g t : ℕ} (hb : 1 ≤ b) (ht : 1 ≤ t)
    (hbase : (2 : ℤ) ^ t = 4096 * H * (b : ℤ) ^ 2)
    (hcap : g < 4 * b * (2 ^ t) ^ 174) :
    N (2 ^ t) ^ 2 ∣ (2 * rank ports (2 ^ t) b g).choose (rank ports (2 ^ t) b g) ↔
      τ 2 g (lowMask (2 ^ t) b) = 0 ∧
      τ 2 (highWord ports (2 ^ t) g) (highMask (2 ^ t)) = 0 := by
  have hbcast : ((2 ^ t : ℕ) : ℤ) = 4096 * H * (b : ℤ) ^ 2 := by exact_mod_cast hbase
  obtain ⟨_, _, hg, hm, _, hj⟩ := prebinary_bounds ports hH hc hb hbcast hcap
  have hmask := highMask_lt ht
  rw [N0_power] at hg hm
  rw [N1_power] at hj hmask
  have h := SelectiveCarry.central_blocks_iff hg hm hj hmask
  simpa only [rank, S, T, N_power, N0_power] using h

/-- The actual low mask decodes precisely the 31 bounded source coordinates. -/
theorem low_mask_iff {b B g k t : ℕ} (hb : b = 2 ^ k) (hB : B = 2 ^ t)
    (hB1 : 1 < B) (hbB : b ≤ B) (hg : g < N0 B) :
    τ 2 g (lowMask B b) = 0 ↔
      ∃ x : Fin 31 → ℕ, (∀ i, x i < b) ∧ g = code B x := by
  have h := LowMaskCoding.indexed_mask_code_iff inputWeights_injective inputWeights_bound
    hb hB hB1 hbB (g := g)
  constructor
  · intro hz
    apply h.mp
    exact ⟨hg, (τ_two_eq_zero_iff _ _).mp hz⟩
  · intro hx
    exact (τ_two_eq_zero_iff _ _).mpr (h.mpr hx).2

/-- Exact source-to-central-binomial contract for the supplied finite words. -/
theorem source_contract (ports : Fin 4 → ℤ) {H : ℤ} (hH : 0 < H)
    (hc : ∀ k p, p ∈ rowSupport k → |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ H)
    {b g k t : ℕ} (hb : b = 2 ^ k) (ht : 1 ≤ t)
    (hbase : (2 : ℤ) ^ t = 4096 * H * (b : ℤ) ^ 2)
    (hcap : g < 4 * b * (2 ^ t) ^ 174) :
    N (2 ^ t) ^ 2 ∣ (2 * rank ports (2 ^ t) b g).choose (rank ports (2 ^ t) b g) ↔
      ∃ x : Fin 31 → ℕ, (∀ i, x i < b) ∧ g = code (2 ^ t) x ∧
        ∀ j, sourceRows ports (fun i => (x i : ℤ) + 1) j = 0 := by
  have hb1 : 1 ≤ b := by rw [hb]; exact Nat.one_le_two_pow
  have hb0 : 0 < b := by omega
  have hbcast : ((2 ^ t : ℕ) : ℤ) = 4096 * H * (b : ℤ) ^ 2 := by exact_mod_cast hbase
  obtain ⟨hB1, hbB, hg, _, _, _⟩ := prebinary_bounds ports hH hc hb1 hbcast hcap
  rw [central_divisibility_iff ports hH hc hb1 ht hbase hcap]
  constructor
  · rintro ⟨hlow, hhigh⟩
    obtain ⟨x, hx, hcode⟩ := (low_mask_iff hb rfl hB1 hbB.le hg).mp hlow
    refine ⟨x, hx, hcode, ?_⟩
    rw [hcode, highWord_eq_doubled ports x hH hc hb0 ht hx hbase,
      highMask_eq_doubled ht] at hhigh
    exact (tau_source_rows_iff_of_scale ports x hH hc hb0 ht hx hbase).mp hhigh
  · rintro ⟨x, hx, hcode, hsource⟩
    refine ⟨(low_mask_iff hb rfl hB1 hbB.le hg).mpr ⟨x, hx, hcode⟩, ?_⟩
    rw [hcode, highWord_eq_doubled ports x hH hc hb0 ht hx hbase,
      highMask_eq_doubled ht]
    exact (tau_source_rows_iff_of_scale ports x hH hc hb0 ht hx hbase).mpr hsource

end DiophantineConsistency.NativeQuadraticSource52
