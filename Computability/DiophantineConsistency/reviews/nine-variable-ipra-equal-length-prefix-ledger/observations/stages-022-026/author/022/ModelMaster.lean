import DiophantineConsistency.ModelCoding
import DiophantineConsistency.ModelDigitTransfer
import DiophantineConsistency.ModelPacking
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Jones 1982, §4 in every model of `𝗜𝚺₁`: the three carry tests at input `1`

Internal counterpart of `Jones1982` `Master2.lean`/`Master3.lean`/`Theorem2.lean`,
specialised to the input `x = 1` and to the index `z = indexZ seed 0`, `y = indexY seed 0`
of a degree-four seed.  Since in the reduction of `NineReduce` the quantities
`e, l, λ, θ, q` are fixed functions of `b`, no unknown `e`, `l` has to be decoded:
the sufficiency direction only uses the tests (4.8) and (4.11), and (4.4) is only
*verified* in the necessity direction (no Lemma 2.9 decoding is needed).

With `b = 2ᵏ`, `B = b⁵`, `q = B^L`, the model elements are
`eV = Σ_{i<2L} dᵢ Bⁱ` (digits of `e`), `lV = Σ_{i<ν} B^(5^(i+1))`, `lamV = Σ_{i<4L} Bⁱ`,
`θV = B − 2z`, `M1V = q³ − 1 − (b − 1) l`, `S3V`, `DV = B − 2`, and the packed code `RV`.
Their values in `DiffRing V` are `eR`, `lR`, `lamR`, `qR`, `thirdR` (the article's `S₃`).

* `tau1_of_code`, `code_of_tau1`: (4.8) — `g = Σ zᵢ B^(5^i)` with `zᵢ < b` iff no carry
  against `M1V` (and then `g < b B^(5^ν)`);
* `tau2_holds`: (4.4) holds for the explicit `e`, `l`;
* `tau3_iff`: (4.11) — for a code `c = 1 + B + g` of `(1, w)`, `NoCarry S₃ T₃ ↔ P(1, w) = 0`;
* `RV_rank`: `ι RV` is `NinePolynomial.rankCode` of the evaluated quantities;
* `pack_iff`: the three tests hold iff `(q¹⁶)² ∣ binom (2 RV) RV`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.ModelMaster
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticBinomPascal ModelCarries ModelDigitTransfer ModelPacking
  ModelDifferenceRing ExecutableJones
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Generic helpers -/

theorem exp_natCast (n : ℕ) : Exp.exp (n : V) = (2 : V) ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, exp_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, exp_succ, ih, pow_succ, mul_comm]

theorem two_z_eq_exp {ν : ℕ} (seed : Expr (Fin (ν + 1))) :
    ((2 * indexZ seed 0 : ℕ) : V) = Exp.exp ((indexExponent seed 0 + 1 : ℕ) : V) := by
  rw [exp_natCast, ModelCoding.indexZ_eq]
  push_cast
  ring

theorem self_le_pow_five {a : V} (h : 1 ≤ a) : a ≤ a ^ 5 := by
  calc a = a ^ 1 := (pow_one a).symm
    _ ≤ a ^ 5 := pow_le_pow_right₀ h (by omega)

open Classical in
/-- A preimage in `V` of a nonnegative element of the ring of differences. -/
def toV (x : DiffRing V) : V := if h : 0 ≤ x then Classical.choose (nonneg_iff.mp h) else 0

theorem ι_toV {x : DiffRing V} (h : 0 ≤ x) : ι (toV x) = x := by
  unfold toV
  rw [dif_pos h]
  exact (Classical.choose_spec (nonneg_iff.mp h)).symm

theorem ι_dsum (B : V) (f : ℕ → V) (n : ℕ) :
    ι (dsum B f n) = ∑ i ∈ Finset.range n, ι (f i) * ι B ^ i := by
  unfold dsum
  rw [map_sum]
  simp only [map_mul, map_pow]

/-- The code positions `5^(i+1)`, `i < ν`. -/
def posν (ν : ℕ) (j : ℕ) : Prop := ∃ i < ν, 5 ^ (i + 1) = j

noncomputable instance posν_dec (ν : ℕ) : DecidablePred (posν ν) := Classical.decPred _

theorem codeInd_le_one (pos : ℕ → Prop) [DecidablePred pos] (j : ℕ) :
    (codeInd pos j : V) ≤ 1 := by
  unfold codeInd
  split_ifs
  · exact le_rfl
  · exact Arithmetic.zero_le _

theorem lV_eq_dsum (ν : ℕ) (B : V) (N : ℕ) (hN : 5 ^ ν < N) :
    ∑ i ∈ Finset.range ν, B ^ (5 ^ (i + 1)) = dsum B (codeInd (posν ν)) N := by
  rw [dsum_powers B ν N hN (codeInd (posν ν)) (fun j hj => by
    unfold codeInd
    rw [if_neg (show ¬ posν ν j from hj)])]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  unfold codeInd
  rw [if_pos (show posν ν (5 ^ (i + 1)) from ⟨i, Finset.mem_range.mp hi, rfl⟩), one_mul]

theorem L_facts (ν : ℕ) :
    1 ≤ codingLexp ν 4 ∧ 5 ^ ν + 1 ≤ codingLexp ν 4 - 1 ∧ 5 ^ ν + 2 ≤ 3 * codingLexp ν 4 ∧
      5 ^ ν + 1 ≤ 2 * codingLexp ν 4 ∧ 5 ^ ν < 2 * codingLexp ν 4 ∧
      5 ^ ν < 3 * codingLexp ν 4 ∧ codingLexp ν 4 < 8 * codingLexp ν 4 ∧
      2 * codingLexp ν 4 < 4 * codingLexp ν 4 := by
  have h1 : codingLexp ν 4 = 5 ^ ν * 5 := by rw [ModelCoding.codingLexp_eq, pow_succ]
  have h2 : 1 ≤ 5 ^ ν := Nat.one_le_pow _ _ (by omega)
  omega

/-! ### Codes `g = Σ_{i<ν} wᵢ B^(5^(i+1))` -/

/-- The code of `w`. -/
def gOf (ν : ℕ) (w : Fin ν → V) (B : V) : V := ∑ i : Fin ν, w i * B ^ (5 ^ ((i : ℕ) + 1))

/-- `w` extended by zero to `ℕ`. -/
def extN {ν : ℕ} (w : Fin ν → V) (i : ℕ) : V := if h : i < ν then w ⟨i, h⟩ else 0

/-- The digit function of a code. -/
def spread (ν : ℕ) (a : ℕ → V) (j : ℕ) : V :=
  ∑ i ∈ Finset.range ν, if 5 ^ (i + 1) = j then a i else 0

theorem gOf_eq (ν : ℕ) (w : Fin ν → V) (B : V) :
    gOf ν w B = ∑ i ∈ Finset.range ν, extN w i * B ^ (5 ^ (i + 1)) := by
  calc gOf ν w B = ∑ i : Fin ν, extN w i * B ^ (5 ^ ((i : ℕ) + 1)) :=
        Finset.sum_congr rfl (fun i _ => by simp only [extN, dif_pos i.isLt, Fin.eta])
    _ = ∑ i ∈ Finset.range ν, extN w i * B ^ (5 ^ (i + 1)) :=
        Fin.sum_univ_eq_sum_range (fun i => extN w i * B ^ (5 ^ (i + 1))) ν

theorem spread_at (ν : ℕ) (a : ℕ → V) {i0 : ℕ} (hi0 : i0 < ν) :
    spread ν a (5 ^ (i0 + 1)) = a i0 := by
  unfold spread
  rw [Finset.sum_eq_single i0]
  · rw [if_pos rfl]
  · intro i _ hne
    rw [if_neg]
    intro h
    apply hne
    have := Nat.pow_right_injective (show 2 ≤ 5 by omega) h
    omega
  · intro h
    exact absurd (Finset.mem_range.mpr hi0) h

theorem spread_off (ν : ℕ) (a : ℕ → V) (j : ℕ) (h : ¬ posν ν j) : spread ν a j = 0 :=
  Finset.sum_eq_zero (fun i hi => if_neg (fun he => h ⟨i, Finset.mem_range.mp hi, he⟩))

theorem spread_lt (ν : ℕ) (a : ℕ → V) {c : V} (hc0 : 0 < c) (ha : ∀ i < ν, a i < c) (j : ℕ) :
    spread ν a j < c := by
  by_cases h : posν ν j
  · obtain ⟨i, hi, rfl⟩ := h
    rw [spread_at ν a hi]
    exact ha i hi
  · rw [spread_off ν a j h]
    exact hc0

theorem dsum_spread (ν : ℕ) (a : ℕ → V) (B : V) (N : ℕ) (hN : 5 ^ ν < N) :
    dsum B (spread ν a) N = ∑ i ∈ Finset.range ν, a i * B ^ (5 ^ (i + 1)) := by
  rw [dsum_powers B ν N hN (spread ν a) (fun j hj => spread_off ν a j hj)]
  exact Finset.sum_congr rfl (fun i hi => by rw [spread_at ν a (Finset.mem_range.mp hi)])

/-- The evaluation point `(1, w)` in the ring of differences. -/
def zsOf {ν : ℕ} (w : Fin ν → V) : Fin (ν + 1) → DiffRing V :=
  fun j => ι ((Fin.cons (1 : V) w : Fin (ν + 1) → V) j)

theorem cval_cons {ν : ℕ} (w : Fin ν → V) (B : V) :
    ModelCoding.cval (zsOf w) (ι B) = 1 + 1 * ι B + ι (gOf ν w B) := by
  unfold ModelCoding.cval gOf zsOf
  rw [Fin.sum_univ_succ, map_sum]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, pow_one, map_one, map_mul,
    map_pow, Fin.val_succ]
  ring

/-! ### The quantities of the reduction -/

section Defs
variable {ν : ℕ} (seed : Expr (Fin (ν + 1)))

def qV (ν : ℕ) (b : V) : V := (b ^ 5) ^ codingL4 ν
def lamV (ν : ℕ) (b : V) : V := ∑ i ∈ Finset.range (4 * codingLexp ν 4), (b ^ 5) ^ i
def lV (ν : ℕ) (b : V) : V := ∑ i ∈ Finset.range ν, (b ^ 5) ^ (5 ^ (i + 1))
/-- The base-`B` digits of `e`, as model elements. -/
def ecV (i : ℕ) : V := ((ModelCoding.ecoef seed (indexZ seed 0) i).toNat : V)
def eV (b : V) : V := dsum (b ^ 5) (ecV seed) (2 * codingLexp ν 4)
def θV (b : V) : V := b ^ 5 - ((2 * indexZ seed 0 : ℕ) : V)
def M1V (ν : ℕ) (b : V) : V := qV ν b ^ 3 - 1 - (b - 1) * lV ν b

/-- The value of `e` (as in `ModelJonesSyntax.mapVars_syntaxVars`). -/
def eR (bR : DiffRing V) : DiffRing V :=
  ∑ k ∈ codingStar ν 4, ((indexZ seed 0 : DiffRing V) + (pCoefficient seed k : DiffRing V)) *
    (bR ^ 5) ^ (codingLexp ν 4 - codingExpo ν 4 k)
def lR (ν : ℕ) (bR : DiffRing V) : DiffRing V :=
  ∑ i ∈ Finset.range ν, (bR ^ 5) ^ (5 ^ (i + 1))
def lamR (ν : ℕ) (bR : DiffRing V) : DiffRing V :=
  ∑ i ∈ Finset.range (4 * codingLexp ν 4), (bR ^ 5) ^ i
def qR (ν : ℕ) (bR : DiffRing V) : DiffRing V := (bR ^ 5) ^ codingL4 ν
/-- The signed third block `S₃ = 2(e − zλ)(1 + x B + g)⁴ + λB + λBq⁴` at `x = 1`. -/
def thirdR (bR gR : DiffRing V) : DiffRing V :=
  2 * (eR seed bR - (indexZ seed 0 : DiffRing V) * lamR ν bR) * (1 + 1 * bR ^ 5 + gR) ^ 4 +
    lamR ν bR * bR ^ 5 + lamR ν bR * bR ^ 5 * qR ν bR ^ 4

def S3V (b g : V) : V := toV (thirdR seed (ι b) (ι g))
def DV (b : V) : V := toV (ι b ^ 5 - 2)

/-- The packed code `R` of Theorem 2. -/
def RV (b g : V) : V :=
  centralCode (qV ν b ^ 16)
    (pack3 (qV ν b ^ 3) (qV ν b ^ 4) g (eV seed b + lV ν b * qV ν b ^ 2) (S3V seed b g))
    (pack3 (qV ν b ^ 3) (qV ν b ^ 4) (M1V ν b) (θV seed b * lamV ν b) (DV b * qV ν b))

theorem qV_eq (ν : ℕ) (b : V) : qV ν b = (b ^ 5) ^ codingLexp ν 4 := rfl

theorem qV_pow (ν : ℕ) (b : V) (m : ℕ) : qV ν b ^ m = (b ^ 5) ^ (m * codingLexp ν 4) := by
  rw [qV_eq, ← pow_mul, mul_comm]

theorem ι_qV (ν : ℕ) (b : V) : ι (qV ν b) = qR ν (ι b) := by
  unfold qV qR
  rw [map_pow, map_pow]

theorem ι_lamV (ν : ℕ) (b : V) : ι (lamV ν b) = lamR ν (ι b) := by
  unfold lamV lamR
  rw [map_sum]
  simp only [map_pow]

theorem ι_lV (ν : ℕ) (b : V) : ι (lV ν b) = lR ν (ι b) := by
  unfold lV lR
  rw [map_sum]
  simp only [map_pow]

theorem ecoef_nonneg (i : ℕ) : 0 ≤ ModelCoding.ecoef seed (indexZ seed 0) i :=
  (ModelCoding.ecoef_bounds seed (ModelCoding.index_big' seed)
    (le_trans (by omega) (ModelCoding.four_le_indexZ seed)) i).1

theorem ι_ecV (i : ℕ) :
    ι (ecV seed i) = (ModelCoding.ecoef seed (indexZ seed 0) i : DiffRing V) := by
  unfold ecV
  rw [map_natCast, ← Int.cast_natCast, Int.toNat_of_nonneg (ecoef_nonneg seed i)]

theorem ecV_lt (i : ℕ) : ecV seed i < ((2 * indexZ seed 0 : ℕ) : V) := by
  have hb := ModelCoding.ecoef_bounds seed (ModelCoding.index_big' seed)
    (le_trans (by omega) (ModelCoding.four_le_indexZ seed)) i
  have h1 : ((ModelCoding.ecoef seed (indexZ seed 0) i).toNat : ℤ) < 2 * (indexZ seed 0 : ℤ) := by
    rw [Int.toNat_of_nonneg hb.1]
    exact hb.2.1
  have h2 : (ModelCoding.ecoef seed (indexZ seed 0) i).toNat < 2 * indexZ seed 0 := by
    exact_mod_cast h1
  unfold ecV
  exact Nat.cast_lt.mpr h2

theorem ι_eV (b : V) : ι (eV seed b) = eR seed (ι b) := by
  have hL := ModelCoding.codingLexp_pos ν
  unfold eV eR
  rw [ι_dsum, ModelCoding.sum_eq_ecoef seed (indexZ seed 0) (ι b ^ 5) (2 * codingLexp ν 4)
    (by omega)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ι_ecV, map_pow]

theorem ι_θV {b : V} (h : ((2 * indexZ seed 0 : ℕ) : V) ≤ b ^ 5) :
    ι (θV seed b) = ι b ^ 5 - 2 * (indexZ seed 0 : DiffRing V) := by
  unfold θV
  rw [ι_tsub h, map_pow, map_natCast, Nat.cast_mul, Nat.cast_ofNat]

theorem ι_M1V (ν : ℕ) {b : V} (hb1 : 1 ≤ b) (h : (b - 1) * lV ν b + 1 ≤ qV ν b ^ 3) :
    ι (M1V ν b) = qR ν (ι b) ^ 3 - 1 - (ι b - 1) * lR ν (ι b) := by
  have hX : (b - 1) * lV ν b ≤ qV ν b ^ 3 - 1 := le_tsub_of_add_le_right h
  have h1 : 1 ≤ qV ν b ^ 3 := le_trans (le_add_left le_rfl) h
  unfold M1V
  rw [ι_tsub hX, ι_tsub h1, map_mul, ι_tsub hb1, map_pow, ι_qV, ι_lV, map_one]

end Defs

/-! ### Sizes -/

section Sizes
variable {ν : ℕ} (seed : Expr (Fin (ν + 1)))

theorem dr_base {b : V} (hyb : (indexY seed 0 : V) < b) :
    (9 : DiffRing V) ≤ ι (b) ∧ 2 * (indexZ seed 0 : DiffRing V) + 1 ≤ ι (b) ∧
      2 * (indexZ seed 0 : DiffRing V) * ((ν : DiffRing V) + 2) ^ 4 < ι (b) ∧
      (4 : DiffRing V) ≤ indexZ seed 0 ∧ (indexY seed 0 : DiffRing V) + 1 ≤ ι (b) := by
  have hV : (indexY seed 0 : V) + 1 ≤ b := lt_iff_succ_le.mp hyb
  have hR : (indexY seed 0 : DiffRing V) + 1 ≤ ι (b) := by
    have h := ι_le_ι.mpr hV
    rwa [map_add, map_natCast, map_one] at h
  have h2z : 2 * (indexZ seed 0 : DiffRing V) ≤ indexY seed 0 := by
    exact_mod_cast ModelCoding.two_z_le_y seed
  have hz4 : (4 : DiffRing V) ≤ indexZ seed 0 := by
    exact_mod_cast ModelCoding.four_le_indexZ seed
  have hbig : 2 * (indexZ seed 0 : DiffRing V) * ((ν : DiffRing V) + 2) ^ 4 < indexY seed 0 := by
    exact_mod_cast ModelCoding.y_big seed
  exact ⟨by linarith, by linarith, by linarith, hz4, hR⟩

theorem v_base {b : V} (hyb : (indexY seed 0 : V) < b) :
    1 ≤ b ∧ b ≤ b ^ 5 ∧ 4 * b ≤ b ^ 5 ∧
      ((2 * indexZ seed 0 : ℕ) : V) ≤ b ^ 5 ∧ 2 ≤ b ^ 5 := by
  obtain ⟨h9, h2z1, -, -, -⟩ := dr_base seed hyb
  have hx4 : (4 : DiffRing V) ≤ ι (b) ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : DiffRing V) ≤ 9) h9 4
    have e : (9 : DiffRing V) ^ 4 = 6561 := by norm_num
    rw [e] at h
    linarith
  have hx0 : (0 : DiffRing V) ≤ ι (b) := by linarith
  have hx5 : 4 * ι (b) ≤ ι (b) ^ 5 := by
    have h := mul_le_mul_of_nonneg_left hx4 hx0
    have e : ι (b) * ι (b) ^ 4 = ι (b) ^ 5 := by ring
    linarith
  refine ⟨pos_iff_one_le.mp (lt_of_le_of_lt (Arithmetic.zero_le _) hyb), ?_, ?_, ?_, ?_⟩
  · apply ι_le_ι.mp
    rw [map_pow]
    linarith
  · apply ι_le_ι.mp
    simp only [map_mul, map_pow, map_ofNat]
    exact hx5
  · apply ι_le_ι.mp
    rw [map_pow, map_natCast]
    push_cast
    linarith
  · apply ι_le_ι.mp
    simp only [map_pow, map_ofNat]
    linarith

theorem g_lt_pow {b g : V} (hyb : (indexY seed 0 : V) < b)
    (hg : g < 4 * b * (b ^ 5) ^ (5 ^ ν)) :
    g < (b ^ 5) ^ (5 ^ ν + 1) := by
  obtain ⟨-, -, h4, -, -⟩ := v_base seed hyb
  calc g < 4 * b * (b ^ 5) ^ (5 ^ ν) := hg
    _ ≤ b ^ 5 * (b ^ 5) ^ (5 ^ ν) :=
        mul_le_mul_of_nonneg_right h4 (Arithmetic.zero_le _)
    _ = (b ^ 5) ^ (5 ^ ν + 1) := (pow_succ' _ _).symm

theorem c_le_q {b g : V} (hyb : (indexY seed 0 : V) < b)
    (hg : g < 4 * b * (b ^ 5) ^ (5 ^ ν)) :
    1 + b ^ 5 + g ≤ qV ν (b) := by
  obtain ⟨hb1, hbB, -, -, hB2⟩ := v_base seed hyb
  have hB1 : 1 ≤ b ^ 5 := le_trans hb1 hbB
  obtain ⟨hL1, hn1, -, -, -, -, -, -⟩ := L_facts ν
  have hgX : g + 1 ≤ (b ^ 5) ^ (codingLexp ν 4 - 1) :=
    lt_iff_succ_le.mp (lt_of_lt_of_le (g_lt_pow seed hyb hg) (pow_le_pow_right₀ hB1 hn1))
  have hBX : b ^ 5 ≤ (b ^ 5) ^ (codingLexp ν 4 - 1) := by
    calc b ^ 5 = (b ^ 5) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hB1 (le_trans (Nat.le_add_left 1 (5 ^ ν)) hn1)
  have hBXL : b ^ 5 * (b ^ 5) ^ (codingLexp ν 4 - 1) = qV ν (b) := by
    rw [qV_eq, ← pow_succ']
    congr 1
    omega
  calc 1 + b ^ 5 + g = b ^ 5 + (g + 1) := by ring
    _ ≤ (b ^ 5) ^ (codingLexp ν 4 - 1) + (b ^ 5) ^ (codingLexp ν 4 - 1) :=
        add_le_add hBX hgX
    _ = 2 * (b ^ 5) ^ (codingLexp ν 4 - 1) := (two_mul _).symm
    _ ≤ b ^ 5 * (b ^ 5) ^ (codingLexp ν 4 - 1) :=
        mul_le_mul_of_nonneg_right hB2 (Arithmetic.zero_le _)
    _ = qV ν (b) := hBXL

theorem g_lt_q3 {b g : V} (hyb : (indexY seed 0 : V) < b)
    (hg : g < 4 * b * (b ^ 5) ^ (5 ^ ν)) : g < qV ν (b) ^ 3 := by
  obtain ⟨hb1, hbB, -, -, -⟩ := v_base seed hyb
  obtain ⟨-, -, h3, -, -, -, -, -⟩ := L_facts ν
  rw [qV_pow]
  exact lt_of_lt_of_le (g_lt_pow seed hyb hg) (pow_le_pow_right₀ (le_trans hb1 hbB) (by omega))

theorem eV_lt {b : V} (hyb : (indexY seed 0 : V) < b) :
    eV seed (b) < qV ν (b) ^ 2 := by
  obtain ⟨-, -, -, hZB, -⟩ := v_base seed hyb
  rw [qV_pow, eV]
  exact dsum_lt _ _ _ (fun i _ => lt_of_lt_of_le (ecV_lt seed i) hZB)

theorem lV_lt (ν : ℕ) {b : V} (hB2 : 2 ≤ b ^ 5) : lV ν b < (b ^ 5) ^ (5 ^ ν + 1) := by
  rw [lV, lV_eq_dsum ν (b ^ 5) (5 ^ ν + 1) (by omega)]
  exact dsum_lt _ _ _ (fun i _ =>
    lt_of_le_of_lt (codeInd_le_one _ i) (lt_of_lt_of_le one_lt_two hB2))

theorem M1_ok {b : V} (hyb : (indexY seed 0 : V) < b) :
    (b - 1) * lV ν (b) + 1 ≤ qV ν (b) ^ 3 := by
  obtain ⟨hb1, hbB, -, -, hB2⟩ := v_base seed hyb
  have hB1 : 1 ≤ b ^ 5 := le_trans hb1 hbB
  obtain ⟨-, -, h3, -, -, -, -, -⟩ := L_facts ν
  have h1 : (b - 1) * lV ν (b) ≤ b * lV ν (b) :=
    mul_le_mul_of_nonneg_right tsub_le_self (Arithmetic.zero_le _)
  have h2 : b * lV ν (b) < b * (b ^ 5) ^ (5 ^ ν + 1) :=
    mul_lt_mul_of_pos_left (lV_lt ν hB2) (lt_of_le_of_lt (Arithmetic.zero_le _) hyb)
  have h3' : b * (b ^ 5) ^ (5 ^ ν + 1) ≤
      b ^ 5 * (b ^ 5) ^ (5 ^ ν + 1) :=
    mul_le_mul_of_nonneg_right hbB (Arithmetic.zero_le _)
  have h4 : b ^ 5 * (b ^ 5) ^ (5 ^ ν + 1) = (b ^ 5) ^ (5 ^ ν + 1 + 1) :=
    (pow_succ' _ _).symm
  have h5 : (b ^ 5) ^ (5 ^ ν + 1 + 1) ≤ qV ν (b) ^ 3 := by
    rw [qV_pow]
    exact pow_le_pow_right₀ hB1 (by omega)
  exact lt_iff_succ_le.mp (lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (h3'.trans (h4.le.trans h5))))

theorem block2_lt {b : V} (hyb : (indexY seed 0 : V) < b) :
    eV seed (b) + lV ν (b) * qV ν (b) ^ 2 < qV ν (b) ^ 4 := by
  obtain ⟨hb1, hbB, -, -, hB2⟩ := v_base seed hyb
  have hB1 : 1 ≤ b ^ 5 := le_trans hb1 hbB
  obtain ⟨-, -, -, h2, -, -, -, -⟩ := L_facts ν
  have he := eV_lt seed hyb
  have hl : lV ν (b) < qV ν (b) ^ 2 := by
    rw [qV_pow]
    exact lt_of_lt_of_le (lV_lt ν hB2) (pow_le_pow_right₀ hB1 (by omega))
  calc eV seed (b) + lV ν (b) * qV ν (b) ^ 2
      < qV ν (b) ^ 2 + lV ν (b) * qV ν (b) ^ 2 :=
        add_lt_add_of_lt_of_le he le_rfl
    _ = (lV ν (b) + 1) * qV ν (b) ^ 2 := by ring
    _ ≤ qV ν (b) ^ 2 * qV ν (b) ^ 2 :=
        mul_le_mul_of_nonneg_right (lt_iff_succ_le.mp hl) (Arithmetic.zero_le _)
    _ = qV ν (b) ^ 4 := by ring

theorem geomV (B : V) (hB : 1 ≤ B) (n : ℕ) :
    (B - 1) * ∑ i ∈ Finset.range n, B ^ i + 1 = B ^ n := by
  obtain ⟨D, rfl⟩ : ∃ D, B = D + 1 := ⟨B - 1, (tsub_add_cancel_of_le hB).symm⟩
  rw [add_tsub_cancel_right]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ, ← ih]
    ring

theorem block2'_lt {b : V} (hyb : (indexY seed 0 : V) < b) :
    θV seed (b) * lamV ν (b) < qV ν (b) ^ 4 := by
  obtain ⟨hb1, hbB, -, -, -⟩ := v_base seed hyb
  have hB1 : 1 ≤ b ^ 5 := le_trans hb1 hbB
  have hZ1 : (1 : V) ≤ ((2 * indexZ seed 0 : ℕ) : V) := by
    have := ModelCoding.four_le_indexZ seed
    exact Nat.one_le_cast.mpr (by omega)
  have hθ : θV seed (b) ≤ b ^ 5 - 1 := tsub_le_tsub_left hZ1 _
  calc θV seed (b) * lamV ν (b)
      ≤ (b ^ 5 - 1) * lamV ν (b) :=
        mul_le_mul_of_nonneg_right hθ (Arithmetic.zero_le _)
    _ < (b ^ 5 - 1) * lamV ν (b) + 1 := lt_add_one _
    _ = qV ν (b) ^ 4 := by
        rw [qV_pow, lamV]
        exact geomV _ hB1 _

/-- `0 ≤ S₃ < q⁹` for every `g < 4 b B^(5^ν)`. -/
theorem third_ok {b g : V} (hyb : (indexY seed 0 : V) < b)
    (hg : g < 4 * b * (b ^ 5) ^ (5 ^ ν)) :
    0 ≤ thirdR seed (ι (b)) (ι g) ∧
      thirdR seed (ι (b)) (ι g) < qR ν (ι (b)) ^ 9 := by
  obtain ⟨h9, -, -, hz4, -⟩ := dr_base seed hyb
  obtain ⟨hb1, hbB, -, hZB, hB2⟩ := v_base seed hyb
  have hB1 : 1 ≤ b ^ 5 := le_trans hb1 hbB
  obtain ⟨hL1, -, -, -, -, -, -, h24⟩ := L_facts ν
  have he : 0 ≤ eR seed (ι (b)) := by rw [← ι_eV]; exact ι_nonneg _
  have heq : eR seed (ι (b)) < qR ν (ι (b)) ^ 2 := by
    rw [← ι_eV, ← ι_qV, ← map_pow]
    exact ι_lt_ι.mpr (eV_lt seed hyb)
  have hlam : qV ν (b) ^ 2 ≤ lamV ν (b) := by
    rw [qV_pow, lamV]
    exact Finset.single_le_sum (f := fun i => (b ^ 5) ^ i)
      (fun _ _ => Arithmetic.zero_le _) (Finset.mem_range.mpr h24)
  have hq2 : qR ν (ι (b)) ^ 2 ≤ lamR ν (ι (b)) := by
    rw [← ι_qV, ← map_pow, ← ι_lamV]
    exact ι_le_ι.mpr hlam
  have hz : (1 : DiffRing V) ≤ indexZ seed 0 := by linarith
  have hc0 : (0 : DiffRing V) ≤ 1 + 1 * ι (b) ^ 5 + ι g := by
    have := pow_nonneg (ι_nonneg (b)) 5
    have := ι_nonneg g
    linarith
  have hcq : 1 + 1 * ι (b) ^ 5 + ι g ≤ qR ν (ι (b)) := by
    have h := ι_le_ι.mpr (c_le_q seed hyb hg)
    rw [map_add, map_add, map_one, map_pow, ι_qV] at h
    linarith
  have hzB : 2 * (indexZ seed 0 : DiffRing V) ≤ ι (b) ^ 5 := by
    have h := ι_le_ι.mpr hZB
    rw [map_natCast, map_pow] at h
    push_cast at h
    exact h
  have hgeom : (ι (b) ^ 5 - 1) * lamR ν (ι (b)) + 1 =
      qR ν (ι (b)) ^ 4 := by
    unfold lamR qR
    rw [ModelCoding.geom_identity, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    simp only [codingL4]
    ring
  have hBR2 : (2 : DiffRing V) ≤ ι (b) ^ 5 := by
    have h := ι_le_ι.mpr hB2
    simp only [map_pow, map_ofNat] at h
    exact h
  have hq5 : (5 : DiffRing V) ≤ qR ν (ι (b)) := by
    have hBq : b ^ 5 ≤ qV ν (b) := by
      rw [qV_eq]
      calc b ^ 5 = (b ^ 5) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hB1 hL1
    have h := ι_le_ι.mpr (le_trans hbB hBq)
    rw [ι_qV] at h
    linarith
  unfold thirdR
  exact ModelCoding.third_bounds _ _ _ _ _ _ he heq hq2 hz hc0 hcq hzB hgeom hBR2 hq5

end Sizes

/-! ### The packed code -/

section Packed
variable {ν : ℕ} (seed : Expr (Fin (ν + 1)))

theorem ι_S3V {b g : V} (hyb : (indexY seed 0 : V) < b)
    (hg : g < 4 * b * (b ^ 5) ^ (5 ^ ν)) :
    ι (S3V seed (b) g) = thirdR seed (ι (b)) (ι g) :=
  ι_toV (third_ok seed hyb hg).1

theorem ι_DV {b : V} (hyb : (indexY seed 0 : V) < b) :
    ι (DV (b)) = ι (b) ^ 5 - 2 := by
  obtain ⟨h9, -, -, -, -⟩ := dr_base seed hyb
  have h : (0 : DiffRing V) ≤ ι (b) ^ 5 - 2 := by
    have h4 := pow_le_pow_left₀ (by norm_num : (0 : DiffRing V) ≤ 9) h9 5
    have e : (9 : DiffRing V) ^ 5 = 59049 := by norm_num
    rw [e] at h4
    linarith
  exact ι_toV h

/-- **(U21)–(U24) at `x = 1`.** The packed code is the rank code of the evaluated quantities. -/
theorem RV_rank {b g : V} (hyb : (indexY seed 0 : V) < b)
    (hg : g < 4 * b * (b ^ 5) ^ (5 ^ ν)) :
    ι (RV seed (b) g) =
      NinePolynomial.rankCode (1 : DiffRing V) (indexZ seed 0 : DiffRing V) (ι (b))
        (eR seed (ι (b))) (ι g) (lR ν (ι (b))) (qR ν (ι (b)) ^ 16)
        (qR ν (ι (b))) (ι (b) ^ 5 - 2 * (indexZ seed 0 : DiffRing V))
        (lamR ν (ι (b))) := by
  obtain ⟨hb1, -, -, hZB, -⟩ := v_base seed hyb
  have hn : 1 ≤ qV ν (b) ^ 16 := by
    have h1 : 1 ≤ qV ν (b) := by
      rw [qV_eq]
      exact one_le_pow₀ (le_trans hb1 (self_le_pow_five hb1))
    exact one_le_pow₀ h1
  have hS : ι (S3V seed (b) g) =
      2 * (ι (eV seed (b)) - ι ((indexZ seed 0 : ℕ) : V) * ι (lamV ν (b))) *
          (1 + ι (1 : V) * ι (b) ^ 5 + ι g) ^ 4 +
        ι (lamV ν (b)) * ι (b) ^ 5 +
        ι (lamV ν (b)) * ι (b) ^ 5 * ι (qV ν (b)) ^ 4 := by
    rw [ι_S3V seed hyb hg, map_one, map_natCast, ι_eV, ι_lamV, ι_qV]
    rfl
  have hM : ι (M1V ν (b)) =
      ι (qV ν (b)) ^ 3 - 1 - (ι (b) - 1) * ι (lV ν (b)) := by
    rw [ι_M1V ν hb1 (M1_ok seed hyb), ι_qV, ι_lV]
  have h := ι_centralCode_eq_rankCode (x := (1 : V)) (z := ((indexZ seed 0 : ℕ) : V))
    (b := b) (e := eV seed (b)) (g := g) (l := lV ν (b))
    (n := qV ν (b) ^ 16) (q := qV ν (b)) (θ := θV seed (b))
    (lam := lamV ν (b)) (S₃ := S3V seed (b) g) (M₁ := M1V ν (b))
    (D := DV (b)) hn hS hM (ι_DV seed hyb)
  unfold RV
  rw [h, map_one, map_natCast, ι_eV, ι_lV, map_pow, ι_qV, ι_θV seed hZB, ι_lamV]

/-- **(U18)–(U24)**: the three carry tests hold iff `(q¹⁶)² ∣ binom (2R) R`. -/
theorem pack_iff {k g : V} (hyb : (indexY seed 0 : V) < Exp.exp k)
    (hg : g < 4 * Exp.exp k * (Exp.exp k ^ 5) ^ (5 ^ ν)) :
    (NoCarry g (M1V ν (Exp.exp k)) ∧
      NoCarry (eV seed (Exp.exp k) + lV ν (Exp.exp k) * qV ν (Exp.exp k) ^ 2)
        (θV seed (Exp.exp k) * lamV ν (Exp.exp k)) ∧
      NoCarry (S3V seed (Exp.exp k) g) (DV (Exp.exp k) * qV ν (Exp.exp k))) ↔
      (qV ν (Exp.exp k) ^ 16) ^ 2 ∣
        binom (2 * RV seed (Exp.exp k) g) (RV seed (Exp.exp k) g) := by
  obtain ⟨hb1, hbB, -, -, hB2⟩ := v_base seed hyb
  have hB1 : 1 ≤ Exp.exp k ^ 5 := le_trans hb1 hbB
  obtain ⟨hL1, -, -, -, -, -, -, -⟩ := L_facts ν
  -- the six block bounds
  have hS₁ := g_lt_q3 seed hyb hg
  have hq3pos : 0 < qV ν (Exp.exp k) ^ 3 := (Arithmetic.zero_le g).trans_lt hS₁
  have hT₁ : M1V ν (Exp.exp k) < qV ν (Exp.exp k) ^ 3 :=
    lt_of_le_of_lt tsub_le_self (tsub_lt_self hq3pos one_pos)
  have hS₂ := block2_lt seed hyb
  have hT₂ := block2'_lt seed hyb
  have hS₃ : S3V seed (Exp.exp k) g < qV ν (Exp.exp k) ^ 9 := by
    apply ι_lt_ι.mp
    rw [ι_S3V seed hyb hg, map_pow, ι_qV]
    exact (third_ok seed hyb hg).2
  have hT₃ : DV (Exp.exp k) * qV ν (Exp.exp k) < qV ν (Exp.exp k) ^ 9 := by
    apply ι_lt_ι.mp
    rw [map_mul, map_pow, ι_DV seed hyb, ι_qV]
    have hBq : Exp.exp k ^ 5 ≤ qV ν (Exp.exp k) := by
      rw [qV_eq]
      calc Exp.exp k ^ 5 = (Exp.exp k ^ 5) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hB1 hL1
    have h1 := ι_le_ι.mpr hBq
    rw [map_pow, ι_qV] at h1
    have h9 := (dr_base seed hyb).1
    have h5 := pow_le_pow_left₀ (by norm_num : (0 : DiffRing V) ≤ 9) h9 5
    have e5 : (9 : DiffRing V) ^ 5 = 59049 := by norm_num
    rw [e5] at h5
    have hq0 : (0 : DiffRing V) < qR ν (ι (Exp.exp k)) := by linarith
    have h2 : (ι (Exp.exp k) ^ 5 - 2) * qR ν (ι (Exp.exp k)) <
        qR ν (ι (Exp.exp k)) * qR ν (ι (Exp.exp k)) :=
      mul_lt_mul_of_pos_right (by linarith) hq0
    have h3 : qR ν (ι (Exp.exp k)) ^ 2 ≤ qR ν (ι (Exp.exp k)) ^ 9 :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have e : qR ν (ι (Exp.exp k)) * qR ν (ι (Exp.exp k)) = qR ν (ι (Exp.exp k)) ^ 2 := by ring
    linarith
  -- `q` is a power of two
  obtain ⟨t, ht⟩ := pow_exp_exists k 5
  obtain ⟨κq, hκq⟩ := pow_exp_exists t (codingLexp ν 4)
  have hq : qV ν (Exp.exp k) = Exp.exp κq := by rw [qV_eq, ht, hκq]
  rw [hq] at hS₁ hT₁ hS₂ hT₂ hS₃ hT₃
  unfold RV
  rw [hq]
  exact pack3_carries_iff_dvd hS₁ hT₁ hS₂ hT₂ hS₃ hT₃

end Packed

/-! ### The three tests -/

section Tests
variable {ν : ℕ} (seed : Expr (Fin (ν + 1)))

theorem M1V_eq (ν : ℕ) {k t : V} (ht : Exp.exp k ^ 5 = Exp.exp t) :
    M1V ν (Exp.exp k) = Exp.exp t ^ (3 * codingLexp ν 4) - 1 -
      (Exp.exp k - 1) * ∑ i ∈ Finset.range ν, Exp.exp t ^ (5 ^ (i + 1)) := by
  unfold M1V qV lV
  rw [ht, ← pow_mul, mul_comm (codingL4 ν) 3]

/-- **(4.8), necessity**: a code of digits `< b` passes the test, and `g < b B^(5^ν)`. -/
theorem tau1_of_code (ν : ℕ) {k : V} (w : Fin ν → V) (hw : ∀ i, w i < Exp.exp k) :
    NoCarry (gOf ν w (Exp.exp k ^ 5)) (M1V ν (Exp.exp k)) ∧
      gOf ν w (Exp.exp k ^ 5) < Exp.exp k * (Exp.exp k ^ 5) ^ (5 ^ ν) := by
  obtain ⟨t, ht⟩ := pow_exp_exists k 5
  have hbB : Exp.exp k ≤ Exp.exp t := by rw [← ht]; exact self_le_pow_five (one_le_exp k)
  have hkt : k ≤ t := exp_monotone_le.mp hbB
  have hB : 0 < Exp.exp t := exp_pos t
  obtain ⟨-, -, -, -, -, h3, -, -⟩ := L_facts ν
  have ha : ∀ i < ν, extN w i < Exp.exp k := fun i hi => by
    simp only [extN, dif_pos hi]
    exact hw _
  have hF : ∀ j, spread ν (extN w) j < Exp.exp k := spread_lt ν _ (exp_pos k) ha
  have hFB : ∀ j < 3 * codingLexp ν 4, spread ν (extN w) j < Exp.exp t :=
    fun j _ => lt_of_lt_of_le (hF j) hbB
  have hg3 : gOf ν w (Exp.exp t) = dsum (Exp.exp t) (spread ν (extN w)) (3 * codingLexp ν 4) := by
    rw [gOf_eq, dsum_spread ν _ _ _ h3]
  have hg1 : gOf ν w (Exp.exp t) = dsum (Exp.exp t) (spread ν (extN w)) (5 ^ ν + 1) := by
    rw [gOf_eq, dsum_spread ν _ _ _ (by omega)]
  rw [ht]
  constructor
  · have hlt : gOf ν w (Exp.exp t) < Exp.exp t ^ (3 * codingLexp ν 4) := by
      rw [hg3]; exact dsum_lt _ _ _ hFB
    rw [M1V_eq ν ht, noCarry_M1_iff hkt (N := 3 * codingLexp ν 4) h3 (posν ν) (fun j => Iff.rfl)
      (gOf ν w (Exp.exp t)) hlt]
    intro j hj
    rw [hg3, dsum_digit _ hB _ _ hFB j hj]
    exact ⟨fun _ => hF j, fun hp => spread_off ν _ j hp⟩
  · rw [hg1]
    exact dsum_lt_mul hbB (fun i _ => hF i)

/-- **(4.8), sufficiency**: a number `g < q³` passing the test is a code of digits `< b`. -/
theorem code_of_tau1 (ν : ℕ) {k g : V} (hg : g < qV ν (Exp.exp k) ^ 3)
    (h : NoCarry g (M1V ν (Exp.exp k))) :
    ∃ w : Fin ν → V, (∀ i, w i < Exp.exp k) ∧ g = gOf ν w (Exp.exp k ^ 5) := by
  obtain ⟨t, ht⟩ := pow_exp_exists k 5
  have hbB : Exp.exp k ≤ Exp.exp t := by rw [← ht]; exact self_le_pow_five (one_le_exp k)
  have hkt : k ≤ t := exp_monotone_le.mp hbB
  obtain ⟨-, -, -, -, -, h3, -, -⟩ := L_facts ν
  have hq3 : qV ν (Exp.exp k) ^ 3 = Exp.exp t ^ (3 * codingLexp ν 4) := by
    rw [qV_pow, ht]
  rw [M1V_eq ν ht] at h
  rw [hq3] at hg
  have hd := (noCarry_M1_iff hkt (N := 3 * codingLexp ν 4) h3 (posν ν) (fun j => Iff.rfl)
    g hg).mp h
  refine ⟨fun i => g / Exp.exp t ^ (5 ^ ((i : ℕ) + 1)) % Exp.exp t, fun i => ?_, ?_⟩
  · have hi : 5 ^ ((i : ℕ) + 1) < 3 * codingLexp ν 4 := by
      have : 5 ^ ((i : ℕ) + 1) ≤ 5 ^ ν := Nat.pow_le_pow_right (by omega) i.isLt
      omega
    exact (hd _ hi).1 ⟨i, i.isLt, rfl⟩
  · rw [ht]
    have he := eq_sum_of_code (N := 3 * codingLexp ν 4) h3 (posν ν) (fun j => Iff.rfl) g hg
      (fun j hj hp => (hd j hj).2 hp)
    calc g = ∑ i ∈ Finset.range ν,
          (g / Exp.exp t ^ (5 ^ (i + 1)) % Exp.exp t) * Exp.exp t ^ (5 ^ (i + 1)) := he
      _ = gOf ν (fun i => g / Exp.exp t ^ (5 ^ ((i : ℕ) + 1)) % Exp.exp t) (Exp.exp t) :=
          (Fin.sum_univ_eq_sum_range
            (fun i => (g / Exp.exp t ^ (5 ^ (i + 1)) % Exp.exp t) * Exp.exp t ^ (5 ^ (i + 1)))
            ν).symm

theorem mask_add (B Z : V) (m n : ℕ) : mask B Z (m + n) = mask B Z m + mask B Z n * B ^ m := by
  simp only [mask, dsum]
  rw [Finset.sum_range_add, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pow_add]
  ring

/-- **(4.4) holds** for the explicit `e`, `l`: their digits are `< 2z`. -/
theorem tau2_holds {k : V} (hyb : (indexY seed 0 : V) < Exp.exp k) :
    NoCarry (eV seed (Exp.exp k) + lV ν (Exp.exp k) * qV ν (Exp.exp k) ^ 2)
      (θV seed (Exp.exp k) * lamV ν (Exp.exp k)) := by
  obtain ⟨-, -, -, hZB, hB2⟩ := v_base seed hyb
  obtain ⟨-, -, -, -, h2, -, -, h24⟩ := L_facts ν
  obtain ⟨t, ht⟩ := pow_exp_exists k 5
  have hs := two_z_eq_exp (V := V) seed
  have hst : ((indexExponent seed 0 + 1 : ℕ) : V) ≤ t :=
    exp_monotone_le.mp (by rw [← hs, ← ht]; exact hZB)
  have hB : 0 < Exp.exp t := exp_pos t
  have hZ8 : (2 : V) ≤ Exp.exp ((indexExponent seed 0 + 1 : ℕ) : V) := by
    rw [← hs]
    have := ModelCoding.four_le_indexZ seed
    exact_mod_cast (show 2 ≤ 2 * indexZ seed 0 by omega)
  have hZB' : Exp.exp ((indexExponent seed 0 + 1 : ℕ) : V) ≤ Exp.exp t :=
    exp_monotone_le.mpr hst
  -- `e` and `l` as digit numbers
  have he : eV seed (Exp.exp k) = dsum (Exp.exp t) (ecV seed) (2 * codingLexp ν 4) := by
    unfold eV
    rw [ht]
  have hecZ : ∀ i, ecV seed i < Exp.exp ((indexExponent seed 0 + 1 : ℕ) : V) := fun i => by
    rw [← hs]
    exact ecV_lt seed i
  have heB : ∀ i < 2 * codingLexp ν 4, ecV seed i < Exp.exp t :=
    fun i _ => lt_of_lt_of_le (hecZ i) hZB'
  have hl : lV ν (Exp.exp k) = dsum (Exp.exp t) (codeInd (posν ν)) (2 * codingLexp ν 4) := by
    unfold lV
    rw [ht]
    exact lV_eq_dsum ν _ _ h2
  have hlZ : ∀ i, (codeInd (posν ν) i : V) < Exp.exp ((indexExponent seed 0 + 1 : ℕ) : V) :=
    fun i => lt_of_le_of_lt (codeInd_le_one _ i) (lt_of_lt_of_le one_lt_two hZ8)
  have hlB : ∀ i < 2 * codingLexp ν 4, (codeInd (posν ν) i : V) < Exp.exp t :=
    fun i _ => lt_of_lt_of_le (hlZ i) hZB'
  -- the mask
  have hq2 : qV ν (Exp.exp k) ^ 2 = Exp.exp t ^ (2 * codingLexp ν 4) := by rw [qV_pow, ht]
  have hthetalam : θV seed (Exp.exp k) * lamV ν (Exp.exp k) =
      mask (Exp.exp t) (Exp.exp ((indexExponent seed 0 + 1 : ℕ) : V)) (2 * codingLexp ν 4) +
        mask (Exp.exp t) (Exp.exp ((indexExponent seed 0 + 1 : ℕ) : V)) (2 * codingLexp ν 4) *
          qV ν (Exp.exp k) ^ 2 := by
    rw [hq2, ← mask_add, show 2 * codingLexp ν 4 + 2 * codingLexp ν 4 = 4 * codingLexp ν 4 by
      omega]
    unfold θV lamV
    rw [ht, hs, Finset.mul_sum]
    simp only [mask, dsum]
  have hel : eV seed (Exp.exp k) < Exp.exp t ^ (2 * codingLexp ν 4) := by
    rw [he]; exact dsum_lt _ _ _ heB
  have hml : mask (Exp.exp t) (Exp.exp ((indexExponent seed 0 + 1 : ℕ) : V)) (2 * codingLexp ν 4) <
      Exp.exp t ^ (2 * codingLexp ν 4) :=
    dsum_lt _ _ _ (fun _ _ => tsub_lt_self hB (exp_pos _))
  obtain ⟨K, hK⟩ := pow_exp_exists t (2 * codingLexp ν 4)
  have hne : NoCarry (eV seed (Exp.exp k))
      (mask (Exp.exp t) (Exp.exp ((indexExponent seed 0 + 1 : ℕ) : V)) (2 * codingLexp ν 4)) := by
    rw [noCarry_mask_iff hst, he]
    intro j hj
    rw [dsum_digit _ hB _ _ heB j hj]
    exact hecZ j
  have hnl : NoCarry (lV ν (Exp.exp k))
      (mask (Exp.exp t) (Exp.exp ((indexExponent seed 0 + 1 : ℕ) : V)) (2 * codingLexp ν 4)) := by
    rw [noCarry_mask_iff hst, hl]
    intro j hj
    rw [dsum_digit _ hB _ _ hlB j hj]
    exact hlZ j
  have hc := (noCarry_concat (k := K) (S₁ := eV seed (Exp.exp k)) (S₂ := lV ν (Exp.exp k))
    (T₁ := mask (Exp.exp t) (Exp.exp ((indexExponent seed 0 + 1 : ℕ) : V)) (2 * codingLexp ν 4))
    (T₂ := mask (Exp.exp t) (Exp.exp ((indexExponent seed 0 + 1 : ℕ) : V)) (2 * codingLexp ν 4))
    (by rw [← hK]; exact hel) (by rw [← hK]; exact hml)).mp ⟨hne, hnl⟩
  rw [← hK, ← hq2] at hc
  rw [hthetalam]
  exact hc

/-- **(4.10)–(4.11)**: for the code `g` of `(1, w)` with `wᵢ < b`,
`NoCarry S₃ T₃ ↔ P(1, w) = 0`. -/
theorem tau3_iff (hP : seed.toPolynomial.totalDegree ≤ 4) {k : V}
    (hyb : (indexY seed 0 : V) < Exp.exp k) (w : Fin ν → V) (hw : ∀ i, w i < Exp.exp k) :
    NoCarry (S3V seed (Exp.exp k) (gOf ν w (Exp.exp k ^ 5))) (DV (Exp.exp k) * qV ν (Exp.exp k)) ↔
      seed.evalRing (zsOf w) = 0 := by
  obtain ⟨h9, -, hzb, hz4, -⟩ := dr_base seed hyb
  obtain ⟨-, -, -, -, hB2⟩ := v_base seed hyb
  obtain ⟨hL1, -, -, -, -, -, h18, -⟩ := L_facts ν
  obtain ⟨t, ht⟩ := pow_exp_exists k 5
  -- `B = 2^(κ+1)`
  obtain ⟨κ, hκ⟩ : ∃ κ, Exp.exp k ^ 5 = Exp.exp (κ + 1) := by
    rcases zero_or_succ t with h0 | ⟨κ, hκ⟩
    · exfalso
      rw [ht, h0, exp_zero] at hB2
      exact absurd hB2 (not_le.mpr one_lt_two)
    · exact ⟨κ, by rw [ht, hκ]⟩
  have hBR : ι (Exp.exp k) ^ 5 = 2 * ι (Exp.exp κ) := by
    rw [← map_pow, hκ, exp_succ]
    simp only [map_mul, map_ofNat]
  have hιB : ι (Exp.exp (κ + 1)) = ι (Exp.exp k) ^ 5 := by rw [← hκ, map_pow]
  have hz0 : (0 : DiffRing V) < indexZ seed 0 := by linarith
  have hz2 : 2 ≤ indexZ seed 0 := le_trans (by omega) (ModelCoding.four_le_indexZ seed)
  -- the code `c = 1 + B + g`
  have hc := (cval_cons w (Exp.exp k ^ 5)).symm
  rw [map_pow] at hc
  have hthird : thirdR seed (ι (Exp.exp k)) (ι (gOf ν w (Exp.exp k ^ 5))) =
      2 * ∑ i ∈ Finset.range (8 * codingLexp ν 4),
        (ModelCoding.hcoef seed (indexZ seed 0) (zsOf w) i + ι (Exp.exp κ)) *
          (ι (Exp.exp k) ^ 5) ^ i := by
    unfold thirdR eR lamR qR
    rw [hc]
    exact ModelCoding.third_eq seed (indexZ seed 0) (zsOf w) _ _ hBR
  -- `|hᵢ| < B/2`
  have hzsb : ∀ j, zsOf w j + 1 ≤ ι (Exp.exp k) := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [zsOf, Fin.cons_zero, map_one]
      linarith
    · simp only [zsOf, Fin.cons_succ]
      have h := ι_le_ι.mpr (lt_iff_succ_le.mp (hw i))
      rwa [map_add, map_one] at h
  have habs : ∀ i, |ModelCoding.hcoef seed (indexZ seed 0) (zsOf w) i| < ι (Exp.exp κ) := by
    intro i
    have h1 := ModelCoding.abs_hcoef_le seed (ModelCoding.index_big' seed) hz2
      (zs := zsOf w) (fun j => ι_nonneg _) i
    have h2 := ModelCoding.code_bound (indexZ seed 0 : DiffRing V) (ι (Exp.exp k)) (zsOf w)
      (fun j => ι_nonneg _) hzsb hz0 hzb (by linarith)
    linarith
  -- the digits `hᵢ + B/2`
  have hd_nonneg : ∀ i, 0 ≤ ModelCoding.hcoef seed (indexZ seed 0) (zsOf w) i + ι (Exp.exp κ) :=
    fun i => by have := (abs_lt.mp (habs i)).1; linarith
  obtain ⟨d, hd_def⟩ : ∃ d : ℕ → V, ∀ i,
      d i = toV (ModelCoding.hcoef seed (indexZ seed 0) (zsOf w) i + ι (Exp.exp κ)) :=
    ⟨fun i => toV (ModelCoding.hcoef seed (indexZ seed 0) (zsOf w) i + ι (Exp.exp κ)),
      fun _ => rfl⟩
  have hι_d : ∀ i, ι (d i) = ModelCoding.hcoef seed (indexZ seed 0) (zsOf w) i + ι (Exp.exp κ) :=
    fun i => by rw [hd_def]; exact ι_toV (hd_nonneg i)
  have hιE2 : ι (Exp.exp (κ + 1)) = 2 * ι (Exp.exp κ) := by rw [hιB, hBR]
  have hd0 : ∀ i < 8 * codingLexp ν 4, 0 < d i := fun i _ => by
    apply ι_lt_ι.mp
    rw [map_zero, hι_d]
    have := (abs_lt.mp (habs i)).1
    linarith
  have hd : ∀ i < 8 * codingLexp ν 4, d i < Exp.exp (κ + 1) := fun i _ => by
    apply ι_lt_ι.mp
    rw [hι_d, hιE2]
    have := (abs_lt.mp (habs i)).2
    linarith
  -- `S₃` and `T₃` in the form of the digit test
  have hth0 : 0 ≤ thirdR seed (ι (Exp.exp k)) (ι (gOf ν w (Exp.exp k ^ 5))) := by
    rw [hthird]
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (hd_nonneg i) (pow_nonneg (pow_nonneg (ι_nonneg _) 5) i))
  have hS3 : S3V seed (Exp.exp k) (gOf ν w (Exp.exp k ^ 5)) =
      2 * dsum (Exp.exp (κ + 1)) d (8 * codingLexp ν 4) := by
    apply ι_injective
    rw [S3V, ι_toV hth0, hthird]
    simp only [map_mul, map_ofNat]
    rw [ι_dsum, hιB]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [hι_d])
  have hT : DV (Exp.exp k) * qV ν (Exp.exp k) =
      2 * ((Exp.exp κ - 1) * Exp.exp (κ + 1) ^ codingLexp ν 4) := by
    apply ι_injective
    have hE1 : ι (Exp.exp κ - 1) = ι (Exp.exp κ) - 1 := by
      rw [ι_tsub (one_le_exp κ), map_one]
    simp only [map_mul, map_pow, map_ofNat, ι_DV seed hyb, hE1, ι_qV, hιB]
    unfold qR
    rw [hBR]
    ring
  rw [hS3, hT, noCarry_shifted_iff (show codingLexp ν 4 < 8 * codingLexp ν 4 from h18) d hd0 hd]
  have hhL := ModelCoding.hcoef_L seed hP (indexZ seed 0) (zsOf w)
  constructor
  · intro h
    have h1 : ι (d (codingLexp ν 4)) = ι (Exp.exp κ) := by rw [h]
    rw [hι_d] at h1
    have h2 : ModelCoding.hcoef seed (indexZ seed 0) (zsOf w) (codingLexp ν 4) = 0 := by linarith
    rw [hhL] at h2
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  · intro h
    apply ι_injective
    rw [hι_d, hhL, h]
    ring

end Tests

end DiophantineConsistency.ModelMaster
