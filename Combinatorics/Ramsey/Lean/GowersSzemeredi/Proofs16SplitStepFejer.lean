import GowersSzemeredi.Proofs16SplitStepBounds
import GowersSzemeredi.Proofs16ClassStepDegreesFejer
import GowersSzemeredi.Proofs16SplitFejerDegrees
import GowersSzemeredi.Proofs16UniformCoverTwoFejer

/-! **Split uniform classes in every dimension under the Fejér θ₁ and the
tight radius** (Notes L.16d).

The Fejér instance of `Proofs16SplitStepBounds` and
`Proofs16SplitAllDimensions`. The step is generated from the corpus by a
script with a guard that no printed parameter survives:
* the parameter-side degrees `fsStepY … fsExpW`: the corpus's with
  `fejerStepP k = 64F`, `fejerStepT k = 22F + 105` in place of
  `stepP k`, `stepT k`, where `F = fejerProductExponent k`. The family-side
  degrees (`sQrN … sExpN`, `splitStepA`) do not see Section 16 and are
  reused;
* `split_count_le_fejer`, `split_exp_inv_le_fejer`;
* `splitUniformClass_succ_fejer`: the split step with family exponent
  `splitStepA k a` and parameter degree `splitStepDFejer k a D`.
  `splitStepDFejer_eq` identifies the latter with
  `splitStepDWith (fejerStepP k) (fejerStepT k) k a D`
  (`Proofs16SplitFejerDegrees`).

From the dimension-two seed `splitUniformClass_two_fejer` (`a = D = 2^46`),
`splitUniformClass_all_fejer` gives a split class in every dimension
`k ≥ 2` with degrees `splitPairWith (2^46) (2^46) k`. By
`split_pair_with_bounds_fourteen`, `log₂ D_k ≤ 22·2^k`
(`split_pair_fejer_bound`), against `75·2^k` (`split_pair_bounds`) for the
printed parameters. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The split degrees -/

def fsStepY (k a D : Nat) : Nat := a * (fejerStepP k + 1) + D * (fejerStepP k + k + 6)
def fsQrW (k a D : Nat) : Nat := fsStepY k a D * 2 ^ k
def fsSW (k a D : Nat) : Nat := fsQrW k a D + fejerStepP k + 8
def fsPbW (k a D : Nat) : Nat := a * (fejerStepP k + fsSW k a D + 1) + D * (fejerStepP k + 5)

/-- The parameter degree of the count of the next class. -/
def fsCountW (k a D : Nat) : Nat := fejerStepP k + 1 + 2 * fsSW k a D + 2 * fsPbW k a D

/-! ### Shared facts of the step -/

/-- The piece count `M = n·m` and the level-`k` bases, in the two bases. -/
theorem split_step_basics_fejer {k : Nat} {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let ν : Real := (n : Real) + 1
    let W := splitW V' theta gamma rho
    (((n * classPiecesFejer gamma theta k : Nat) : Real) ≤ ν ^ 1 * W ^ (fejerStepP k)) ∧
      (((n * classPiecesFejer gamma theta k : Nat) : Real) + 1 ≤ ν ^ 1 * W ^ (fejerStepP k + 1)) ∧
      (2 / (gamma * classBudgetW (fejerThetaOne theta gamma k) k) ≤ W ^ (fejerStepP k + 1)) ∧
      (2 / (section16Delta (fejerThetaOne theta gamma k) * classBudgetW (fejerThetaOne theta gamma k) k) ≤ W ^ (fejerStepP k + 1)) := by
  intro ν W
  obtain ⟨hw2, huw, hrw, hVw, hV'w⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hm := classPiecesFejer_le_gen k hg hg1 ht ht1
  have hgd := twoDiv_gamma_le_fejer k hg hg1 ht ht1
  have hdd := twoDiv_delta_le_fejer k hg hg1 ht ht1
  have hu0 : 0 ≤ 2 / (gamma * theta) := by linarith
  have lift : ∀ (x : Real) (j : Nat), x ≤ (2 / (gamma * theta)) ^ j → x ≤ W ^ j :=
    fun x j h => h.trans (pow_le_pow_left₀ hu0 huw j)
  have hmW := lift _ _ hm
  have hn : (n : Real) ≤ ν := by show (n : Real) ≤ (n : Real) + 1; linarith
  have hν : 1 ≤ ν := by show (1 : Real) ≤ (n : Real) + 1; have := Nat.cast_nonneg (α := Real) n; linarith
  have hM : ((n * classPiecesFejer gamma theta k : Nat) : Real) ≤ ν ^ 1 * W ^ (fejerStepP k) := by
    rw [Nat.cast_mul, pow_one]
    exact mul_le_mul hn hmW (Nat.cast_nonneg _) (le_trans zero_le_one hν)
  exact ⟨hM, tb_add_one hν hw2 hM, lift _ _ hgd, lift _ _ hdd⟩

/-! ### The remainder count, the samples and the slices -/

/-- **The remainder count, in two bases.** -/
theorem split_Qr_le_fejer {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    max (splitCnt V a D (classBudgetW (fejerThetaOne theta gamma k) k) gamma (n * classPiecesFejer gamma theta k)
        (rho / 8 / ((classVertexNum k : Real) + 1)))
      (((3 ^ (k + 1) * (n * classPiecesFejer gamma theta k)) : Nat) : Real) ≤
      ((n : Real) + 1) ^ a * splitW V' theta gamma rho ^ fsStepY k a D ∧
    clsQr (splitCnt V a D) k (n * classPiecesFejer gamma theta k) (classBudgetW (fejerThetaOne theta gamma k) k) gamma
      (rho / 8) ≤ ((n : Real) + 1) ^ sQrN k a * splitW V' theta gamma rho ^ fsQrW k a D := by
  obtain ⟨hw2, huw, hrw, hVw, hV'w⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, hM1, hgd, -⟩ := split_step_basics_fejer (k := k) hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hb, -⟩ := classBudgetW_pos_le k (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  have hPk := fejerStepP_ge k
  have hnv := classVertexNum_succ_le k
  set ν : Real := (n : Real) + 1 with hνdef
  set W := splitW V' theta gamma rho with hWdef
  set M := n * classPiecesFejer gamma theta k with hMdef
  set tS := classBudgetW (fejerThetaOne theta gamma k) k
  set P := fejerStepP k with hPdef
  clear_value W
  have hν : 1 ≤ ν := by rw [hνdef]; have := Nat.cast_nonneg (α := Real) n; linarith
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hnv0 : (0 : Real) < (classVertexNum k : Real) + 1 := by
    have := Nat.cast_nonneg (α := Real) (classVertexNum k); linarith only [this]
  have h3k : (((3 ^ (k + 1) * M) : Nat) : Real) ≤ ν ^ 1 * W ^ (2 * (k + 1) + P) := by
    rw [Nat.cast_mul]
    have h3 : ((3 ^ (k + 1) : Nat) : Real) ≤ W ^ (2 * (k + 1)) := by
      push_cast; rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by nlinarith only [hw2]) _
    have h := mul_le_mul h3 hM (Nat.cast_nonneg _) (pow_nonneg hW0 _)
    refine h.trans (le_of_eq ?_)
    rw [pow_add]; ring
  have hfac : max (splitCnt V a D tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)))
        (((3 ^ (k + 1) * M) : Nat) : Real) ≤ ν ^ a * W ^ fsStepY k a D := by
    unfold splitCnt
    have hc : (8 : Real) * ((classVertexNum k : Real) + 1) ≤ 2 ^ (k + 3) := by
      have h1 : ((classVertexNum k : Real) + 1) ≤ 2 ^ k := by exact_mod_cast hnv
      have h2 : (2 : Real) ^ (k + 3) = 2 ^ k * 8 := by rw [pow_add]; norm_num
      rw [h2]; linarith only [h1]
    have hbase : splitW V tS gamma (rho / (8 * ((classVertexNum k : Real) + 1))) ≤
        W ^ (P + (k + 3) + 3) :=
      split_level_base_le hw2 hV0 hVw hr hrw (mul_pos (by norm_num) hnv0) hc hg hb hgd
    rw [← div_div] at hbase
    have hscale : 0 < rho / 8 / ((classVertexNum k : Real) + 1) :=
      div_pos (div_pos hr (by norm_num)) hnv0
    have hsw0 := splitW_nonneg (V := V) (t := tS) hV0 hg hb hscale
    have hM10 : (0 : Real) ≤ (M : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) M; linarith
    have h1 := tb_pow hM10 hM1 a
    have h2 : splitW V tS gamma (rho / 8 / ((classVertexNum k : Real) + 1)) ^ D ≤
        ν ^ 0 * W ^ ((P + (k + 3) + 3) * D) := by
      rw [pow_zero, one_mul, pow_mul]
      exact pow_le_pow_left₀ hsw0 hbase D
    have h12 := tb_mul hν hW1 (pow_nonneg hM10 _) (pow_nonneg hsw0 _) h1 h2
    refine max_le (h12.trans (tb_mono hν hW1 (by omega)
      (le_of_eq (by unfold fsStepY; rw [← hPdef]; ring)))) ?_
    refine h3k.trans (tb_mono hν hW1 (by omega) ?_)
    have h1' : P + 1 ≤ a * (P + 1) := Nat.le_mul_of_pos_left _ ha
    have h2' : P + k + 6 ≤ D * (P + k + 6) := Nat.le_mul_of_pos_left _ hD
    unfold fsStepY
    rw [← hPdef]
    omega
  refine ⟨hfac, ?_⟩
  unfold clsQr
  have hfac1 : (1 : Real) ≤ ν ^ a * W ^ fsStepY k a D := tb_one_le hν hW1
  refine (Finset.prod_le_prod (g := fun _ => ν ^ a * W ^ fsStepY k a D)
    (fun i _ => le_max_of_le_right (Nat.cast_nonneg _)) (fun i _ => hfac)).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine (pow_le_pow_right₀ hfac1 hnv).trans (le_of_eq ?_)
  unfold sQrN fsQrW
  rw [mul_pow, ← pow_mul, ← pow_mul]

/-- **The sample count and the slice count, in two bases.** -/
theorem split_samples_le_fejer {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let M := n * classPiecesFejer gamma theta k
    let S := famPieceSamples (clsQr (splitCnt V a D) k M (classBudgetW (fejerThetaOne theta gamma k) k) gamma) M rho
    (S : Real) ≤ ((n : Real) + 1) ^ sSN k a * splitW V' theta gamma rho ^ fsSW k a D ∧
      1 ≤ (S : Real) ∧
      splitCnt V a D (classBudgetW (fejerThetaOne theta gamma k) k) gamma (M * S) (rho / 4) ≤
        ((n : Real) + 1) ^ sPbN k a * splitW V' theta gamma rho ^ fsPbW k a D ∧
      1 ≤ splitCnt V a D (classBudgetW (fejerThetaOne theta gamma k) k) gamma (M * S) (rho / 4) := by
  intro M S
  obtain ⟨hw2, huw, hrw, hVw, hV'w⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, hM1, hgd, -⟩ := split_step_basics_fejer (k := k) hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hb, hb1⟩ := classBudgetW_pos_le k (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  obtain ⟨-, hQr⟩ := split_Qr_le_fejer (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n
  set ν : Real := (n : Real) + 1 with hνdef
  set W := splitW V' theta gamma rho with hWdef
  set tS := classBudgetW (fejerThetaOne theta gamma k) k
  set P := fejerStepP k with hPdef
  clear_value W
  have hν : 1 ≤ ν := by rw [hνdef]; have := Nat.cast_nonneg (α := Real) n; linarith
  have hW1 : 1 ≤ W := by linarith
  have hV0 : 0 ≤ V := by linarith
  -- the samples
  have hS : (S : Real) ≤ ν ^ sSN k a * W ^ fsSW k a D := by
    show ((famPieceSamples (clsQr (splitCnt V a D) k M tS gamma) M rho : Nat) : Real) ≤ _
    unfold famPieceSamples
    set Q := clsQr (splitCnt V a D) k M tS gamma
    have hQ1 : max 1 (Q (rho / 8)) ≤ ν ^ sQrN k a * W ^ fsQrW k a D :=
      max_le (tb_one_le hν hW1) hQr
    have hM1' : ((max 1 M : Nat) : Real) ≤ ν ^ 1 * W ^ P := by
      rcases le_total 1 M with h | h
      · rw [max_eq_right h]; exact hM
      · rw [max_eq_left h]; exact_mod_cast tb_one_le hν hW1
    have hx0 : 0 ≤ 6 * max 1 (Q (rho / 8)) * ((max 1 M : Nat) : Real) / (rho / 4) := by
      have : (0 : Real) ≤ max 1 (Q (rho / 8)) := le_trans zero_le_one (le_max_left _ _)
      positivity
    have hval : 6 * max 1 (Q (rho / 8)) * ((max 1 M : Nat) : Real) / (rho / 4) =
        24 * (max 1 (Q (rho / 8)) * (((max 1 M : Nat) : Real) * rho⁻¹)) := by
      field_simp; ring
    have hinner : max 1 (Q (rho / 8)) * (((max 1 M : Nat) : Real) * rho⁻¹) ≤
        ν ^ (sQrN k a + 1) * W ^ (fsQrW k a D + (P + 1)) := by
      have hr' : rho⁻¹ ≤ ν ^ 0 * W ^ 1 := by rw [pow_zero, one_mul, pow_one]; exact hrw
      have h1 := tb_mul hν hW1 (by positivity) (inv_pos.mpr hr).le hM1' hr'
      exact tb_mul hν hW1 (le_trans zero_le_one (le_max_left _ _)) (by positivity) hQ1 h1
    have hx : 6 * max 1 (Q (rho / 8)) * ((max 1 M : Nat) : Real) / (rho / 4) ≤
        ν ^ (sQrN k a + 1) * W ^ (5 + (fsQrW k a D + (P + 1))) := by
      rw [hval]
      exact tb_const_mul hν hw2 (by norm_num) (by norm_num) (by positivity) hinner
    have hceil := Nat.ceil_lt_add_one hx0
    have h2 := tb_add_one hν hw2 hx
    calc ((⌈6 * max 1 (Q (rho / 8)) * ((max 1 M : Nat) : Real) / (rho / 4)⌉₊ : Nat) : Real)
        ≤ 6 * max 1 (Q (rho / 8)) * ((max 1 M : Nat) : Real) / (rho / 4) + 1 := hceil.le
      _ ≤ ν ^ (sQrN k a + 1) * W ^ (5 + (fsQrW k a D + (P + 1)) + 1) := h2
      _ ≤ ν ^ sSN k a * W ^ fsSW k a D := tb_mono hν hW1 (by unfold sSN; omega)
          (by unfold fsSW; rw [← hPdef]; omega)
  have hS1 : (1 : Real) ≤ (S : Real) := by
    have h0 : 0 < S := famPieceSamples_pos (Qr := clsQr (splitCnt V a D) k M tS gamma) (n := M) hr
    exact Nat.one_le_cast.mpr h0
  -- the slice count
  have hMS : ((M * S : Nat) : Real) + 1 ≤ ν ^ (1 + sSN k a) * W ^ (P + fsSW k a D + 1) := by
    have h := tb_mul hν hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hM hS
    rw [← Nat.cast_mul] at h
    exact tb_add_one hν hw2 h
  have hbase : splitW V tS gamma (rho / 4) ≤ W ^ (P + 2 + 3) :=
    split_level_base_le hw2 hV0 hVw hr hrw (by norm_num) (by norm_num) hg hb hgd
  have hMS0 : (0 : Real) ≤ ((M * S : Nat) : Real) + 1 := by
    have := Nat.cast_nonneg (α := Real) (M * S); linarith
  have hsw0 := splitW_nonneg (V := V) (t := tS) hV0 hg hb (by positivity : (0 : Real) < rho / 4)
  refine ⟨hS, hS1, ?_, ?_⟩
  · unfold splitCnt
    have h1 := tb_pow hMS0 hMS a
    have h2 : splitW V tS gamma (rho / 4) ^ D ≤ ν ^ 0 * W ^ ((P + 2 + 3) * D) := by
      rw [pow_zero, one_mul, pow_mul]
      exact pow_le_pow_left₀ hsw0 hbase D
    have h12 := tb_mul hν hW1 (pow_nonneg hMS0 _) (pow_nonneg hsw0 _) h1 h2
    push_cast at h12 ⊢
    refine h12.trans (tb_mono hν hW1 (le_of_eq (by unfold sPbN; ring))
      (le_of_eq (by unfold fsPbW; rw [← hPdef]; ring)))
  · unfold splitCnt
    obtain ⟨h2, -, -, -⟩ := splitW_facts hV hg hg1 hb hb1
      (by positivity : (0 : Real) < rho / 4) (by linarith only [hr1])
    have hMS1 : (1 : Real) ≤ ((M * S : Nat) : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) (M * S); linarith
    push_cast at hMS1 ⊢
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hMS1) (one_le_pow₀ (by linarith))

/-! ### The count -/

/-- **The count of the next class, in two bases.** -/
theorem split_count_le_fejer {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    max (famPieceGraphBound
        (clsQr (splitCnt V a D) k (n * classPiecesFejer gamma theta k) (classBudgetW (fejerThetaOne theta gamma k) k) gamma)
        (clsPb (splitCnt V a D) (n * classPiecesFejer gamma theta k) (classBudgetW (fejerThetaOne theta gamma k) k) gamma)
        (n * classPiecesFejer gamma theta k) rho)
      (((3 ^ (k + 1) * (n * classPiecesFejer gamma theta k)) : Nat) : Real) ≤
      ((n : Real) + 1) ^ sCountN k a * splitW V' theta gamma rho ^ fsCountW k a D := by
  obtain ⟨hw2, huw, hrw, hVw, hV'w⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, -, -, -⟩ := split_step_basics_fejer (k := k) hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hfac, -⟩ := split_Qr_le_fejer (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hS, hS1, hPb, hPb1⟩ := split_samples_le_fejer (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n
  set ν : Real := (n : Real) + 1 with hνdef
  set W := splitW V' theta gamma rho with hWdef
  set M := n * classPiecesFejer gamma theta k with hMdef
  set tS := classBudgetW (fejerThetaOne theta gamma k) k
  set S := famPieceSamples (clsQr (splitCnt V a D) k M tS gamma) M rho with hSdef
  clear_value W
  have hν : 1 ≤ ν := by rw [hνdef]; have := Nat.cast_nonneg (α := Real) n; linarith
  have hW1 : 1 ≤ W := by linarith
  have hG : famPieceGraphBound (clsQr (splitCnt V a D) k M tS gamma) (clsPb (splitCnt V a D) M tS gamma)
      M rho ≤ ν ^ (1 + (2 * sSN k a + 2 * sPbN k a)) *
        W ^ (fejerStepP k + (2 * fsSW k a D + 2 * fsPbW k a D)) := by
    have hPbv : clsPb (splitCnt V a D) M tS gamma S (rho / 4) =
        splitCnt V a D tS gamma (M * S) (rho / 4) := by
      unfold clsPb; rw [abs_of_pos (by positivity : (0 : Real) < rho / 4)]
    have h := famPieceGraphBound_le_mul_sq (Pb := clsPb (splitCnt V a D) M tS gamma)
      (tb_one_le hν hW1) (tb_one_le hν hW1) hM hS
      (by rw [← hSdef, hPbv]; exact zero_le_one.trans hPb1)
      (by rw [← hSdef, hPbv]; exact hPb)
    convert h using 1 <;> ring
  have h3k := (le_max_right _ _).trans hfac
  refine max_le (hG.trans (tb_mono hν hW1 (by unfold sCountN; omega) (by unfold fsCountW; omega))) ?_
  refine h3k.trans (tb_mono hν hW1 (by unfold sCountN sPbN; nlinarith) ?_)
  unfold fsCountW fsPbW fsSW fsQrW
  nlinarith [Nat.le_mul_of_pos_left (fsStepY k a D) (Nat.two_pow_pos k)]

/-! ### The width exponent -/

def fsEbW (k a D : Nat) : Nat := a * (fejerStepP k + 1) + D * (fejerStepP k + 6)
def fsErW (k a D : Nat) : Nat := (fsStepY k a D + 4) * 2 ^ k
def fsBqW (k a D : Nat) : Nat := 4 + (fsEbW k a D + 1) * 2 ^ (k + 2)
def fsLW (k a D : Nat) : Nat := fsBqW k a D + (fsErW k a D + fsEbW k a D)
def fsZW (k a D : Nat) : Nat := fejerStepT k + a + fsEbW k a D + 7

/-- The parameter degree of the width exponent of the next class. -/
def fsExpW (k a D : Nat) : Nat := fsZW k a D + fsLW k a D + fsPbW k a D + 6

def sPbN2 (k ac ae : Nat) : Nat := ae * (sSN k ac + 1)

def fsPbW2 (k ac Dc ae De : Nat) : Nat :=
  ae * (fejerStepP k + fsSW k ac Dc + 1) + De * (fejerStepP k + 5)

def sLN2 (k ac ae : Nat) : Nat := sBqN k ac + (sErN k ae + ae)

def fsLW2 (k ac Dc ae De : Nat) : Nat := fsBqW k ac Dc + (fsErW k ae De + fsEbW k ae De)

/-- The family exponent of the width exponent of the next two-track class. -/
def sExpN2 (k ac ae : Nat) : Nat := 1 + sLN2 k ac ae + sPbN2 k ac ae

/-- The parameter degree of the width exponent of the next two-track class. -/
def fsExpW2 (k ac Dc ae De : Nat) : Nat :=
  fsZW k ac Dc + fsLW2 k ac Dc ae De + fsPbW2 k ac Dc ae De + 6

/-- **The width exponent of the next class from a two-track class.** -/
theorem split_exp_inv_le_fejer2 {k ac Dc ae De : Nat} (hac : 1 ≤ ac) (hDc : 1 ≤ Dc) (hae : 1 ≤ ae)
    (hDe : 1 ≤ De) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p) (hKV : (K : Real) ≤ V')
    (hpV : (p : Real) ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let M := n * classPiecesFejer gamma theta k
    let tS := classBudgetW (fejerThetaOne theta gamma k) k
    let gS := section16Delta (fejerThetaOne theta gamma k)
    let e := section16CappedWidthExponent
        (pieceLineExponent (familyWidthDivisor k p) (splitCnt V ac Dc tS gS M)
            (splitExp V ae De tS gS M) (clsEr (splitExp V ae De) k M tS gamma) rho *
          famPieceSliceExponent (clsQr (splitCnt V ac Dc) k M tS gamma)
            (clsEs (splitExp V ae De) M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale (familyWidthPrefactor K) (splitCnt V ac Dc tS gS M)
            (tightZeta (fejerThetaOne theta gamma k / 4)) rho)
          (pieceLineExponent (familyWidthDivisor k p) (splitCnt V ac Dc tS gS M)
            (splitExp V ae De tS gS M) (clsEr (splitExp V ae De) k M tS gamma) rho)
          (famPieceSliceExponent (clsQr (splitCnt V ac Dc) k M tS gamma)
            (clsEs (splitExp V ae De) M tS gamma) M rho))
    0 < e ∧ e⁻¹ ≤ ((n : Real) + 1) ^ sExpN2 k ac ae * splitW V' theta gamma rho ^ fsExpW2 k ac Dc ae De := by
  intro M tS gS e
  obtain ⟨hw2, huw, hrw, hVw, hV'w⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, hM1, hgd, hdd⟩ := split_step_basics_fejer (k := k) hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hfacE, -⟩ := split_Qr_le_fejer (k := k) hae hDe hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hS, hS1, -, -⟩ := split_samples_le_fejer (k := k) hac hDc hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hb, hb1⟩ := classBudgetW_pos_le k (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  obtain ⟨-, -, hd', hd1'⟩ := section16_theta_delta_bounds_with (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  have hd : 0 < gS := hd'
  have hd1 : gS ≤ 1 := hd1'
  obtain ⟨hz0, hz1, hzi⟩ := tightZeta_fejer_inv_le_gen k hg hg1 ht ht1
  have hu0 : 0 ≤ 2 / (gamma * theta) := (div_pos two_pos (mul_pos hg ht)).le
  have hnv := classVertexNum_succ_le k
  set ν : Real := (n : Real) + 1 with hνdef
  set W := splitW V' theta gamma rho with hWdef
  set P := fejerStepP k with hPdef
  clear_value W
  have hν : 1 ≤ ν := by rw [hνdef]; have := Nat.cast_nonneg (α := Real) n; linarith
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hnv0 : (0 : Real) < (classVertexNum k : Real) + 1 := by
    have := Nat.cast_nonneg (α := Real) (classVertexNum k); linarith only [this]
  -- the count and the exponent controls at `ρ/8`
  have hcbGen : ∀ a D : Nat, splitCnt V a D tS gS M (rho / 8) ≤ ν ^ a * W ^ fsEbW k a D := by
    intro a D
    unfold splitCnt
    have hbase : splitW V tS gS (rho / 8) ≤ W ^ (P + 3 + 3) :=
      split_level_base_le hw2 hV0 hVw hr hrw (by norm_num) (by norm_num) hd hb hdd
    have hM10 : (0 : Real) ≤ (M : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) M; linarith
    have hsw0 := splitW_nonneg (V := V) (t := tS) hV0 hd hb (by positivity : (0 : Real) < rho / 8)
    have h1 := tb_pow hM10 hM1 a
    have h2 : splitW V tS gS (rho / 8) ^ D ≤ ν ^ 0 * W ^ ((P + 3 + 3) * D) := by
      rw [pow_zero, one_mul, pow_mul]
      exact pow_le_pow_left₀ hsw0 hbase D
    have h12 := tb_mul hν hW1 (pow_nonneg hM10 _) (pow_nonneg hsw0 _) h1 h2
    exact h12.trans (tb_mono hν hW1 (by omega) (le_of_eq (by unfold fsEbW; rw [← hPdef]; ring)))
  have hcb1Gen : ∀ a D : Nat, 1 ≤ splitCnt V a D tS gS M (rho / 8) := by
    intro a D
    unfold splitCnt
    obtain ⟨h2, -, -, -⟩ := splitW_facts hV hd hd1 hb hb1 (by positivity : (0 : Real) < rho / 8)
      (by linarith only [hr1])
    have hM1' : (1 : Real) ≤ (M : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) M; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1') (one_le_pow₀ (by linarith))
  have hcb := hcbGen ac Dc
  have hcb1 := hcb1Gen ac Dc
  have hEb0 : 0 < splitExp V ae De tS gS M (rho / 8) := by
    show 0 < (splitCnt V ae De tS gS M (rho / 8))⁻¹
    exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (hcb1Gen ae De))
  have hEbi : (splitExp V ae De tS gS M (rho / 8))⁻¹ ≤ ν ^ ae * W ^ fsEbW k ae De := by
    show ((splitCnt V ae De tS gS M (rho / 8))⁻¹)⁻¹ ≤ _
    rw [inv_inv]; exact hcbGen ae De
  -- the remainder exponent at `ρ/8`, from the exponent track
  have hfac' : splitCnt V ae De tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)) ≤
      ν ^ ae * W ^ fsStepY k ae De := (le_max_left _ _).trans hfacE
  have hscale : 0 < rho / 8 / ((classVertexNum k : Real) + 1) :=
    div_pos (div_pos hr (by norm_num)) hnv0
  have hcr1 : 1 ≤ splitCnt V ae De tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)) := by
    unfold splitCnt
    obtain ⟨h2, -, -, -⟩ := splitW_facts hV hg hg1 hb hb1 hscale (by
      rw [div_le_one hnv0]; have := Nat.cast_nonneg (α := Real) (classVertexNum k)
      linarith only [this, hr1])
    have hM1' : (1 : Real) ≤ (M : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) M; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1') (one_le_pow₀ (by linarith))
  set cr := splitCnt V ae De tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)) with hcrdef
  have hEr : clsEr (splitExp V ae De) k M tS gamma (rho / 8) =
      (cr⁻¹ / 16) ^ (classVertexNum k + 1) := by
    unfold clsEr
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  have hEr0 : 0 < clsEr (splitExp V ae De) k M tS gamma (rho / 8) := by
    rw [hEr]; exact pow_pos (div_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hcr1)) (by norm_num)) _
  have hEri : (clsEr (splitExp V ae De) k M tS gamma (rho / 8))⁻¹ ≤ ν ^ sErN k ae * W ^ fsErW k ae De := by
    rw [hEr, ← inv_pow, inv_div, div_inv_eq_mul]
    have h16 : 16 * cr ≤ ν ^ ae * W ^ (4 + fsStepY k ae De) :=
      tb_const_mul hν hw2 (by norm_num) (by norm_num) (le_trans zero_le_one hcr1) hfac'
    have h16' : 16 * cr ≤ ν ^ ae * W ^ (fsStepY k ae De + 4) := by rw [add_comm]; exact h16
    have hone : (1 : Real) ≤ ν ^ ae * W ^ (fsStepY k ae De + 4) := tb_one_le hν hW1
    calc (16 * cr) ^ (classVertexNum k + 1) ≤ (ν ^ ae * W ^ (fsStepY k ae De + 4)) ^ (classVertexNum k + 1) :=
          pow_le_pow_left₀ (by linarith) h16' _
      _ ≤ (ν ^ ae * W ^ (fsStepY k ae De + 4)) ^ (2 ^ k) := pow_le_pow_right₀ hone hnv
      _ = ν ^ sErN k ae * W ^ fsErW k ae De := by
          unfold sErN fsErW; rw [mul_pow, ← pow_mul, ← pow_mul]
  -- the divisor, from the count track
  set q := ⌊splitCnt V ac Dc tS gS M (rho / 8)⌋₊ with hqdef
  have hq : (q : Real) ≤ ν ^ ac * W ^ fsEbW k ac Dc :=
    (Nat.floor_le (le_trans zero_le_one hcb1)).trans hcb
  have hq1 : ((q + 1 : Nat) : Real) ≤ ν ^ ac * W ^ (fsEbW k ac Dc + 1) := by
    push_cast; exact tb_add_one hν hw2 hq
  have hBq : familyWidthDivisor k p q ≤ ν ^ sBqN k ac * W ^ fsBqW k ac Dc := by
    unfold familyWidthDivisor
    have hpow : (((q + 1) ^ (2 * 2 ^ (k + 1)) : Nat) : Real) ≤
        ν ^ (ac * 2 ^ (k + 2)) * W ^ ((fsEbW k ac Dc + 1) * 2 ^ (k + 2)) := by
      rw [Nat.cast_pow, show 2 * 2 ^ (k + 1) = 2 ^ (k + 2) by rw [pow_succ 2 (k + 1)]; ring]
      exact tb_pow (Nat.cast_nonneg _) hq1 _
    have hpw : ((p : Nat) : Real) ≤ ν ^ 0 * W ^ 1 := by
      rw [pow_zero, one_mul, pow_one]; exact hpV.trans hV'w
    have h1 := tb_mul hν hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hpw hpow
    rw [← Nat.cast_mul] at h1
    have h2 := tb_const_mul (c := (2 : Real)) (j := 1) hν hw2 (by norm_num) (by norm_num)
      (Nat.cast_nonneg _) h1
    have h3 := tb_const_mul (c := (4 : Real)) (j := 2) hν hw2 (by norm_num) (by norm_num)
      (by positivity) h2
    push_cast at h3 ⊢
    refine h3.trans (tb_mono hν hW1 (by unfold sBqN; omega) ?_)
    unfold fsBqW
    omega
  have hBq0 : 0 < familyWidthDivisor k p q := familyWidthDivisor_pos hp q
  -- the line exponent
  set L := pieceLineExponent (familyWidthDivisor k p) (splitCnt V ac Dc tS gS M)
    (splitExp V ae De tS gS M) (clsEr (splitExp V ae De) k M tS gamma) rho with hLdef
  have hL0 : 0 < L := by
    rw [hLdef]; unfold pieceLineExponent
    exact div_pos (mul_pos hEr0 hEb0) hBq0
  have hLi : L⁻¹ ≤ ν ^ sLN2 k ac ae * W ^ fsLW2 k ac Dc ae De := by
    rw [hLdef]; unfold pieceLineExponent
    rw [inv_div, div_eq_mul_inv, mul_inv, ← hqdef]
    have h1 := tb_mul hν hW1 (inv_pos.mpr hEr0).le (inv_pos.mpr hEb0).le hEri hEbi
    exact tb_mul hν hW1 hBq0.le (by positivity) hBq h1
  -- the slice exponent: samples from the count track, slices from the exponent track
  set S := famPieceSamples (clsQr (splitCnt V ac Dc) k M tS gamma) M rho with hSdef
  have hPbE : splitCnt V ae De tS gamma (M * S) (rho / 4) ≤ ν ^ sPbN2 k ac ae * W ^ fsPbW2 k ac Dc ae De := by
    have hMS : ((M * S : Nat) : Real) + 1 ≤ ν ^ (1 + sSN k ac) * W ^ (P + fsSW k ac Dc + 1) := by
      have h := tb_mul hν hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hM hS
      rw [← Nat.cast_mul] at h
      exact tb_add_one hν hw2 h
    have hbase : splitW V tS gamma (rho / 4) ≤ W ^ (P + 2 + 3) :=
      split_level_base_le hw2 hV0 hVw hr hrw (by norm_num) (by norm_num) hg hb hgd
    have hMS0 : (0 : Real) ≤ ((M * S : Nat) : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) (M * S); linarith
    have hsw0 := splitW_nonneg (V := V) (t := tS) hV0 hg hb (by positivity : (0 : Real) < rho / 4)
    unfold splitCnt
    have h1 := tb_pow hMS0 hMS ae
    have h2 : splitW V tS gamma (rho / 4) ^ De ≤ ν ^ 0 * W ^ ((P + 2 + 3) * De) := by
      rw [pow_zero, one_mul, pow_mul]
      exact pow_le_pow_left₀ hsw0 hbase De
    have h12 := tb_mul hν hW1 (pow_nonneg hMS0 _) (pow_nonneg hsw0 _) h1 h2
    push_cast at h12 ⊢
    refine h12.trans (tb_mono hν hW1 (le_of_eq (by unfold sPbN2; ring))
      (le_of_eq (by unfold fsPbW2; rw [← hPdef]; ring)))
  have hPbE1 : 1 ≤ splitCnt V ae De tS gamma (M * S) (rho / 4) := by
    unfold splitCnt
    obtain ⟨h2, -, -, -⟩ := splitW_facts hV hg hg1 hb hb1
      (by positivity : (0 : Real) < rho / 4) (by linarith only [hr1])
    have hMS1 : (1 : Real) ≤ ((M * S : Nat) : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) (M * S); linarith
    push_cast at hMS1 ⊢
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hMS1) (one_le_pow₀ (by linarith))
  set Sl := famPieceSliceExponent (clsQr (splitCnt V ac Dc) k M tS gamma)
    (clsEs (splitExp V ae De) M tS gamma) M rho with hSldef
  have hSlval : Sl = (splitCnt V ae De tS gamma (M * S) (rho / 4))⁻¹ := by
    rw [hSldef]
    unfold famPieceSliceExponent clsEs
    rw [← hSdef, abs_of_pos (by positivity : (0 : Real) < rho / 4)]
    rfl
  have hSl0 : 0 < Sl := by rw [hSlval]; exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one hPbE1)
  have hSl1 : Sl ≤ 1 := by rw [hSlval]; exact inv_le_one_of_one_le₀ hPbE1
  have hSli : Sl⁻¹ ≤ ν ^ sPbN2 k ac ae * W ^ fsPbW2 k ac Dc ae De := by
    rw [hSlval, inv_inv]; exact hPbE
  -- the width scale, from the count track
  have hA1 : 1 ≤ familyWidthPrefactor K q := by
    unfold familyWidthPrefactor
    have : (1 : Real) ≤ ((K * (q + 1) : Nat) : Real) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    linarith only [this]
  have hA : familyWidthPrefactor K q ≤ ν ^ ac * W ^ (2 + (1 + (fsEbW k ac Dc + 1))) := by
    unfold familyWidthPrefactor
    have hKw : ((K : Nat) : Real) ≤ ν ^ 0 * W ^ 1 := by
      rw [pow_zero, one_mul, pow_one]; exact hKV.trans hV'w
    have h1 := tb_mul hν hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hKw hq1
    rw [← Nat.cast_mul, zero_add] at h1
    exact tb_const_mul (c := (4 : Real)) (j := 2) hν hw2 (by norm_num) (by norm_num)
      (Nat.cast_nonneg _) h1
  set z := pieceWidthScale (familyWidthPrefactor K) (splitCnt V ac Dc tS gS M)
    (tightZeta (fejerThetaOne theta gamma k / 4)) rho with hzdef
  have hzval : z = tightZeta (fejerThetaOne theta gamma k / 4) / familyWidthPrefactor K q := by rw [hzdef]; rfl
  have hzpos : 0 < z := by rw [hzval]; exact div_pos hz0 (lt_of_lt_of_le zero_lt_one hA1)
  have hzle : z ≤ 1 := by
    rw [hzval, div_le_one (lt_of_lt_of_le zero_lt_one hA1)]; exact hz1.trans hA1
  set Λ := (ac : Real) * ν + ((fsEbW k ac Dc + 4 : Nat) : Real) * W + W ^ fejerStepT k with hΛdef
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; positivity
  have hzinv : z⁻¹ ≤ Real.exp Λ := by
    rw [hzval, inv_div, div_eq_mul_inv]
    have hAexp : familyWidthPrefactor K q ≤ Real.exp ((ac : Real) * ν + ((fsEbW k ac Dc + 4 : Nat) : Real) * W) := by
      have h1 : ν ^ ac ≤ Real.exp ((ac : Real) * ν) := pow_le_exp_mul (by linarith) ac
      have h2 : W ^ (fsEbW k ac Dc + 4) ≤ Real.exp (((fsEbW k ac Dc + 4 : Nat) : Real) * W) :=
        pow_le_exp_mul (by linarith) _
      rw [Real.exp_add]
      refine hA.trans ?_
      rw [show 2 + (1 + (fsEbW k ac Dc + 1)) = fsEbW k ac Dc + 4 by ring]
      exact mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    have hze : (tightZeta (fejerThetaOne theta gamma k / 4))⁻¹ ≤ Real.exp (W ^ fejerStepT k) :=
      hzi.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hu0 huw _))
    rw [hΛdef, Real.exp_add]
    exact mul_le_mul hAexp hze (inv_pos.mpr hz0).le (Real.exp_pos _).le
  -- the cap
  set R := ν ^ (sLN2 k ac ae + sPbN2 k ac ae) *
    W ^ (fsLW2 k ac Dc ae De + fsPbW2 k ac Dc ae De + 2) with hRdef
  have hR1 : 1 ≤ R := tb_one_le hν hW1
  have hLR : L⁻¹ ≤ R := hLi.trans (tb_mono hν hW1 (by omega) (by omega))
  have hLSR : (L * Sl / 4)⁻¹ ≤ R := by
    rw [show (L * Sl / 4)⁻¹ = 4 * (L⁻¹ * Sl⁻¹) by field_simp]
    have h := tb_mul hν hW1 (inv_pos.mpr hL0).le (inv_pos.mpr hSl0).le hLi hSli
    have h4 := tb_const_mul (c := (4 : Real)) (j := 2) hν hw2 (by norm_num) (by norm_num)
      (mul_nonneg (inv_pos.mpr hL0).le (inv_pos.mpr hSl0).le) h
    exact h4.trans (tb_mono hν hW1 le_rfl (by omega))
  have hcap := capped_rounded_inv_le_real hL0 hSl0 hSl1 hzpos hzle hΛ0 hzinv hR1 hLR hLSR
  refine ⟨section16CappedWidthExponent_pos (div_pos (mul_pos hL0 hSl0) (by norm_num)), ?_⟩
  refine hcap.trans ?_
  have hfront : 2 * (6 + Λ) ≤ ν * W ^ (fsZW k ac Dc + 4) := by
    simpa only [hΛdef, fsZW, Nat.add_assoc] using
      split_width_front_factor_le hν hw2 ac (fsEbW k ac Dc) (fejerStepT k)
  have hR0 : 0 ≤ R := le_trans zero_le_one hR1
  calc 2 * ((6 + Λ) * R) = (2 * (6 + Λ)) * R := by ring
    _ ≤ (ν * W ^ (fsZW k ac Dc + 4)) * R := mul_le_mul_of_nonneg_right hfront hR0
    _ = ν ^ (1 + (sLN2 k ac ae + sPbN2 k ac ae)) *
          W ^ ((fsZW k ac Dc + 4) + (fsLW2 k ac Dc ae De + fsPbW2 k ac Dc ae De + 2)) := by
        rw [hRdef]; ring
    _ ≤ ν ^ sExpN2 k ac ae * W ^ fsExpW2 k ac Dc ae De :=
        tb_mono hν hW1 (by unfold sExpN2; omega) (by unfold fsExpW2; omega)

/-- **The width exponent of the next class, in two bases.** -/
theorem split_exp_inv_le_fejer {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p) (hKV : (K : Real) ≤ V')
    (hpV : (p : Real) ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let M := n * classPiecesFejer gamma theta k
    let tS := classBudgetW (fejerThetaOne theta gamma k) k
    let gS := section16Delta (fejerThetaOne theta gamma k)
    let e := section16CappedWidthExponent
        (pieceLineExponent (familyWidthDivisor k p) (splitCnt V a D tS gS M)
            (splitExp V a D tS gS M) (clsEr (splitExp V a D) k M tS gamma) rho *
          famPieceSliceExponent (clsQr (splitCnt V a D) k M tS gamma)
            (clsEs (splitExp V a D) M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale (familyWidthPrefactor K) (splitCnt V a D tS gS M)
            (tightZeta (fejerThetaOne theta gamma k / 4)) rho)
          (pieceLineExponent (familyWidthDivisor k p) (splitCnt V a D tS gS M)
            (splitExp V a D tS gS M) (clsEr (splitExp V a D) k M tS gamma) rho)
          (famPieceSliceExponent (clsQr (splitCnt V a D) k M tS gamma)
            (clsEs (splitExp V a D) M tS gamma) M rho))
    0 < e ∧ e⁻¹ ≤ ((n : Real) + 1) ^ sExpN k a * splitW V' theta gamma rho ^ fsExpW k a D := by
  exact split_exp_inv_le_fejer2 (k := k) ha hD ha hD hV hVV hK hp hKV hpV
    hg hg1 ht ht1 hr hr1 n

/-! ### The split step -/

/-- The parameter degree of the next split class. -/
def splitStepDFejer (k a D : Nat) : Nat := fsCountW k a D + fsExpW k a D + fejerStepThrDeg k D

/-- **The split step of route (II).** A split class of dimension `k ≥ 1`
with the family Lemma 16.6 at dimension `k` gives a split class of dimension
`k+1`, with family exponent `splitStepA k a` and parameter degree
`splitStepDFejer k a D`. -/
theorem splitUniformClass_succ_fejer {k : Nat} (hk : 1 ≤ k) {V : Real} (hV : 1 ≤ V) {a D : Nat}
    (ha : 1 ≤ a) (hD : 1 ≤ D) (C : SplitUniformClass k V a D) {K p : Nat} (hK : 1 ≤ K)
    (hp : 0 < p)
    (hlemma6 : AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor K) (familyWidthDivisor k p)))
    {V' : Real} (hVV : V ≤ V') (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V') :
    Nonempty (SplitUniformClass (k + 1) V' (splitStepA k a) (splitStepDFejer k a D)) := by
  classical
  obtain ⟨hCnt, hExp, hCntMono, hExpAnti⟩ := splitCnt_controls hV a D
  refine ⟨{
    U := fun N _ theta gamma Gamma =>
      ∃ P : Fin (classPiecesFejer gamma theta k) → StepPieceFejer C N theta gamma,
        Gamma ⊆ stepPieceFejerGraphs C P
    mono := fun N _ theta gamma Gamma Gamma' hsub ⟨P, hP⟩ => ⟨P, hsub.trans hP⟩
    empty := fun N _ theta gamma =>
      ⟨fun _ => ClassPiece.empty C _ _ _ _ _ _, Finset.empty_subset _⟩
    decomp := ?_
    cover := ?_ }⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hVu : 1 ≤ V' * (2 / (gamma * theta)) :=
      one_le_mul_of_one_le_of_one_le (hV.trans hVV) (le_trans (by norm_num) hu2)
    have hN' : classStepThrFejer (fun theta gamma => (V * (2 / (gamma * theta))) ^ D) theta gamma k ≤ N := by
      rw [← classStepThresholdFejer_eq]
      refine (step_thr_le_fejer hk hV hVV hg hg1 ht ht1).trans (le_trans ?_ hN)
      exact pow_le_pow_right₀ hVu (by unfold splitStepDFejer; omega)
    obtain ⟨J, hJ, P, hP⟩ := class_step_decomp_fejer C hk ht ht1 hg hg1 hN' Gamma hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have h := class_step_cover_gen_fejer C hk hCnt hExp hCntMono hExpAnti (familyWidthPrefactor_pos hK)
      (familyWidthDivisor_pos hp) hlemma6 ht ht1 hg hg1 Gamma P hP
    refine h.weaken ?_ ?_ ?_
    · intro rho hr hr1
      have hc := split_count_le_fejer (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      refine hc.trans (tb_mono hν (by linarith) (by unfold splitStepA; omega)
        (by unfold splitStepDFejer; omega))
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (tb_one_le hν (by linarith)))
    · intro rho hr hr1
      obtain ⟨he0, hei⟩ := split_exp_inv_le_fejer (k := k) ha hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      have hmono := tb_mono (a := sExpN k a) (b := fsExpW k a D) (a' := splitStepA k a)
        (b' := splitStepDFejer k a D) hν (by linarith) (by unfold splitStepA; omega)
        (by unfold splitStepDFejer; omega)
      have h1 := inv_anti₀ (lt_of_lt_of_le zero_lt_one (tb_one_le hν (by linarith))) hmono
      have h2 := inv_anti₀ (inv_pos.mpr he0) hei
      rw [inv_inv] at h2
      exact h1.trans h2

theorem splitStepDFejer_eq (k a D : Nat) :
    splitStepDFejer k a D = splitStepDWith (fejerStepP k) (fejerStepT k) k a D := by
  unfold splitStepDWith wCountW wExpW wThrDeg wZW wLW wBqW wErW wEbW wPbW wSW wStepY
    splitStepDFejer fsCountW fsExpW fejerStepThrDeg fsZW fsLW fsBqW fsErW fsEbW fsPbW fsSW fsQrW fsStepY
  rfl

/-! ### Every dimension -/

/-- The dimension-two seed under the Fejér θ₁: `2^46` (printed `2^132`). -/
def splitSeedFejer : Nat := 2 ^ 46

theorem split_pair_fejer_basic : ∀ k, 2 ≤ k →
    1 ≤ (splitPairWith splitSeedFejer splitSeedFejer k).1 ∧
      1 ≤ (splitPairWith splitSeedFejer splitSeedFejer k).2 := by
  intro k hk
  have h := split_pair_with_bounds 14 (seedA := splitSeedFejer) (seedD := splitSeedFejer)
    Nat.one_le_two_pow Nat.one_le_two_pow
    (by unfold splitSeedFejer; rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num))
    (by unfold splitSeedFejer; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)) k hk
  exact ⟨h.1, h.2.1⟩

/-- **The parameter degree of the Fejér split class**: `log₂ D_k ≤ 22·2^k`. -/
theorem split_pair_fejer_bound : ∀ k, 2 ≤ k →
    (splitPairWith splitSeedFejer splitSeedFejer k).2 ≤ 2 ^ (22 * 2 ^ k) :=
  split_pair_with_bounds_fourteen Nat.one_le_two_pow Nat.one_le_two_pow
    (by unfold splitSeedFejer; exact Nat.pow_le_pow_right (by norm_num) (by norm_num))
    (by unfold splitSeedFejer; exact Nat.pow_le_pow_right (by norm_num) (by norm_num))

/-- **A split uniform class in every dimension `k ≥ 2` under the Fejér θ₁
and the tight radius**, with degrees `splitPairWith (2^46) (2^46) k`, so
`log₂ D_k ≤ 22·2^k` (`split_pair_fejer_bound`). -/
theorem splitUniformClass_all_fejer (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k)))) :
    ∀ k, 2 ≤ k →
      Nonempty (SplitUniformClass k (classV Kc pc k) (splitPairWith splitSeedFejer splitSeedFejer k).1
        (splitPairWith splitSeedFejer splitSeedFejer k).2) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have hV1 := one_le_classV Kc pc 2
    have hc1 := const_le_classV_succ Kc pc 1
    rw [splitPairWith_two]
    exact splitUniformClass_two_fejer (hK 1) (hp 1) (hlem 1 le_rfl) hV1 (hc1.1.trans le_rfl)
      (hc1.2.trans le_rfl) (by unfold splitSeedFejer; exact le_rfl)
  | succ k hk ih =>
    obtain ⟨C⟩ := ih
    obtain ⟨ha, hD⟩ := split_pair_fejer_basic k hk
    have hV1 := one_le_classV Kc pc k
    have hc := const_le_classV_succ Kc pc k
    rw [splitPairWith_succ _ _ hk, ← splitStepDFejer_eq]
    exact splitUniformClass_succ_fejer (by omega) hV1 ha hD C (hK k) (hp k) (hlem k (by omega))
      (classV_le_succ Kc pc k) hc.1 hc.2

end LeanProofs.GowersSzemeredi
