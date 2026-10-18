import GowersSzemeredi.Proofs16SplitStepBounds
import GowersSzemeredi.Proofs16ClassStepDegreesFejer
import GowersSzemeredi.Proofs16SplitFejerDegrees
import GowersSzemeredi.Proofs16UniformCoverTwoFejer

/-! **Split uniform classes in every dimension under the Fejér θ₁ and the
tight radius** (Notes L.16d).

The Fejér instance of `Proofs16SplitStepBounds` and
`Proofs16SplitAllDimensions`:
* the parameter-side degrees `fsStepY … fsExpW`: the corpus's with
  `fejerStepP k = 64F`, `fejerStepT k = 22F + 105` in place of
  `stepP k`, `stepT k`, where `F = fejerProductExponent k`. The family-side
  degrees (`sQrN … sExpN`, `splitStepA`) do not see Section 16 and are
  reused;
* `split_count_le_fejer`, `split_exp_inv_le_fejer2` and their lemmas: the
  step bounds of `Proofs16SplitStepBounds` (`…_W`) at
  `(fejerStepP k, fejerStepT k)` with the Fejér inputs;
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
printed parameters.

`splitUniformClass_all_fejer` is in `Proofs16SplitStepFejerSide`, outside the
final route. -/
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

def fsEbW (k a D : Nat) : Nat := a * (fejerStepP k + 1) + D * (fejerStepP k + 6)
def fsErW (k a D : Nat) : Nat := (fsStepY k a D + 4) * 2 ^ k
def fsBqW (k a D : Nat) : Nat := 4 + (fsEbW k a D + 1) * 2 ^ (k + 2)
def fsLW (k a D : Nat) : Nat := fsBqW k a D + (fsErW k a D + fsEbW k a D)
def fsZW (k a D : Nat) : Nat := fejerStepT k + a + fsEbW k a D + 7

/-- The parameter degree of the width exponent of the next class. -/
def fsExpW (k a D : Nat) : Nat := fsZW k a D + fsLW k a D + fsPbW k a D + 6

def fsPbW2 (k ac Dc ae De : Nat) : Nat :=
  ae * (fejerStepP k + fsSW k ac Dc + 1) + De * (fejerStepP k + 5)

def fsLW2 (k ac Dc ae De : Nat) : Nat := fsBqW k ac Dc + (fsErW k ae De + fsEbW k ae De)

/-- The parameter degree of the width exponent of the next two-track class. -/
def fsExpW2 (k ac Dc ae De : Nat) : Nat :=
  fsZW k ac Dc + fsLW2 k ac Dc ae De + fsPbW2 k ac Dc ae De + 6

/-! ### The step bounds at `(fejerStepP k, fejerStepT k)` -/

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
  have hf := fejerThetaOne_bounds k ht ht1 hg hg1
  have hb := classBudgetW_pos_le k hf.1 hf.2
  exact split_Qr_le_W ha hD hV hVV hg hg1 ht ht1 hr hr1 n (P := fejerStepP k) (classPiecesFejer_le_gen k hg hg1 ht ht1) (twoDiv_gamma_le_fejer k hg hg1 ht ht1)
    (twoDiv_delta_le_fejer k hg hg1 ht ht1)
    hb.1 (by have := fejerStepP_ge k; omega)

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
  have hf := fejerThetaOne_bounds k ht ht1 hg hg1
  have hb := classBudgetW_pos_le k hf.1 hf.2
  exact split_samples_le_W ha hD hV hVV hg hg1 ht ht1 hr hr1 n (P := fejerStepP k)
    (classPiecesFejer_le_gen k hg hg1 ht ht1) (twoDiv_gamma_le_fejer k hg hg1 ht ht1)
    (twoDiv_delta_le_fejer k hg hg1 ht ht1) hb.1 hb.2 (by have := fejerStepP_ge k; omega)

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
  have hf := fejerThetaOne_bounds k ht ht1 hg hg1
  have hb := classBudgetW_pos_le k hf.1 hf.2
  exact split_count_le_W ha hD hV hVV hg hg1 ht ht1 hr hr1 n (P := fejerStepP k)
    (classPiecesFejer_le_gen k hg hg1 ht ht1) (twoDiv_gamma_le_fejer k hg hg1 ht ht1)
    (twoDiv_delta_le_fejer k hg hg1 ht ht1) hb.1 hb.2 (by have := fejerStepP_ge k; omega)

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
  have hf := fejerThetaOne_bounds k ht ht1 hg hg1
  have hb := classBudgetW_pos_le k hf.1 hf.2
  have hd := section16_theta_delta_bounds_with hf.1 hf.2
  exact split_exp_inv_le_W2 hac hDc hae hDe hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n
    (P := fejerStepP k) (T := fejerStepT k) (classPiecesFejer_le_gen k hg hg1 ht ht1) (twoDiv_gamma_le_fejer k hg hg1 ht ht1)
    (twoDiv_delta_le_fejer k hg hg1 ht ht1) hb.1 hb.2 hd.2.2.1 hd.2.2.2
    (tightZeta_fejer_inv_le_gen k hg hg1 ht ht1) (by have := fejerStepP_ge k; omega)

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

end LeanProofs.GowersSzemeredi
