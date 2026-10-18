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

`fsExpW`, `fsLW`, `splitSeedFejer`, `splitStepDFejer`, `splitStepDFejer_eq`,
`splitUniformClass_all_fejer`, `splitUniformClass_succ_fejer`,
`split_Qr_le_fejer`, `split_exp_inv_le_fejer`, `split_pair_fejer_basic`,
`split_pair_fejer_bound` and `split_samples_le_fejer` are in
`Proofs16SplitStepFejerSide`, outside the final route. -/
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
def fsZW (k a D : Nat) : Nat := fejerStepT k + a + fsEbW k a D + 7

def fsPbW2 (k ac Dc ae De : Nat) : Nat :=
  ae * (fejerStepP k + fsSW k ac Dc + 1) + De * (fejerStepP k + 5)

def fsLW2 (k ac Dc ae De : Nat) : Nat := fsBqW k ac Dc + (fsErW k ae De + fsEbW k ae De)

/-- The parameter degree of the width exponent of the next two-track class. -/
def fsExpW2 (k ac Dc ae De : Nat) : Nat :=
  fsZW k ac Dc + fsLW2 k ac Dc ae De + fsPbW2 k ac Dc ae De + 6

/-! ### The step bounds at `(fejerStepP k, fejerStepT k)` -/

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

end LeanProofs.GowersSzemeredi
