import GowersSzemeredi.Proofs16SplitStepBounds
import GowersSzemeredi.Proofs16ClassStepDegreesSide

/-! Declarations of `Proofs16SplitStepBounds` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

def sStepY (k a D : Nat) : Nat := a * (stepP k + 1) + D * (stepP k + k + 6)

def sQrW (k a D : Nat) : Nat := sStepY k a D * 2 ^ k

def sSW (k a D : Nat) : Nat := sQrW k a D + stepP k + 8

def sPbW (k a D : Nat) : Nat := a * (stepP k + sSW k a D + 1) + D * (stepP k + 5)

/-- The parameter degree of the count of the next class. -/
def sCountW (k a D : Nat) : Nat := stepP k + 1 + 2 * sSW k a D + 2 * sPbW k a D

def sEbW (k a D : Nat) : Nat := a * (stepP k + 1) + D * (stepP k + 6)

def sErW (k a D : Nat) : Nat := (sStepY k a D + 4) * 2 ^ k

def sBqW (k a D : Nat) : Nat := 4 + (sEbW k a D + 1) * 2 ^ (k + 2)

def sLW (k a D : Nat) : Nat := sBqW k a D + (sErW k a D + sEbW k a D)

def sZW (k a D : Nat) : Nat := stepT k + a + sEbW k a D + 7

/-- The parameter degree of the width exponent of the next class. -/
def sExpW (k a D : Nat) : Nat := sZW k a D + sLW k a D + sPbW k a D + 6

/-- The parameter degree of the next split class. -/
def splitStepD (k a D : Nat) : Nat := sCountW k a D + sExpW k a D + stepThrDeg k D

end

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- **The remainder count, in two bases.** -/
theorem split_Qr_le {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    max (splitCnt V a D (classBudget theta gamma k) gamma (n * classPieces gamma theta k)
        (rho / 8 / ((classVertexNum k : Real) + 1)))
      (((3 ^ (k + 1) * (n * classPieces gamma theta k)) : Nat) : Real) ≤
      ((n : Real) + 1) ^ a * splitW V' theta gamma rho ^ sStepY k a D ∧
    clsQr (splitCnt V a D) k (n * classPieces gamma theta k) (classBudget theta gamma k) gamma
      (rho / 8) ≤ ((n : Real) + 1) ^ sQrN k a * splitW V' theta gamma rho ^ sQrW k a D :=
  split_Qr_le_W ha hD hV hVV hg hg1 ht ht1 hr hr1 n (P := stepP k) (classPieces_le_stepP k hg hg1 ht ht1) (twoDiv_gamma_le k hg hg1 ht ht1)
    (twoDiv_delta_le k hg hg1 ht ht1)
    (classBudget_pos_le k ht ht1 hg hg1).1 (stepP_ge k)

/-- **The sample count and the slice count, in two bases.** -/
theorem split_samples_le {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let M := n * classPieces gamma theta k
    let S := famPieceSamples (clsQr (splitCnt V a D) k M (classBudget theta gamma k) gamma) M rho
    (S : Real) ≤ ((n : Real) + 1) ^ sSN k a * splitW V' theta gamma rho ^ sSW k a D ∧
      1 ≤ (S : Real) ∧
      splitCnt V a D (classBudget theta gamma k) gamma (M * S) (rho / 4) ≤
        ((n : Real) + 1) ^ sPbN k a * splitW V' theta gamma rho ^ sPbW k a D ∧
      1 ≤ splitCnt V a D (classBudget theta gamma k) gamma (M * S) (rho / 4) :=
  have hb := classBudget_pos_le k ht ht1 hg hg1
  split_samples_le_W ha hD hV hVV hg hg1 ht ht1 hr hr1 n (P := stepP k) (classPieces_le_stepP k hg hg1 ht ht1) (twoDiv_gamma_le k hg hg1 ht ht1)
    (twoDiv_delta_le k hg hg1 ht ht1) hb.1 hb.2
    (stepP_ge k)

/-- **The count of the next class, in two bases.** -/
theorem split_count_le {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    max (famPieceGraphBound
        (clsQr (splitCnt V a D) k (n * classPieces gamma theta k) (classBudget theta gamma k) gamma)
        (clsPb (splitCnt V a D) (n * classPieces gamma theta k) (classBudget theta gamma k) gamma)
        (n * classPieces gamma theta k) rho)
      (((3 ^ (k + 1) * (n * classPieces gamma theta k)) : Nat) : Real) ≤
      ((n : Real) + 1) ^ sCountN k a * splitW V' theta gamma rho ^ sCountW k a D :=
  have hb := classBudget_pos_le k ht ht1 hg hg1
  split_count_le_W ha hD hV hVV hg hg1 ht ht1 hr hr1 n (P := stepP k) (classPieces_le_stepP k hg hg1 ht ht1) (twoDiv_gamma_le k hg hg1 ht ht1)
    (twoDiv_delta_le k hg hg1 ht ht1) hb.1 hb.2
    (stepP_ge k)

/-- **The width exponent of the next class, in two bases.** -/
theorem split_exp_inv_le {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p) (hKV : (K : Real) ≤ V')
    (hpV : (p : Real) ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let M := n * classPieces gamma theta k
    let tS := classBudget theta gamma k
    let gS := classDelta theta gamma k
    let e := section16CappedWidthExponent
        (pieceLineExponent (familyWidthDivisor k p) (splitCnt V a D tS gS M)
            (splitExp V a D tS gS M) (clsEr (splitExp V a D) k M tS gamma) rho *
          famPieceSliceExponent (clsQr (splitCnt V a D) k M tS gamma)
            (clsEs (splitExp V a D) M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale (familyWidthPrefactor K) (splitCnt V a D tS gS M)
            (section16Zeta theta gamma k) rho)
          (pieceLineExponent (familyWidthDivisor k p) (splitCnt V a D tS gS M)
            (splitExp V a D tS gS M) (clsEr (splitExp V a D) k M tS gamma) rho)
          (famPieceSliceExponent (clsQr (splitCnt V a D) k M tS gamma)
            (clsEs (splitExp V a D) M tS gamma) M rho))
    0 < e ∧ e⁻¹ ≤ ((n : Real) + 1) ^ sExpN k a * splitW V' theta gamma rho ^ sExpW k a D :=
  have hb := classBudget_pos_le k ht ht1 hg hg1
  have hd := section16_theta_delta_bounds k ht ht1 hg hg1
  split_exp_inv_le_W2 ha hD ha hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n (P := stepP k)
    (T := stepT k) (classPieces_le_stepP k hg hg1 ht ht1) (twoDiv_gamma_le k hg hg1 ht ht1)
    (twoDiv_delta_le k hg hg1 ht ht1) hb.1 hb.2 hd.2.2.1 hd.2.2.2
    (section16Zeta_inv_le_gen k hg ht) (stepP_ge k)

/-- **The split step of route (II).** A split class of dimension `k ≥ 1`
with the family Lemma 16.6 at dimension `k` gives a split class of dimension
`k+1`, with family exponent `splitStepA k a` and parameter degree
`splitStepD k a D`. -/
theorem splitUniformClass_succ {k : Nat} (hk : 1 ≤ k) {V : Real} (hV : 1 ≤ V) {a D : Nat}
    (ha : 1 ≤ a) (hD : 1 ≤ D) (C : SplitUniformClass k V a D) {K p : Nat} (hK : 1 ≤ K)
    (hp : 0 < p)
    (hlemma6 : AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor K) (familyWidthDivisor k p)))
    {V' : Real} (hVV : V ≤ V') (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V') :
    Nonempty (SplitUniformClass (k + 1) V' (splitStepA k a) (splitStepD k a D)) := by
  obtain ⟨hCnt, hExp, hCntMono, hExpAnti⟩ := splitCnt_controls hV a D
  refine ⟨{
    U := fun N _ theta gamma Gamma =>
      ∃ P : Fin (classPieces gamma theta k) → StepPiece C N theta gamma,
        Gamma ⊆ stepPieceGraphs C P
    mono := fun N _ theta gamma Gamma Gamma' hsub ⟨P, hP⟩ => ⟨P, hsub.trans hP⟩
    empty := fun N _ theta gamma =>
      ⟨fun _ => ClassPiece.empty C _ _ _ _ _ _, Finset.empty_subset _⟩
    decomp := ?_
    cover := ?_ }⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hVu : 1 ≤ V' * (2 / (gamma * theta)) :=
      one_le_mul_of_one_le_of_one_le (hV.trans hVV) (le_trans (by norm_num) hu2)
    have hN' : classStepThr (fun theta gamma => (V * (2 / (gamma * theta))) ^ D) theta gamma k ≤ N := by
      rw [← classStepThreshold_eq]
      refine (step_thr_le hk hV hVV hg hg1 ht ht1).trans (le_trans ?_ hN)
      exact pow_le_pow_right₀ hVu (by unfold splitStepD; omega)
    obtain ⟨J, hJ, P, hP⟩ := class_step_decomp C hk ht ht1 hg hg1 hN' Gamma hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have h := class_step_cover_gen C hk hCnt hExp hCntMono hExpAnti (familyWidthPrefactor_pos hK)
      (familyWidthDivisor_pos hp) hlemma6 ht ht1 hg hg1 Gamma P hP
    refine h.weaken ?_ ?_ ?_
    · intro rho hr hr1
      have hc := split_count_le (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      refine hc.trans (tb_mono hν (by linarith) (by unfold splitStepA; omega)
        (by unfold splitStepD; omega))
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (tb_one_le hν (by linarith)))
    · intro rho hr hr1
      obtain ⟨he0, hei⟩ := split_exp_inv_le (k := k) ha hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      have hmono := tb_mono (a := sExpN k a) (b := sExpW k a D) (a' := splitStepA k a)
        (b' := splitStepD k a D) hν (by linarith) (by unfold splitStepA; omega)
        (by unfold splitStepD; omega)
      have h1 := inv_anti₀ (lt_of_lt_of_le zero_lt_one (tb_one_le hν (by linarith))) hmono
      have h2 := inv_anti₀ (inv_pos.mpr he0) hei
      rw [inv_inv] at h2
      exact h1.trans h2

end

end LeanProofs.GowersSzemeredi
