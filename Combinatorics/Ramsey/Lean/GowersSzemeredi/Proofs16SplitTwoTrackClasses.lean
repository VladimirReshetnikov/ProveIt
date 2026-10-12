import GowersSzemeredi.Proofs16SplitTwoTrack

/-! **Two-track split classes in every dimension** (Notes L.16x).

* `SplitUniformClass2 k V ac Dc ae De`: count `(n+1)^ac·W^Dc`, threshold
  `(V·2/(γθ))^Dc`, width exponent `((n+1)^ae·W^De)⁻¹`;
  `SplitUniformClass2.toSplit` weakens it to a split class at
  `(max ac ae, max Dc De)`;
* `splitUniformClass2_succ_fejer`: the step;
* `splitUniformClass2_two`: dimension two at count `(11, 2^41)` and exponent
  `(29, 2^46)` (the one-track seed is `(32, 2^48)`);
* `splitQuad`: the two-track recursion, `split_quad_le_max` (pointwise below
  the `max` pairs of `Proofs18TightClassesFejerM`), `splitUniformClass2_all`;
* `tDegT2`: the exact table up to `l = 14`
  (`…, 122, 188, 288, 452, 742, 1277, 2300, 4294, 8225, 16029, 31572`), then
  `5·2^(l−1) + 3(l+4)² + 2`; `split_quad_le_uDegT2`, `polyCoverAt_classT2`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- **A two-track split class.** -/
abbrev SplitUniformClass2 (k : Nat) (V : Real) (ac Dc ae De : Nat) :=
  UniformClassWith k (fun theta gamma => (V * (2 / (gamma * theta))) ^ Dc)
    (fun theta gamma n rho => ((n : Real) + 1) ^ ac * splitW V theta gamma rho ^ Dc)
    (fun theta gamma n rho => (((n : Real) + 1) ^ ae * splitW V theta gamma rho ^ De)⁻¹)

/-- **A two-track class is a split class** at `(max ac ae, max Dc De)`. -/
def SplitUniformClass2.toSplit {k : Nat} {V : Real} {ac Dc ae De : Nat}
    (C : SplitUniformClass2 k V ac Dc ae De) (hV : 1 ≤ V) :
    SplitUniformClass k V (max ac ae) (max Dc De) where
  U := C.U
  mono := C.mono
  empty := C.empty
  decomp := by
    intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    refine C.decomp theta gamma ht ht1 hg hg1 N (le_trans ?_ hN) Gamma hsize hprod
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hVu : 1 ≤ V * (2 / (gamma * theta)) :=
      one_le_mul_of_one_le_of_one_le hV (le_trans (by norm_num) hu2)
    exact pow_le_pow_right₀ hVu (le_max_left _ _)
  cover := by
    intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    refine (C.cover theta gamma ht ht1 hg hg1 N n Gamma hU).weaken ?_ ?_ ?_
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      exact tb_mono hν (by linarith) (le_max_left _ _) (le_max_left _ _)
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have : (0 : Real) < splitW V theta gamma rho := by linarith
      positivity
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      have hW0 : (0 : Real) < splitW V theta gamma rho := by linarith
      refine inv_anti₀ (by positivity) ?_
      exact tb_mono hν (by linarith) (le_max_right _ _) (le_max_right _ _)

/-- **The two-track split step.** -/
theorem splitUniformClass2_succ_fejer {k : Nat} (hk : 1 ≤ k) {V : Real} (hV : 1 ≤ V)
    {ac Dc ae De : Nat} (hac : 1 ≤ ac) (hDc : 1 ≤ Dc) (hae : 1 ≤ ae) (hDe : 1 ≤ De)
    (C : SplitUniformClass2 k V ac Dc ae De) {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p)
    (hlemma6 : AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor K) (familyWidthDivisor k p)))
    {V' : Real} (hVV : V ≤ V') (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V') :
    Nonempty (SplitUniformClass2 (k + 1) V' (sCountN k ac)
      (max (fsCountW k ac Dc) (fejerStepThrDeg k Dc)) (sExpN2 k ac ae) (fsExpW2 k ac Dc ae De)) := by
  classical
  obtain ⟨hCnt, -, hCntMono, -⟩ := splitCnt_controls hV ac Dc
  obtain ⟨-, hExp, -, hExpAnti⟩ := splitCnt_controls hV ae De
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
    have hN' : classStepThrFejer (fun theta gamma => (V * (2 / (gamma * theta))) ^ Dc) theta gamma k ≤ N := by
      rw [← classStepThresholdFejer_eq]
      refine (step_thr_le_fejer hk hV hVV hg hg1 ht ht1).trans (le_trans ?_ hN)
      exact pow_le_pow_right₀ hVu (le_max_right _ _)
    obtain ⟨J, hJ, P, hP⟩ := class_step_decomp_fejer C hk ht ht1 hg hg1 hN' Gamma hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have h := class_step_cover_gen_fejer C hk hCnt hExp hCntMono hExpAnti (familyWidthPrefactor_pos hK)
      (familyWidthDivisor_pos hp) hlemma6 ht ht1 hg hg1 Gamma P hP
    refine h.weaken ?_ ?_ ?_
    · intro rho hr hr1
      have hc := split_count_le_fejer (k := k) hac hDc hV hVV hg hg1 ht ht1 hr hr1 n
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      exact hc.trans (tb_mono hν (by linarith) le_rfl (le_max_left _ _))
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (tb_one_le hν (by linarith)))
    · intro rho hr hr1
      obtain ⟨he0, hei⟩ := split_exp_inv_le_fejer2 (k := k) hac hDc hae hDe hV hVV hK hp hKV hpV
        hg hg1 ht ht1 hr hr1 n
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      have h2 := inv_anti₀ (inv_pos.mpr he0) hei
      rw [inv_inv] at h2
      exact h2

/-- **Dimension two as a two-track class**: count `(11, 2^41)`, exponent `(29, 2^46)`. -/
theorem splitUniformClass2_two {K1 p1 : Nat} (hK1 : 1 ≤ K1) (hp1 : 0 < p1)
    (hlemma6 : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    {V : Real} (hV : 1 ≤ V) (hKV : (K1 : Real) ≤ V) (hpV : (p1 : Real) ≤ V) :
    Nonempty (SplitUniformClass2 2 V 11 ((2 : Nat) ^ 41) 29 ((2 : Nat) ^ 46)) := by
  classical
  refine ⟨{
    U := fun N _ theta gamma Gamma =>
      ∃ P : Fin (polyTwoFejerPieces gamma theta) → PolyPieceTwoFejer N theta gamma,
        Gamma ⊆ polyPieceTwoFejerGraphs P
    mono := fun N _ theta gamma Gamma Gamma' hsub ⟨P, hP⟩ => ⟨P, hsub.trans hP⟩
    empty := fun N _ theta gamma =>
      ⟨fun _ => PolyPieceTwoData.empty _ _ _ _ _, Finset.empty_subset _⟩
    decomp := ?_
    cover := ?_ }⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hVu : 1 ≤ V * (2 / (gamma * theta)) :=
      one_le_mul_of_one_le_of_one_le hV (le_trans (by norm_num) hu2)
    have hthr : polyTwoFejerThreshold theta gamma ≤ N := by
      refine (polyTwoFejerThreshold_le_power hg hg1 ht ht1).trans (le_trans ?_ hN)
      refine (pow_le_pow_left₀ (by linarith only [hu2])
        (le_mul_of_one_le_left (by linarith only [hu2]) hV) _).trans ?_
      exact pow_le_pow_right₀ hVu (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    obtain ⟨J, hJ, P, hP⟩ := section16_poly_piece_decomposition_two_fejer ht ht1 hg hg1 hthr Gamma
      hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have hcov := section16_uniform_cover_two_fejer (familyWidthPrefactor_pos hK1)
      (familyWidthDivisor_pos hp1) hlemma6 ht ht1 hg hg1 Gamma (fun _ => Finset.univ) P
      (fun i => by rw [restrictRelation_univ]; exact hP i)
    have hsub : Finset.univ.biUnion Gamma ⊆
        Finset.univ.biUnion fun i => restrictRelation (Gamma i) Finset.univ := by
      simp only [restrictRelation_univ]; exact le_rfl
    have hν : (1 : Real) ≤ (n : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) n; linarith only [this]
    refine (hcov.subset hsub).weaken ?_ ?_ ?_
    · intro rho hr hr1
      exact uniTwoFejerCount_le_split hV hg hg1 ht ht1 hr hr1 n
    · intro rho hr hr1
      obtain ⟨hW2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have : (0 : Real) < splitW V theta gamma rho := by linarith only [hW2]
      positivity
    · intro rho hr hr1
      have h := uniTwoFejerExp_inv_le_split hV (by omega : 0 < K1) hp1 hKV hpV hg hg1 ht ht1 hr hr1 n
      have h0 := uniTwoFejerExp_pos (A := familyWidthPrefactor K1) (Bq := familyWidthDivisor 1 p1)
        (familyWidthDivisor_pos (k := 1) hp1)
        (theta := theta) (gamma := gamma) (n * polyTwoFejerPieces gamma theta) hr
      have := inv_anti₀ (inv_pos.mpr h0) h
      rwa [inv_inv] at this

/-! ### The two-track recursion -/

/-- One two-track step on `((ac, Dc), (ae, De))`. -/
def splitQuadStep (k : Nat) (x : (Nat × Nat) × (Nat × Nat)) : (Nat × Nat) × (Nat × Nat) :=
  ((sCountN k x.1.1, max (fsCountW k x.1.1 x.1.2) (fejerStepThrDeg k x.1.2)),
    (sExpN2 k x.1.1 x.2.1, fsExpW2 k x.1.1 x.1.2 x.2.1 x.2.2))

/-- The two-track recursion from the dimension-two seed. -/
def splitQuad : Nat → (Nat × Nat) × (Nat × Nat)
  | 0 => ((11, 2 ^ 41), (29, 2 ^ 46))
  | k + 1 => if k < 2 then ((11, 2 ^ 41), (29, 2 ^ 46)) else splitQuadStep k (splitQuad k)

theorem splitQuad_two : splitQuad 2 = ((11, 2 ^ 41), (29, 2 ^ 46)) := by simp [splitQuad]

theorem splitQuad_succ {k : Nat} (hk : 2 ≤ k) : splitQuad (k + 1) = splitQuadStep k (splitQuad k) := by
  rw [splitQuad, if_neg (by omega)]

/-- **The two-track degrees stay below the `max` pairs.** -/
theorem split_quad_le_max : ∀ l, 2 ≤ l →
    1 ≤ (splitQuad l).1.1 ∧ 1 ≤ (splitQuad l).1.2 ∧ 1 ≤ (splitQuad l).2.1 ∧ 1 ≤ (splitQuad l).2.2 ∧
      (splitQuad l).1.1 ≤ (splitPairMax splitSeedSmallA splitSeedSmallD l).1 ∧
      (splitQuad l).1.2 ≤ (splitPairMax splitSeedSmallA splitSeedSmallD l).2 ∧
      (splitQuad l).2.1 ≤ (splitPairMax splitSeedSmallA splitSeedSmallD l).1 ∧
      (splitQuad l).2.2 ≤ (splitPairMax splitSeedSmallA splitSeedSmallD l).2 := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base =>
    rw [splitQuad_two, splitPairMax_two]
    unfold splitSeedSmallA splitSeedSmallD
    refine ⟨by norm_num, Nat.one_le_two_pow, by norm_num, Nat.one_le_two_pow, by norm_num,
      Nat.pow_le_pow_right (by norm_num) (by norm_num), by norm_num,
      Nat.pow_le_pow_right (by norm_num) (by norm_num)⟩
  | succ k hk ih =>
    obtain ⟨h1, h2, h3, h4, hac, hDc, hae, hDe⟩ := ih
    rw [splitQuad_succ hk, splitPairMax_succ _ _ hk]
    set ac := (splitQuad k).1.1
    set Dc := (splitQuad k).1.2
    set ae := (splitQuad k).2.1
    set De := (splitQuad k).2.2
    set a := (splitPairMax splitSeedSmallA splitSeedSmallD k).1
    set D := (splitPairMax splitSeedSmallA splitSeedSmallD k).2
    show 1 ≤ sCountN k ac ∧ 1 ≤ max (fsCountW k ac Dc) (fejerStepThrDeg k Dc) ∧
      1 ≤ sExpN2 k ac ae ∧ 1 ≤ fsExpW2 k ac Dc ae De ∧
      sCountN k ac ≤ splitStepAMax k a ∧
      max (fsCountW k ac Dc) (fejerStepThrDeg k Dc) ≤
        splitStepDMaxWith (fejerStepP k) (fejerStepT k) k a D ∧
      sExpN2 k ac ae ≤ splitStepAMax k a ∧
      fsExpW2 k ac Dc ae De ≤ splitStepDMaxWith (fejerStepP k) (fejerStepT k) k a D
    have hc : sCountN k ac ≤ sCountN k a := by
      simp only [sCountN, sSN, sQrN, sPbN]; gcongr
    have he : sExpN2 k ac ae ≤ sExpN k a := by
      unfold sExpN2 sExpN sLN2 sLN sPbN2 sPbN sSN sQrN sBqN sErN; gcongr
    have hcw : fsCountW k ac Dc ≤ wCountW (fejerStepP k) k a D := by
      simp only [fsCountW, wCountW, fsSW, fsPbW, fsQrW, fsStepY, wSW, wPbW, wStepY]; gcongr
    have hct : fejerStepThrDeg k Dc ≤ wThrDeg (fejerStepP k) D := by
      unfold fejerStepThrDeg wThrDeg; gcongr
    have hew : fsExpW2 k ac Dc ae De ≤ wExpW (fejerStepP k) (fejerStepT k) k a D := by
      unfold fsExpW2 wExpW fsZW wZW fsLW2 wLW fsBqW wBqW fsErW wErW fsEbW wEbW fsPbW2 wPbW fsSW wSW
        fsQrW fsStepY wStepY
      gcongr
    refine ⟨?_, ?_, ?_, ?_, hc.trans (le_max_left _ _), max_le (hcw.trans ?_) (hct.trans (le_max_right _ _)),
      he.trans (le_max_right _ _), hew.trans ((le_max_right _ _).trans (le_max_left _ _))⟩
    · unfold sCountN; omega
    · exact (show 1 ≤ fejerStepThrDeg k Dc by unfold fejerStepThrDeg; omega).trans (le_max_right _ _)
    · unfold sExpN2; omega
    · unfold fsExpW2; omega
    · exact (le_max_left _ _).trans (le_max_left _ _)

/-- **A two-track class in every dimension `k ≥ 2`.** -/
theorem splitUniformClass2_all (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k)))) :
    ∀ k, 2 ≤ k →
      Nonempty (SplitUniformClass2 k (classV Kc pc k) (splitQuad k).1.1 (splitQuad k).1.2
        (splitQuad k).2.1 (splitQuad k).2.2) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have hV1 := one_le_classV Kc pc 2
    have hc1 := const_le_classV_succ Kc pc 1
    rw [splitQuad_two]
    exact splitUniformClass2_two (hK 1) (hp 1) (hlem 1 le_rfl) hV1 (hc1.1.trans le_rfl)
      (hc1.2.trans le_rfl)
  | succ k hk ih =>
    obtain ⟨C⟩ := ih
    obtain ⟨h1, h2, h3, h4, -⟩ := split_quad_le_max k hk
    have hV1 := one_le_classV Kc pc k
    have hc := const_le_classV_succ Kc pc k
    rw [splitQuad_succ hk]
    exact splitUniformClass2_succ_fejer (by omega) hV1 h1 h2 h3 h4 C (hK k) (hp k) (hlem k (by omega))
      (classV_le_succ Kc pc k) hc.1 hc.2

/-! ### The class table -/

/-- The exact two-track class log-degrees in dimensions `0, …, 14`. -/
def tTableT2 : List Nat :=
  [17, 17, 47, 78, 122, 188, 288, 452, 742, 1277, 2300, 4294, 8225, 16029, 31572]

/-- The class log-degree: the exact two-track table up to `14`, constant `5/2` beyond. -/
def tDegT2 (l : Nat) : Nat := if l ≤ 14 then tTableT2.getD l 0 else 5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 + 2

/-- The two-track class degree. -/
def uDegT2 (l : Nat) : Nat := 2 ^ tDegT2 l

theorem uDegT2_eq (l : Nat) : uDegT2 l = 2 ^ tDegT2 l := rfl

theorem tDegT2_eq_of_ge {l : Nat} (hl : 15 ≤ l) :
    tDegT2 l = 5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 + 2 := by
  unfold tDegT2; rw [if_neg (by omega)]

theorem seventeen_le_tDegT2 (l : Nat) : 17 ≤ tDegT2 l := by
  rcases Nat.lt_or_ge l 15 with h | h
  · interval_cases l <;> decide
  · rw [tDegT2_eq_of_ge h]
    have : 16 ≤ (l + 4) ^ 2 := by nlinarith
    omega

theorem tDegT2_le_succ (l : Nat) : tDegT2 l ≤ tDegT2 (l + 1) := by
  rcases Nat.lt_or_ge l 15 with h | h
  · interval_cases l <;> decide
  · rw [tDegT2_eq_of_ge h, tDegT2_eq_of_ge (by omega)]
    have h1 : 2 ^ (l - 1) ≤ 2 ^ (l + 1 - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (l + 4) ^ 2 ≤ (l + 1 + 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega

theorem tDegT2_mono {l k : Nat} (hl : l ≤ k) : tDegT2 l ≤ tDegT2 k := by
  induction k, hl using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (tDegT2_le_succ k)

theorem uDegT2_le_pow {l k : Nat} (hl : l ≤ k) : uDegT2 l ≤ 2 ^ tDegT2 k := by
  rw [uDegT2_eq]; exact Nat.pow_le_pow_right (by norm_num) (tDegT2_mono hl)

/-- The η side condition `3(k+4)²` fits the class degree. -/
theorem sq_le_three_tDegT2 (k : Nat) : 3 * (k + 4) ^ 2 ≤ 3 * tDegT2 k + 5 * k + 37 := by
  rcases Nat.lt_or_ge k 15 with h | h
  · interval_cases k <;> decide
  · rw [tDegT2_eq_of_ge h]; omega

/-- **The two-track degrees fit `uDegT2`**, kernel-evaluated up to dimension `14`. -/
theorem split_quad_le_uDegT2 {l : Nat} (hl : 2 ≤ l) :
    max (splitQuad l).1.1 (splitQuad l).2.1 + max (splitQuad l).1.2 (splitQuad l).2.2 + l + 1 ≤
      uDegT2 l := by
  rcases Nat.lt_or_ge l 15 with h | h
  · interval_cases l <;> decide +kernel
  · obtain ⟨-, -, -, -, hac, hDc, hae, hDe⟩ := split_quad_le_max l hl
    have hM := split_pair_max_le_uDegM hl
    have hMT : uDegM l = uDegT2 l := by
      unfold uDegM uDegT2; rw [tDegM_eq_of_ge h, tDegT2_eq_of_ge h]
    rw [← hMT]
    have h1 := max_le hac hae
    have h2 := max_le hDc hDe
    omega

/-- **The class cover in dimension `l` at degree `uDegT2 l`.** -/
theorem polyCoverAt_classT2 (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    {l : Nat} (hl1 : 1 ≤ l) :
    PolyCoverAt l (uCount (classV Kc pc l) (uDegT2 l)) (uExp (classV Kc pc l) (uDegT2 l)) := by
  have hVl := one_le_classV Kc pc l
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    refine polyCoverAt_one_uniform_low hVl ?_
    unfold uDegT2
    exact Nat.pow_le_pow_right (by norm_num) (seventeen_le_tDegT2 1)
  · obtain ⟨C2⟩ := splitUniformClass2_all Kc pc hK hp hlem l hl
    have C := C2.toSplit hVl
    have hfit := split_quad_le_uDegT2 hl
    have P0 := (C.toPower hVl).polyCoverAt (by omega) hVl (D := uDegT2 l) (by omega) (by omega)
      (by omega)
    refine P0.weaken ?_ ?_ ?_
    · intro g t s hg hg1 ht ht1 hs hs1
      rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]
    · intro g t s _ _ _ _ _ _
      exact (uExp_pos_le _ _ g t s).1
    · intro g t s hg hg1 ht ht1 hs hs1
      show (uCount _ _ g t s)⁻¹ ≤ _
      rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]

/-- `tDegT2 ≤ tDegM`. -/
theorem tDegT2_le_tDegM (l : Nat) : tDegT2 l ≤ tDegM l := by
  rcases Nat.lt_or_ge l 15 with h | h
  · interval_cases l <;> decide
  · rw [tDegT2_eq_of_ge h, tDegM_eq_of_ge h]

end LeanProofs.GowersSzemeredi
