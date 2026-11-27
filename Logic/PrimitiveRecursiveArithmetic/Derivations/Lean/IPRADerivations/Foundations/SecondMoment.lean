import IPRADerivations.Probability.FiniteCauchySchwarz
import IPRADerivations.AnalyticNumberTheory.Mobius
import IPRADerivations.DiophantineNumberTheory.KhinchinMoment
import IPRADerivations.Core.Reindex

/-!
# The second-moment method on a finite grid

Framework (packet `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, (K10)–(K11): "let
`F = Σ_{k=K}^B 1_{E_k(J)}` … `∫F² = Σ_k |E_k| + 2Σ_{k<ℓ} |E_k ∩ E_ℓ|` … finite weighted Cauchy–Schwarz says
`(∫F)² ≤ |{F > 0}| ∫F²`"; reusable for any second-moment covering argument).

For a family of cell sets `b(c, k, x)`, `k < B`, on the cells `c < T`, with `F(c) = Σ_{k<B} b(c, k, x)`
(the body `oB b`):

* `cs_moment`: `(Σ_c F)² ≤ (Σ_c [F > 0]) (Σ_c F²)`, from `Probability/FiniteCauchySchwarz` with the weights
  `[F > 0]` (`sg y · y = y`, `sg_mul_self`);
* `sq_moment`: `Σ_c F² = Σ_{k<B} Σ_{ℓ<B} Σ_c b(c, k) b(c, ℓ)`, the pair-overlap expansion, by `sum_scale`
  and two Fubini exchanges.

`Σ_c F = Σ_k Σ_c b(c, k)` is `Core/Fubini.fubini` itself. When `b` is the covering bit of a finite union
`E_k`, `Σ_c [F > 0] = |⋃_k E_k|` and `Σ_c b(c, k) b(c, ℓ) = |E_k ∩ E_ℓ|`.
-/

namespace LeanProofs.IPRA.Foundations.SecondMoment

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Probability.FiniteCauchySchwarz (wvB wv2B inst2_wvB inst2_wv2B cauchy_schwarz)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (shift_inst2')

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `[y > 0] y = y`. -/
theorem sg_mul_self (y : PTm n) : Γ ⊢[PRAAx] sg y * y ≐ y := by
  refine .orE (zero_or_succ y) ?_ ?_
  · exact (congrMul ((congrSg Prf.hyp0).eqTrans sg_zero) Prf.hyp0).eqTrans ((zero_mul _).eqTrans Prf.hyp0.eqSymm)
  · exact (congrMul ((congrSg Prf.hyp0).eqTrans (sg_succ _)) (.eqRefl _)).eqTrans (one_mul _)

section SM

variable (b : PTm 3)

theorem inst2_sgF (c y : PTm n) : inst2 (sg (oB b)) c y = sg (inst2 (oB b) c y) := by simp [inst2, Signum.sg]

theorem inst2_FF (c y : PTm n) : inst2 (oB b * oB b) c y = inst2 (oB b) c y * inst2 (oB b) c y := by simp [inst2]

/-- `(Σ_c F)² ≤ (Σ_c [F > 0]) (Σ_c F²)`. -/
theorem cs_moment (T B x : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF (oB b)) T (pairT B x) * ap2 (sumF (oB b)) T (pairT B x))
      (ap2 (sumF (sg (oB b))) T (pairT B x) * ap2 (sumF (oB b * oB b)) T (pairT B x)) := by
  have cs := cauchy_schwarz (Γ := Γ) (sg (oB b)) (oB b) T (pairT B x)
  have e1 : Γ ⊢[PRAAx] ap2 (sumF (wvB (sg (oB b)) (oB b))) T (pairT B x) ≐ ap2 (sumF (oB b)) T (pairT B x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_wvB, inst2_sgF]
    exact sg_mul_self _
  have e2 : Γ ⊢[PRAAx] ap2 (sumF (wv2B (sg (oB b)) (oB b))) T (pairT B x) ≐
      ap2 (sumF (oB b * oB b)) T (pairT B x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_wv2B, inst2_sgF, inst2_FF]
    ipra_lc 𝔞 (inst2 (oB b) (var 0) (Syn.shift (pairT B x))) * natEq (sg_mul_self (inst2 (oB b) (var 0) (Syn.shift (pairT B x))))
  exact le_congr (congrMul e1 e1) (congrMul (.eqRefl _) e2) cs

/-! ## The pair expansion of `Σ_c F²` -/

/-- `b(c, k, x) F(c)` over `0 = c`, `1 = k`, `2 = ⟨B, x⟩`. -/
def aB : PTm 3 := Syn.subst ![var 0, var 1, sndT (var 2)] b * Syn.subst ![var 0, var 2] (oB b)

theorem inst3_aB (c k y : PTm n) : inst3 (aB b) c k y = inst3 b c k (sndT y) * inst2 (oB b) c y := by
  simp [inst3, aB, PTm.subst_mul, subst_reindex2, subst_reindex3]

/-- `b(c, k, x) b(c, ℓ, x)` over `0 = c`, `1 = ℓ`, `2 = ⟨k, x⟩`. -/
def dB : PTm 3 := Syn.subst ![var 0, fstT (var 2), sndT (var 2)] b * Syn.subst ![var 0, var 1, sndT (var 2)] b

theorem inst3_dB (c l z : PTm n) : inst3 (dB b) c l z = inst3 b c (fstT z) (sndT z) * inst3 b c l (sndT z) := by
  simp [inst3, dB, PTm.subst_mul, subst_reindex3]

/-- `b(c, k, x) b(c, ℓ, x)` over `0 = c`, `1 = ⟨⟨k, ℓ⟩, x⟩`. -/
def qB : PTm 2 :=
  Syn.subst ![var 0, fstT (fstT (var 1)), sndT (var 1)] b * Syn.subst ![var 0, sndT (fstT (var 1)), sndT (var 1)] b

theorem inst2_qB (c z : PTm n) :
    inst2 (qB b) c z = inst3 b c (fstT (fstT z)) (sndT z) * inst3 b c (sndT (fstT z)) (sndT z) := by
  simp [inst2, qB, PTm.subst_mul, subst_reindex3]

/-- The overlap `Σ_{c<T} b(c, k) b(c, ℓ)` over `0 = k`, `1 = ℓ`, `2 = ⟨T, x⟩`. -/
def ppB : PTm 3 := ap2 (sumF (qB b)) (fstT (var 2)) (pairT (pairT (var 0) (var 1)) (sndT (var 2)))

theorem inst3_ppB (k l y : PTm n) :
    inst3 (ppB b) k l y = ap2 (sumF (qB b)) (fstT y) (pairT (pairT k l) (sndT y)) := by
  simp [inst3, ppB, subst_ap2]

/-- `b(c, k) F(c) = F(c) b(c, k)` read through the row pairs. -/
theorem rowA_at (k c B x : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowB (aB b)) k (pairT c (pairT B x)) ≐
      inst2 (oB b) c (pairT B x) * inst2 (rowB b) k (pairT c x) := by
  rw [inst2_rowB, inst3_aB, inst2_rowB]
  have hc : Γ ⊢[PRAAx] fstT (pairT c (pairT B x)) ≐ c := fst_pair _ _
  have hy : Γ ⊢[PRAAx] sndT (pairT c (pairT B x)) ≐ pairT B x := snd_pair _ _
  have hx : Γ ⊢[PRAAx] sndT (sndT (pairT c (pairT B x))) ≐ x := (congrSnd hy).eqTrans (snd_pair _ _)
  refine (mul_comm _ _).eqTrans ?_
  exact congrMul (congrInst2 (oB b) hc hy)
    (congrInst3 b (hc.eqTrans (fst_pair c x).eqSymm) (.eqRefl _) (hx.eqTrans (snd_pair c x).eqSymm))

/-- `F(c)² = Σ_{k<B} b(c, k) F(c)`. -/
theorem pt_sq (c B x : PTm n) :
    Γ ⊢[PRAAx] inst2 (oB b) c (pairT B x) * inst2 (oB b) c (pairT B x) ≐
      inst2 (oB (aB b)) c (pairT B (pairT B x)) := by
  have hF := oB_at (Γ := Γ) b c B x
  refine (congrMul (.eqRefl _) hF).eqTrans ?_
  refine ((oB_at (Γ := Γ) (aB b) c B (pairT B x)).eqTrans ?_).eqSymm
  refine sum_scale (rowB (aB b)) (rowB b) B (inst2 (oB b) c (pairT B x)) (pairT c x) (pairT c (pairT B x))
    (.allI (.impI ?_))
  simp only [shift_pairT, shift_inst2']
  exact rowA_at b _ _ _ _

/-- `b(c, k) F(c) = Σ_{ℓ<B} b(c, k) b(c, ℓ)`. -/
theorem colA_at (c k B x : PTm n) :
    Γ ⊢[PRAAx] inst2 (colB (aB b)) c (pairT k (pairT B x)) ≐ inst2 (oB (dB b)) c (pairT B (pairT k x)) := by
  rw [inst2_colB, inst3_aB]
  have hk : Γ ⊢[PRAAx] fstT (pairT k (pairT B x)) ≐ k := fst_pair _ _
  have hy : Γ ⊢[PRAAx] sndT (pairT k (pairT B x)) ≐ pairT B x := snd_pair _ _
  have hx : Γ ⊢[PRAAx] sndT (sndT (pairT k (pairT B x))) ≐ x := (congrSnd hy).eqTrans (snd_pair _ _)
  refine (congrMul (congrInst3 b (.eqRefl _) hk hx) ((congrInst2 (oB b) (.eqRefl _) hy).eqTrans (oB_at _ _ _ _))).eqTrans ?_
  refine ((oB_at (Γ := Γ) (dB b) c B (pairT k x)).eqTrans ?_).eqSymm
  refine sum_scale (rowB (dB b)) (rowB b) B (inst3 b c k x) (pairT c x) (pairT c (pairT k x)) (.allI (.impI ?_))
  simp only [shift_pairT]
  rw [inst2_rowB, inst3_dB, inst2_rowB,
    show Syn.shift (inst3 b c k x) = inst3 b (Syn.shift c) (Syn.shift k) (Syn.shift x) by
      simp only [inst3, Syn.shift, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp]
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift B) :: Γ.map Fm.shift
  have hc : Θ ⊢[PRAAx] fstT (pairT (Syn.shift c) (pairT (Syn.shift k) (Syn.shift x))) ≐ Syn.shift c := fst_pair _ _
  have hz : Θ ⊢[PRAAx] sndT (pairT (Syn.shift c) (pairT (Syn.shift k) (Syn.shift x))) ≐
      pairT (Syn.shift k) (Syn.shift x) := snd_pair _ _
  exact congrMul (congrInst3 b hc ((congrFst hz).eqTrans (fst_pair _ _)) ((congrSnd hz).eqTrans (snd_pair _ _)))
    (congrInst3 b (hc.eqTrans (fst_pair _ _).eqSymm) (.eqRefl _)
      (((congrSnd hz).eqTrans (snd_pair _ _)).eqTrans (snd_pair _ _).eqSymm))

/-- One column of the pair expansion. -/
theorem colDQ_at (c l k x : PTm n) :
    Γ ⊢[PRAAx] inst2 (colB (dB b)) c (pairT l (pairT k x)) ≐ inst2 (qB b) c (pairT (pairT k l) x) := by
  rw [inst2_colB, inst3_dB, inst2_qB]
  have hl : Γ ⊢[PRAAx] fstT (pairT l (pairT k x)) ≐ l := fst_pair _ _
  have hz : Γ ⊢[PRAAx] sndT (pairT l (pairT k x)) ≐ pairT k x := snd_pair _ _
  have hk : Γ ⊢[PRAAx] fstT (sndT (pairT l (pairT k x))) ≐ k := (congrFst hz).eqTrans (fst_pair _ _)
  have hx : Γ ⊢[PRAAx] sndT (sndT (pairT l (pairT k x))) ≐ x := (congrSnd hz).eqTrans (snd_pair _ _)
  have q1 : Γ ⊢[PRAAx] fstT (pairT (pairT k l) x) ≐ pairT k l := fst_pair _ _
  have qk : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT k l) x)) ≐ k := (congrFst q1).eqTrans (fst_pair _ _)
  have ql : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT k l) x)) ≐ l := (congrSnd q1).eqTrans (snd_pair _ _)
  have qx : Γ ⊢[PRAAx] sndT (pairT (pairT k l) x) ≐ x := snd_pair _ _
  exact congrMul (congrInst3 b (.eqRefl _) (hk.eqTrans qk.eqSymm) (hx.eqTrans qx.eqSymm))
    (congrInst3 b (.eqRefl _) (hl.eqTrans ql.eqSymm) (hx.eqTrans qx.eqSymm))

/-- One row of `Σ_c F²`: `Σ_c b(c, k) F(c) = Σ_ℓ Σ_c b(c, k) b(c, ℓ)`. -/
theorem col_a (k T B x : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB (aB b)) k (pairT T (pairT B x)) ≐ inst2 (oB (ppB b)) k (pairT B (pairT T x)) := by
  rw [inst2_pB]
  refine (congrAp2 (sumF (colB (aB b))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  have s1 : Γ ⊢[PRAAx] ap2 (sumF (colB (aB b))) T (pairT k (pairT B x)) ≐
      ap2 (sumF (oB (dB b))) T (pairT B (pairT k x)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact colA_at b _ _ _ _
  refine s1.eqTrans ((fubini (dB b) T B (pairT k x)).eqTrans ?_)
  refine .eqTrans ?_ (oB_at (Γ := Γ) (ppB b) k B (pairT T x)).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  rw [inst2_pB, inst2_rowB, inst3_ppB]
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift B) :: Γ.map Fm.shift
  have hT : Θ ⊢[PRAAx] fstT (pairT (Syn.shift T) (pairT (Syn.shift k) (Syn.shift x))) ≐ Syn.shift T := fst_pair _ _
  have hkx : Θ ⊢[PRAAx] sndT (pairT (Syn.shift T) (pairT (Syn.shift k) (Syn.shift x))) ≐
      pairT (Syn.shift k) (Syn.shift x) := snd_pair _ _
  have hk' : Θ ⊢[PRAAx] fstT (pairT (Syn.shift k) (pairT (Syn.shift T) (Syn.shift x))) ≐ Syn.shift k := fst_pair _ _
  have hy' : Θ ⊢[PRAAx] sndT (pairT (Syn.shift k) (pairT (Syn.shift T) (Syn.shift x))) ≐
      pairT (Syn.shift T) (Syn.shift x) := snd_pair _ _
  refine (congrAp2 (sumF (colB (dB b))) hT (congrPairT (.eqRefl _) hkx)).eqTrans ?_
  refine .eqTrans ?_ (congrAp2 (sumF (qB b)) ((congrFst hy').eqTrans (fst_pair _ _))
    (congrPairT (congrPairT hk' (.eqRefl _)) ((congrSnd hy').eqTrans (snd_pair _ _)))).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact colDQ_at b _ _ _ _

/-- `Σ_c F² = Σ_{k<B} Σ_{ℓ<B} Σ_c b(c, k) b(c, ℓ)`. -/
theorem sq_moment (T B x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (oB b * oB b)) T (pairT B x) ≐ ap2 (sumF (oB (ppB b))) B (pairT B (pairT T x)) := by
  have s1 : Γ ⊢[PRAAx] ap2 (sumF (oB b * oB b)) T (pairT B x) ≐ ap2 (sumF (oB (aB b))) T (pairT B (pairT B x)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_FF]
    simp only [shift_pairT]
    exact pt_sq b _ _ _
  refine s1.eqTrans ((fubini (aB b) T B (pairT B x)).eqTrans ?_)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact col_a b _ _ _ _

/-! ## The ordered expansion `Σ_c F² = Σ_k |E_k| + 2 Σ_ℓ Σ_{k<ℓ} |E_k ∩ E_ℓ|` (for `0/1` cell sets) -/

/-- `b(c, ℓ) Σ_{k<ℓ} b(c, k)` over `0 = c`, `1 = ℓ`, `2 = x`: `aB` with the bound `ℓ`. -/
def cB2 : PTm 3 := Syn.subst ![var 0, var 1, pairT (var 1) (var 2)] (aB b)

/-- `Σ_{k<ℓ} Σ_{c<T} b(c, ℓ) b(c, k)` over `0 = ℓ`, `1 = ⟨T, x⟩`. -/
def lowB : PTm 2 := Syn.subst ![var 0, pairT (var 0) (var 1)] (oB (ppB b))

theorem inst3_cB2 (c l x : PTm n) : inst3 (cB2 b) c l x = inst3 (aB b) c l (pairT l x) := by
  simp only [cB2, inst3, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp

theorem inst2_lowB (l y : PTm n) : inst2 (lowB b) l y = inst2 (oB (ppB b)) l (pairT l y) := by
  simp only [lowB, inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp

theorem inst2_two_mul (G : PTm 2) (c y : PTm n) : inst2 (two * G) c y = two * inst2 G c y := by
  simp [inst2]

/-- `F(c)² = F(c) + 2 Σ_{ℓ<B} b(c, ℓ) Σ_{k<ℓ} b(c, k)` for `0/1` cell sets. -/
theorem pt_ord (c B x : PTm n)
    (hb : ∀ {m : ℕ} (Δ : List (Fm PTm m)) (c k y : PTm m), Δ ⊢[PRAAx] inst3 b c k y * inst3 b c k y ≐ inst3 b c k y) :
    Γ ⊢[PRAAx] inst2 (oB b) c (pairT B x) * inst2 (oB b) c (pairT B x) ≐
      inst2 (addBody (oB b) (two * oB (cB2 b))) c (pairT B x) := by
  rw [inst2_addBody, inst2_two_mul]
  have hF := oB_at (Γ := Γ) b c B x
  have sq := DiophantineNumberTheory.KhinchinMoment.sq_sum (Γ := Γ) (rowB b) B (pairT c x)
  have e1 : Γ ⊢[PRAAx] ap2 (sumF (DiophantineNumberTheory.KhinchinMoment.t2B (rowB b))) B (pairT c x) ≐ ap2 (sumF (rowB b)) B (pairT c x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [show inst2 (DiophantineNumberTheory.KhinchinMoment.t2B (rowB b)) (var 0) (Syn.shift (pairT c x)) =
      inst2 (rowB b) (var 0) (Syn.shift (pairT c x)) * inst2 (rowB b) (var 0) (Syn.shift (pairT c x)) by simp [inst2],
      inst2_rowB]
    exact hb _ _ _ _
  have e2 : Γ ⊢[PRAAx] ap2 (sumF (DiophantineNumberTheory.KhinchinMoment.crB (rowB b))) B (pairT c x) ≐ ap2 (sumF (rowB (cB2 b))) B (pairT c x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [DiophantineNumberTheory.KhinchinMoment.inst2_crB, inst2_rowB, inst2_rowB, inst3_cB2, inst3_aB]
    let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift B) :: Γ.map Fm.shift
    have hc : Θ ⊢[PRAAx] fstT (pairT (Syn.shift c) (Syn.shift x)) ≐ Syn.shift c := fst_pair _ _
    have hx : Θ ⊢[PRAAx] sndT (pairT (Syn.shift c) (Syn.shift x)) ≐ Syn.shift x := snd_pair _ _
    refine congrMul (congrInst3 b (.eqRefl _) (.eqRefl _) (snd_pair _ _).eqSymm) ?_
    refine .eqTrans ?_ (oB_at (Γ := Θ) b _ _ _).eqSymm
    exact congrAp2 (sumF (rowB b)) (.eqRefl _) (congrPairT hc hx).eqSymm
  refine (congrMul hF hF).eqTrans (sq.eqTrans (congrAdd (e1.eqTrans hF.eqSymm)
    (congrMul (.eqRefl _) (e2.eqTrans (oB_at (Γ := Γ) (cB2 b) c B x).eqSymm))))

/-- One column of the ordered expansion: `Σ_c b(c, ℓ) Σ_{k<ℓ} b(c, k) = Σ_{k<ℓ} Σ_c b(c, ℓ) b(c, k)`. -/
theorem col_ord (l T x : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB (cB2 b)) l (pairT T x) ≐ inst2 (lowB b) l (pairT T x) := by
  rw [inst2_pB, inst2_lowB]
  refine (congrAp2 (sumF (colB (cB2 b))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  refine .eqTrans ?_ (col_a b l T l x)
  rw [inst2_pB]
  refine .eqTrans ?_ (congrAp2 (sumF (colB (aB b))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  rw [inst2_colB, inst2_colB, inst3_cB2]
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift T) :: Γ.map Fm.shift
  have hl : Θ ⊢[PRAAx] fstT (pairT (Syn.shift l) (Syn.shift x)) ≐ Syn.shift l := fst_pair _ _
  have hx : Θ ⊢[PRAAx] sndT (pairT (Syn.shift l) (Syn.shift x)) ≐ Syn.shift x := snd_pair _ _
  have hl' : Θ ⊢[PRAAx] fstT (pairT (Syn.shift l) (pairT (Syn.shift l) (Syn.shift x))) ≐ Syn.shift l := fst_pair _ _
  have hy' : Θ ⊢[PRAAx] sndT (pairT (Syn.shift l) (pairT (Syn.shift l) (Syn.shift x))) ≐
      pairT (Syn.shift l) (Syn.shift x) := snd_pair _ _
  exact congrInst3 (aB b) (.eqRefl _) (hl.eqTrans hl'.eqSymm) ((congrPairT hl hx).eqTrans hy'.eqSymm)

/-- The ordered expansion `Σ_c F² = Σ_k Σ_c b(c, k) + 2 Σ_{ℓ<B} Σ_{k<ℓ} Σ_c b(c, ℓ) b(c, k)` for `0/1`
cell sets: `∫F² = Σ_k |E_k| + 2 Σ_{k<ℓ} |E_k ∩ E_ℓ|`. -/
theorem ord_moment (T B x : PTm n)
    (hb : ∀ {m : ℕ} (Δ : List (Fm PTm m)) (c k y : PTm m), Δ ⊢[PRAAx] inst3 b c k y * inst3 b c k y ≐ inst3 b c k y) :
    Γ ⊢[PRAAx] ap2 (sumF (oB b * oB b)) T (pairT B x) ≐
      ap2 (sumF (pB b)) B (pairT T x) + two * ap2 (sumF (lowB b)) B (pairT T x) := by
  have s1 : Γ ⊢[PRAAx] ap2 (sumF (oB b * oB b)) T (pairT B x) ≐
      ap2 (sumF (addBody (oB b) (two * oB (cB2 b)))) T (pairT B x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_FF]
    simp only [shift_pairT]
    exact pt_ord b _ _ _ hb
  have s2 := sum_add (Γ := Γ) (oB b) (two * oB (cB2 b)) T (pairT B x)
  have s3 := fubini (Γ := Γ) b T B x
  have s4 : Γ ⊢[PRAAx] ap2 (sumF (two * oB (cB2 b))) T (pairT B x) ≐ two * ap2 (sumF (oB (cB2 b))) T (pairT B x) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_two_mul, show Syn.shift (two : PTm n) = two by simp [Syn.shift]]
    exact .eqRefl _
  have s5 := fubini (Γ := Γ) (cB2 b) T B x
  have s6 : Γ ⊢[PRAAx] ap2 (sumF (pB (cB2 b))) B (pairT T x) ≐ ap2 (sumF (lowB b)) B (pairT T x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact col_ord b _ _ _
  exact s1.eqTrans (s2.eqTrans (congrAdd s3 (s4.eqTrans (congrMul (.eqRefl _) (s5.eqTrans s6)))))

end SM

end LeanProofs.IPRA.Foundations.SecondMoment
