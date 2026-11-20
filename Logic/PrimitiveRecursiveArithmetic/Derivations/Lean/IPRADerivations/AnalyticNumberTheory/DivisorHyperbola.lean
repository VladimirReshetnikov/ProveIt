import IPRADerivations.AnalyticNumberTheory.Harmonic
import IPRADerivations.AnalyticNumberTheory.SumPhi
import IPRADerivations.Foundations.LatticeCount
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.MultiSums
import IPRADerivations.Core.OrderCertificates

/-!
# The Dirichlet hyperbola identity (`pnt_ipra_constructive_2026-11-14`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma
`sb:divisor-approx`: "Let `m = ⌊√y⌋`. Counting pairs of positive integers whose product is at most `y`,
according to which coordinate is at most `m`, gives `D(y) = 2 Σ_{n≤m} ⌊y/n⌋ − m²`."

With `S(N, F) = Σ_{i<N} ⌊F/(i+1)⌋` (`Harmonic.S`), so that `D(y) = Σ_{n≤y} τ(n) = Σ_{n≤y} ⌊y/n⌋ = S(y, y)`,
and `m² ≤ y < (m + 1)²` (`m = ⌊√y⌋`):

  `S(y, y) + m² = 2 S(m, y)`                                                         (`hyperbola`).

The proof counts the lattice pairs `(a + 1)(b + 1) ≤ y`: a row has `⌊y/(a+1)⌋` points (`row_count`, from
`LatticeCount.exact_count`), the rows `a ≥ m` only meet the columns `b < m` (`row_short`, since
`y < (m+1)²`), those are exchanged (`Core/Fubini`), and each column `b < m` has its first `m` points
in the square `a < m` (`col_split`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h quo_anti)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)
open LeanProofs.IPRA.Foundations.LatticeCount (icB icS exact_count)
open LeanProofs.IPRA.Foundations.IntervalCover (cnt)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Indicators -/

/-- `[x ≤ F]`. -/
abbrev leI (x F : PTm n) : PTm n := monus one (monus x F)

theorem leI_one {x F : PTm n} (h : Γ ⊢[PRAAx] le x F) : Γ ⊢[PRAAx] leI x F ≐ one :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)

theorem leI_zero {x F : PTm n} (h : Γ ⊢[PRAAx] lt F x) : Γ ⊢[PRAAx] leI x F ≐ zero := by
  have e := natEq (eq_add_of_le (le_trans (le_succ_self F) h))
  show Γ ⊢[PRAAx] le one (monus x F)
  ipra_le sl h with e

theorem sg_one {t : PTm n} (h : Γ ⊢[PRAAx] le one t) : Γ ⊢[PRAAx] sg t ≐ one :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)

/-- `[(a + 1)(b + 1) ≤ F] = [b < ⌊F/(a+1)⌋]`. -/
theorem ind_eq (a b F : PTm n) :
    Γ ⊢[PRAAx] leI (succ a * succ b) F ≐ cnt zero (quo F (succ a)) b := by
  have dm := div_mod_at (Γ := Γ) (x := F) (y := succ a) (c := a) (.eqRefl _)
  have e := natEq (Prf.andE₁ dm)
  have hr : Γ ⊢[PRAAx] lt (rem F (succ a)) (succ a) := Prf.andE₂ dm
  have c1 : Γ ⊢[PRAAx] cnt zero (quo F (succ a)) b ≐ sg (monus (quo F (succ a)) b) :=
    (congrMul ((congrMonus (.eqRefl _) (zero_monus _)).eqTrans (monus_zero _)) (.eqRefl _)).eqTrans (one_mul _)
  refine .eqTrans ?_ c1.eqSymm
  refine .orE (lt_or_le b (quo F (succ a))) ?_ ?_
  · let Δ : List (Fm PTm n) := lt b (quo F (succ a)) :: Γ
    have h : Δ ⊢[PRAAx] lt b (quo F (succ a)) := Prf.hyp0
    have e' := natEq ((Prf.andE₁ dm).wk : Δ ⊢[PRAAx] _ ≐ _)
    have l1 : Δ ⊢[PRAAx] le (succ a * succ b) F := by
      ipra_le (𝔞 a + 1) * sl h + 𝔞 (rem F (succ a)) with e'
    have l2 : Δ ⊢[PRAAx] le one (monus (quo F (succ a)) b) := by
      have e2 := natEq (eq_add_of_le (le_trans (le_succ_self b) h))
      ipra_le sl h with e2
    exact (leI_one l1).eqTrans (sg_one l2).eqSymm
  · let Δ : List (Fm PTm n) := le (quo F (succ a)) b :: Γ
    have h : Δ ⊢[PRAAx] le (quo F (succ a)) b := Prf.hyp0
    have e' := natEq ((Prf.andE₁ dm).wk : Δ ⊢[PRAAx] _ ≐ _)
    have hr' : Δ ⊢[PRAAx] lt (rem F (succ a)) (succ a) := hr.wk
    have l1 : Δ ⊢[PRAAx] lt F (succ a * succ b) := by
      ipra_le (𝔞 a + 1) * sl h + sl hr' with e'
    exact (leI_zero l1).eqTrans ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)).eqTrans sg_zero).eqSymm

/-! ## Rows -/

/-- `[(a + 1)(b + 1) ≤ F]` over `0 = b`, `1 = ⟨a, F⟩`. -/
abbrev IB : PTm 2 := monus one (monus (succ (fstT (var 1)) * succ (var 0)) (sndT (var 1)))

theorem inst2_IB (b x : PTm n) : inst2 IB b x = leI (succ (fstT x) * succ b) (sndT x) := by simp [inst2]

theorem IB_at (b a F : PTm n) : Γ ⊢[PRAAx] inst2 IB b (pairT a F) ≐ leI (succ a * succ b) F := by
  rw [inst2_IB]
  exact congrMonus (.eqRefl _) (congrMonus (congrMul (congrSucc (fst_pair _ _)) (.eqRefl _)) (snd_pair _ _))

/-- A row has `⌊F/(a+1)⌋` points below any `N ≥ ⌊F/(a+1)⌋`. -/
theorem row_count {a F N : PTm n} (hN : Γ ⊢[PRAAx] le (quo F (succ a)) N) :
    Γ ⊢[PRAAx] ap2 (sumF IB) N (pairT a F) ≐ quo F (succ a) := by
  refine (sum_congr_bounded IB icB (pairT a F) (pairT zero (quo F (succ a))) N (.allI (.impI ?_))).eqTrans
    ((exact_count N zero _ hN).eqTrans (monus_zero _))
  rw [show Syn.shift (pairT a F) = pairT (Syn.shift a) (Syn.shift F) by simp [Syn.shift],
    show Syn.shift (pairT zero (quo F (succ a))) = pairT zero (quo (Syn.shift F) (succ (Syn.shift a))) by
      simp [Syn.shift]]
  refine (IB_at _ _ _).eqTrans ((ind_eq _ _ _).eqTrans ?_)
  have e : inst2 icB (var 0 : PTm (n + 1)) (pairT zero (quo (Syn.shift F) (succ (Syn.shift a)))) =
      cnt (fstT (pairT zero (quo (Syn.shift F) (succ (Syn.shift a)))))
        (sndT (pairT zero (quo (Syn.shift F) (succ (Syn.shift a))))) (var 0) := by simp [inst2, Signum.sg]
  rw [e]
  exact congrMul (congrMonus (.eqRefl _) (congrMonus (fst_pair _ _).eqSymm (.eqRefl _)))
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrMonus (snd_pair _ _).eqSymm (.eqRefl _))))

/-- `⌊F/(a+1)⌋ ≤ F`. -/
theorem quo_le_self (a F : PTm n) : Γ ⊢[PRAAx] le (quo F (succ a)) F := by
  have dm := div_mod_at (Γ := Γ) (x := F) (y := succ a) (c := a) (.eqRefl _)
  have e := natEq (Prf.andE₁ dm)
  ipra_le 𝔞 a * 𝔞 (quo F (succ a)) + 𝔞 (rem F (succ a)) with e

/-- `⌊y/(a+1)⌋ ≤ m` for `a ≥ m` and `y < (m+1)²`. -/
theorem row_short {a m y : PTm n} (ha : Γ ⊢[PRAAx] le m a) (hy : Γ ⊢[PRAAx] lt y (succ m * succ m)) :
    Γ ⊢[PRAAx] le (quo y (succ a)) m := by
  have dm := div_mod_at (Γ := Γ) (x := y) (y := succ a) (c := a) (.eqRefl _)
  refine .orE (lt_or_le m (quo y (succ a))) ?_ Prf.hyp0
  let Δ : List (Fm PTm n) := lt m (quo y (succ a)) :: Γ
  have h : Δ ⊢[PRAAx] lt m (quo y (succ a)) := Prf.hyp0
  have e := natEq ((Prf.andE₁ dm).wk : Δ ⊢[PRAAx] _ ≐ _)
  have ha' : Δ ⊢[PRAAx] le m a := ha.wk
  have hy' : Δ ⊢[PRAAx] lt y (succ m * succ m) := hy.wk
  have hz : Δ ⊢[PRAAx] le one zero := by
    ipra_le sl hy' + (𝔞 a + 1) * sl h + (𝔞 m + 1) * sl ha' + 𝔞 (rem y (succ a)) with e
  exact .botE _ (succ_ne_zero ((monus_zero _).eqSymm.eqTrans hz))

/-! ## The rectangle `j < y − m`, `b < m` -/

/-- `[(m + j + 1)(b + 1) ≤ y]` over `0 = j`, `1 = b`, `2 = ⟨m, y⟩`. -/
abbrev aH : PTm 3 := monus one (monus (succ (fstT (var 2) + var 0) * succ (var 1)) (sndT (var 2)))

theorem inst3_aH (j b z : PTm n) : inst3 aH j b z = leI (succ (fstT z + j) * succ b) (sndT z) := by
  simp [inst3]

/-- A row `a = m + j ≥ m` of the full count, restricted to `b < m`. -/
theorem row_eq (j m y : PTm n) (hy : Γ ⊢[PRAAx] lt y (succ m * succ m)) :
    Γ ⊢[PRAAx] quo y (succ (m + j)) ≐ inst2 (oB aH) j (pairT m (pairT m y)) := by
  refine (row_count (N := m) (row_short (le_add_right m j) hy)).eqSymm.eqTrans ?_
  refine .eqTrans ?_ (oB_at aH j m (pairT m y)).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [show Syn.shift (pairT (m + j) y) = pairT (Syn.shift m + Syn.shift j) (Syn.shift y) by simp [Syn.shift],
    show Syn.shift (pairT j (pairT m y)) = pairT (Syn.shift j) (pairT (Syn.shift m) (Syn.shift y)) by simp [Syn.shift],
    inst2_rowB, inst3_aH]
  refine (IB_at _ _ _).eqTrans ?_
  have hz : (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx]
      sndT (pairT (Syn.shift j) (pairT (Syn.shift m) (Syn.shift y))) ≐ pairT (Syn.shift m) (Syn.shift y) := snd_pair _ _
  exact congrMonus (.eqRefl _) (congrMonus (congrMul (congrSucc (congrAdd ((congrFst hz).eqTrans (fst_pair _ _)).eqSymm
    (fst_pair _ _).eqSymm)) (.eqRefl _)) ((congrSnd hz).eqTrans (snd_pair _ _)).eqSymm)

/-- A column `b < m`: `⌊y/(b+1)⌋ = m + Σ_{j < y − m} [(m + j + 1)(b + 1) ≤ y]`. -/
theorem col_split {b m y : PTm n} (hb : Γ ⊢[PRAAx] lt b m) (hmy : Γ ⊢[PRAAx] le (m * m) y)
    (hm : Γ ⊢[PRAAx] le m y) :
    Γ ⊢[PRAAx] quo y (succ b) ≐ m + inst2 (pB aH) b (pairT (monus y m) (pairT m y)) := by
  have ey : Γ ⊢[PRAAx] y ≐ m + monus y m := eq_add_of_le hm
  -- the full column has `⌊y/(b+1)⌋` points
  have full := row_count (Γ := Γ) (a := b) (F := y) (N := y) (quo_le_self b y)
  have sp := sum_split (Γ := Γ) IB m (monus y m) (pairT b y)
  refine full.eqSymm.eqTrans ((congrAp2 (sumF IB) ey (.eqRefl _)).eqTrans (sp.eqTrans (congrAdd ?_ ?_)))
  · -- the square `a < m` is full
    refine (sum_congr_bounded IB (one : PTm 2) (pairT b y) (pairT b y) m (.allI (.impI ?_))).eqTrans (sum_ones m _)
    rw [show Syn.shift (pairT b y) = pairT (Syn.shift b) (Syn.shift y) by simp [Syn.shift],
      show inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (pairT (Syn.shift b) (Syn.shift y)) = one by simp [inst2]]
    refine (IB_at _ _ _).eqTrans (leI_one ?_)
    have ha : (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift m) := Prf.hyp0
    have hb' : (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx] lt (Syn.shift b) (Syn.shift m) := by
      have hb0 : Γ ⊢[PRAAx] le (succ b) m := hb
      have s := hb0.shift
      simp only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ] at s
      exact s.wk
    have hmy' : (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift m * Syn.shift m) (Syn.shift y) := by
      have s := hmy.shift
      simp only [Fm.shift, subst_le, PTm.subst_mul] at s
      exact s.wk
    ipra_le sl hmy' + 𝔞 (Syn.shift m) * sl hb' + (𝔞 (Syn.shift b) + 1) * sl ha
  · -- the rest is the column `b` of the rectangle
    rw [inst2_pB]
    refine .eqTrans ?_ (congrAp2 (sumF (colB aH)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [show Syn.shift (pairT m (pairT b y)) = pairT (Syn.shift m) (pairT (Syn.shift b) (Syn.shift y)) by simp [Syn.shift],
      show Syn.shift (pairT b (pairT m y)) = pairT (Syn.shift b) (pairT (Syn.shift m) (Syn.shift y)) by simp [Syn.shift],
      inst2_offB, inst2_colB, inst3_aH]
    let Δ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (monus y m)) :: Γ.map Fm.shift
    have s1 : Δ ⊢[PRAAx] sndT (pairT (Syn.shift m) (pairT (Syn.shift b) (Syn.shift y))) ≐ pairT (Syn.shift b) (Syn.shift y) :=
      snd_pair _ _
    have s2 : Δ ⊢[PRAAx] sndT (pairT (Syn.shift b) (pairT (Syn.shift m) (Syn.shift y))) ≐ pairT (Syn.shift m) (Syn.shift y) :=
      snd_pair _ _
    refine ((congrInst2 IB (congrAdd (fst_pair _ _) (.eqRefl _)) s1).eqTrans (IB_at _ _ _)).eqTrans ?_
    refine .eqTrans ?_ (congrMonus (.eqRefl _) (congrMonus (congrMul (congrSucc (congrAdd
      ((congrFst s2).eqTrans (fst_pair _ _)).eqSymm (.eqRefl _))) (congrSucc (fst_pair _ _).eqSymm))
      ((congrSnd s2).eqTrans (snd_pair _ _)).eqSymm))
    exact congrMonus (.eqRefl _) (congrMonus (mul_comm _ _) (.eqRefl _))

/-! ## The identity -/

/-- The constant `m` over `0 = b`, `1 = ⟨M, ⟨m, y⟩⟩`. -/
abbrev mB : PTm 2 := fstT (sndT (var 1))

/-- The Dirichlet hyperbola identity: `S(y, y) + m² = 2 S(m, y)` for `m² ≤ y < (m + 1)²`. -/
theorem hyperbola {y m : PTm n} (h1 : Γ ⊢[PRAAx] le (m * m) y) (h2 : Γ ⊢[PRAAx] lt y (succ m * succ m)) :
    Γ ⊢[PRAAx] S y y + m * m ≐ two * S m y := by
  -- `m ≤ y`
  have hm : Γ ⊢[PRAAx] le m y := by
    refine .orE (zero_or_succ m) ?_ ?_
    · exact le_congr (Prf.hyp0 : ((m ≐ zero) :: Γ) ⊢[PRAAx] m ≐ zero).eqSymm (.eqRefl _) (zero_le _)
    · let Δ : List (Fm PTm n) := (m ≐ succ (pred m)) :: Γ
      have e := natEq (Prf.hyp0 : Δ ⊢[PRAAx] m ≐ succ (pred m))
      have h1' : Δ ⊢[PRAAx] le (m * m) y := h1.wk
      ipra_le sl h1' + 𝔞 m * 𝔞 (pred m) with (𝔞 m) * e
  have ey : Γ ⊢[PRAAx] y ≐ m + monus y m := eq_add_of_le hm
  -- `S(y, y) = S(m, y) + Σ_{j < y − m} ⌊y/(m + j + 1)⌋ = S(m, y) + Σ_j Σ_{b < m} [·]`
  have sA : Γ ⊢[PRAAx] S y y ≐ S m y + ap2 (sumF (oB aH)) (monus y m) (pairT m (pairT m y)) := by
    refine (congrAp2 (sumF hB) ey (.eqRefl _)).eqTrans ((sum_split hB m (monus y m) y).eqTrans (congrAdd (.eqRefl _) ?_))
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_offB, inst2_h, show Syn.shift (pairT m y) = pairT (Syn.shift m) (Syn.shift y) by simp [Syn.shift],
      show Syn.shift (pairT m (pairT m y)) = pairT (Syn.shift m) (pairT (Syn.shift m) (Syn.shift y)) by simp [Syn.shift]]
    have h2' : (lt (var 0) (Syn.shift (monus y m)) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (Syn.shift y) (succ (Syn.shift m) * succ (Syn.shift m)) := by
      have h20 : Γ ⊢[PRAAx] le (succ y) (succ m * succ m) := h2
      have s := h20.shift
      simp only [Fm.shift, subst_le, PTm.subst_mul, ConciseIPRA.PTm.subst_succ] at s
      exact s.wk
    exact (congrAp2 quoF (snd_pair _ _) (congrSucc (congrAdd (fst_pair _ _) (.eqRefl _)))).eqTrans (row_eq _ _ _ h2')
  -- Fubini
  have fb := fubini (Γ := Γ) aH (monus y m) m (pairT m y)
  -- `S(m, y) = m² + Σ_{b < m} (column b)`
  have sB : Γ ⊢[PRAAx] S m y ≐ ap2 (sumF (addBody (pB aH) mB)) m (pairT (monus y m) (pairT m y)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_h, inst2_addBody, show inst2 mB (var 0 : PTm (n + 1)) (Syn.shift (pairT (monus y m) (pairT m y))) =
        fstT (sndT (Syn.shift (pairT (monus y m) (pairT m y)))) by simp [inst2],
      show Syn.shift (pairT (monus y m) (pairT m y)) =
        pairT (Syn.shift (monus y m)) (pairT (Syn.shift m) (Syn.shift y)) by simp [Syn.shift]]
    let Δ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have hb : Δ ⊢[PRAAx] lt (var 0) (Syn.shift m) := Prf.hyp0
    have h1' : Δ ⊢[PRAAx] le (Syn.shift m * Syn.shift m) (Syn.shift y) := by
      have s := h1.shift
      simp only [Fm.shift, subst_le, PTm.subst_mul] at s
      exact s.wk
    have hm' : Δ ⊢[PRAAx] le (Syn.shift m) (Syn.shift y) := by
      have s := hm.shift
      simp only [Fm.shift, subst_le] at s
      exact s.wk
    have cs := col_split hb h1' hm'
    rw [show Syn.shift (monus y m) = monus (Syn.shift y) (Syn.shift m) by simp [Syn.shift]]
    refine cs.eqTrans ((add_comm _ _).eqTrans (congrAdd (.eqRefl _) ?_))
    exact ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)).eqSymm
  have sC : Γ ⊢[PRAAx] ap2 (sumF (addBody (pB aH) mB)) m (pairT (monus y m) (pairT m y)) ≐
      ap2 (sumF (pB aH)) m (pairT (monus y m) (pairT m y)) + m * m := by
    refine (sum_add _ _ _ _).eqTrans (congrAdd (.eqRefl _) ?_)
    refine (sum_scale mB (one : PTm 2) m m (pairT (monus y m) (pairT m y)) (pairT (monus y m) (pairT m y))
      (.allI (.impI ?_))).eqTrans ((congrMul (.eqRefl _) (sum_ones _ _)).eqTrans (.eqRefl _))
    rw [show inst2 mB (var 0 : PTm (n + 1)) (Syn.shift (pairT (monus y m) (pairT m y))) =
        fstT (sndT (Syn.shift (pairT (monus y m) (pairT m y)))) by simp [inst2],
      show inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift (pairT (monus y m) (pairT m y))) = one by simp [inst2],
      show Syn.shift (pairT (monus y m) (pairT m y)) =
        pairT (Syn.shift (monus y m)) (pairT (Syn.shift m) (Syn.shift y)) by simp [Syn.shift]]
    exact ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)).eqTrans ((mul_comm _ _).eqTrans (one_mul _)).eqSymm
  have a := natEq sA; have b := natEq fb; have c := natEq (sB.eqTrans sC)
  apply deriveNat; ipra_simps
  linear_combination a + b - c

end LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola
