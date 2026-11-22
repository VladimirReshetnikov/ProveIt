import IPRADerivations.AnalyticNumberTheory.MobiusBounds
import IPRADerivations.Probability.Independence

/-!
# Divisor inversion for the energy statistic (`thm:energy`, recovery direction)

Packet: `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`, `energy.tex`, proof of `thm:energy`:
"For recovery, divisor inversion gives `Σ_{d≤N} μ(d) T_d = Σ_{k≤N} (m_k/k) Σ_{d∣k} μ(d) = M(N)`", where
`m_k = M(⌊N/k⌋)` and `T_d = Σ_{d∣k≤N} m_k/k`. "The two signs … are accumulated separately in each `N! T_d`."

Generic layer, for any body `g(i, Z)` (the term at `k = i + 1`) and a parameter `Z` with `N = fst Z ≥ 1`:

* `T_g(d) = Σ_{i<N} [d ∣ i+1] g(i)` (`tB`), and the rows `μ^±(d) T_g(d)` for `d = d'+1 ≤ N` (`mtS`), with the
  Möbius values `μ^±_{N+1}(d)` of `AnalyticNumberTheory/Mobius` (`muS`);
* `mobius_rows`: `Σ_{d≤N} μ⁺(d) T_g(d) = Σ_{d≤N} μ⁻(d) T_g(d) + g(0)`. The double sum is exchanged
  (`fubini`); in the column of `k = i + 1` the factor `Σ_{d∣k} μ(d) = [k = 1]` is `MobiusBounds.cancel_gen`.

The energy instance (`gM`): for a signed sequence `M = M⁺ − M⁻` given by two nonnegative bodies `M^±(n, x)`, the
cleared term is `g^±(i) = ⌊N!/k⌋ M^±(⌊N/k⌋, x)`, so `T^±(d) = Σ_{d∣k≤N} ⌊N!/k⌋ M^±(⌊N/k⌋)` and
`T'_d = T⁺(d) − T⁻(d) = N! T_d` (every `⌊N!/k⌋` is exact for `k ≤ N`, `Primes.dvd_fact`). Then

  `Σ_{d≤N} (μ⁺T⁺ + μ⁻T⁻)(d) + N! M⁻(N) = Σ_{d≤N} (μ⁺T⁻ + μ⁻T⁺)(d) + N! M⁺(N)`    (`mobius_energy`),

i.e. `Σ_{d≤N} μ(d) T'_d = N! M(N)`. No floor matters for the identity itself; only `⌊N!/1⌋ = N!` is used.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.EnergyMobius

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN lB inst2_lB inst2_mulB congrEqb' zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (GP GN inst2_GP inst2_GN congrMu cancel_gen)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Probability.Independence (dsum dsum_rows sum_scale row_pt col_pt shift_inst2 inst3_mul')
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Signed Möbius values -/

/-- `μ⁺_B(d)` (`s = true`) or `μ⁻_B(d)` (`s = false`). -/
def muS {k : ℕ} (s : Bool) (B d : PTm k) : PTm k := match s with
  | true => muP B d
  | false => muN B d

theorem subst_muS {k m : ℕ} (σ : Fin k → PTm m) (s : Bool) (B d : PTm k) :
    Syn.subst σ (muS s B d) = muS s (Syn.subst σ B) (Syn.subst σ d) := by
  cases s <;> simp [muS]

theorem shift_muS (s : Bool) (B d : PTm n) : Syn.shift (muS s B d) = muS s (Syn.shift B) (Syn.shift d) := by
  cases s <;> simp [muS, Syn.shift]

theorem congrMuS (s : Bool) {B B' d : PTm n} (h : Γ ⊢[PRAAx] B ≐ B') : Γ ⊢[PRAAx] muS s B d ≐ muS s B' d := by
  cases s
  · exact Prf.andE₂ (congrMu h)
  · exact Prf.andE₁ (congrMu h)

/-- `[d ≥ 1][d ∣ k] μ^±_N(d)` with `y = ⟨N, k⟩`. -/
def GS (s : Bool) : PTm 2 := match s with
  | true => GP
  | false => GN

theorem inst2_GS (s : Bool) (d y : PTm n) :
    inst2 (GS s) d y = (sg d * eqb (rem (sndT y) d) zero) * muS s (fstT y) d := by
  cases s
  · exact inst2_GN d y
  · exact inst2_GP d y

theorem shift_fstT (Z : PTm n) : Syn.shift (fstT Z) = fstT (Syn.shift Z) := by simp [Syn.shift]

/-! ## The bodies -/

section Generic

variable (g : PTm 2)

/-- `[d ∣ i + 1] g(i, Z)` with `y = ⟨d, Z⟩`. -/
def tB : PTm 2 := eqb (rem (succ (var 0)) (fstT (var 1))) zero * lB g

theorem inst2_tB (i y : PTm n) : inst2 (tB g) i y = eqb (rem (succ i) (fstT y)) zero * inst2 g i (sndT y) := by
  simp only [tB]
  rw [inst2_mulB, inst2_lB]
  simp [inst2]

/-- `g(i, Z)` read in a three-variable body `(d, i, Z)`. -/
theorem inst3_sub12 (d i Z : PTm n) : inst3 (Syn.subst ![var 1, var 2] g : PTm 3) d i Z = inst2 g i Z := by
  simp only [inst3, inst2, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> rfl

/-- `μ^±_{N+1}(d+1) [d+1 ∣ i+1] g(i, Z)`, over `0 = d`, `1 = i`, `2 = Z`, with `N = fst Z`. -/
def aS (s : Bool) : PTm 3 := muS s (succ (fstT (var 2))) (succ (var 0)) *
  (eqb (rem (succ (var 1)) (succ (var 0))) zero * Syn.subst ![var 1, var 2] g)

theorem inst3_aS (s : Bool) (d i Z : PTm n) : inst3 (aS g s) d i Z =
    muS s (succ (fstT Z)) (succ d) * (eqb (rem (succ i) (succ d)) zero * inst2 g i Z) := by
  simp only [aS]
  rw [inst3_mul', inst3_mul', inst3_sub12]
  have h1 : inst3 (muS s (succ (fstT (var 2))) (succ (var 0)) : PTm 3) d i Z = muS s (succ (fstT Z)) (succ d) := by
    simp [inst3, subst_muS]
  have h2 : inst3 (eqb (rem (succ (var 1)) (succ (var 0))) zero : PTm 3) d i Z = eqb (rem (succ i) (succ d)) zero := by
    simp [inst3]
  rw [h1, h2]

/-- The row `μ^±(d+1) T_g(d+1)`, over `0 = d`, `1 = Z`. -/
def mtS (s : Bool) : PTm 2 := muS s (succ (fstT (var 1))) (succ (var 0)) *
  ap2 (sumF (tB g)) (fstT (var 1)) (pairT (succ (var 0)) (var 1))

theorem inst2_mtS (s : Bool) (d Z : PTm n) : inst2 (mtS g s) d Z =
    muS s (succ (fstT Z)) (succ d) * ap2 (sumF (tB g)) (fstT Z) (pairT (succ d) Z) := by
  simp [inst2, mtS, subst_muS]

/-! ## Rows -/

theorem row_point (s : Bool) (i d Z : PTm n) : Γ ⊢[PRAAx] inst2 (rowB (aS g s)) i (pairT d Z) ≐
    muS s (succ (fstT Z)) (succ d) * inst2 (tB g) i (pairT (succ d) Z) := by
  refine (row_pt (aS g s) d i Z).eqTrans ?_
  rw [inst3_aS, inst2_tB]
  exact congrMul (.eqRefl _) (congrMul (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _).eqSymm) (.eqRefl _))
    (congrInst2 g (.eqRefl _) (snd_pair _ _).eqSymm))

theorem row_mt (s : Bool) (d Z : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB (aS g s))) (fstT Z) (pairT d Z) ≐ inst2 (mtS g s) d Z := by
  rw [inst2_mtS]
  refine sum_scale (rowB (aS g s)) (tB g) (fstT Z) (muS s (succ (fstT Z)) (succ d)) (pairT (succ d) Z) (pairT d Z)
    (.allI (.impI ?_))
  simp only [shift_pairT, shift_muS, shift_succ'', shift_fstT]
  exact row_point g s _ _ _

/-! ## Columns -/

theorem col_point (s : Bool) (d i Z : PTm n) : Γ ⊢[PRAAx] inst2 (colB (aS g s)) d (pairT i Z) ≐
    inst2 g i Z * inst2 (shiftBody (GS s)) d (pairT (succ (fstT Z)) (succ i)) := by
  refine (col_pt (aS g s) d i Z).eqTrans ?_
  rw [inst3_aS, inst2_shiftBody, inst2_GS]
  have e1 : Γ ⊢[PRAAx] sg (succ d) * eqb (rem (sndT (pairT (succ (fstT Z)) (succ i))) (succ d)) zero ≐
      eqb (rem (succ i) (succ d)) zero :=
    (congrMul (sg_succ _) (congrEqb' (congrAp2 remF (snd_pair _ _) (.eqRefl _)) (.eqRefl _))).eqTrans (one_mul _)
  have e2 := congrMuS (Γ := Γ) s (d := succ d) (fst_pair (succ (fstT Z)) (succ i))
  refine .eqTrans ?_ (congrMul (.eqRefl _) (congrMul e1 e2)).eqSymm
  apply deriveNat; ipra_simps; ring

theorem col_eq (s : Bool) (i Z : PTm n) : Γ ⊢[PRAAx] inst2 (pB (aS g s)) i (pairT (fstT Z) Z) ≐
    inst2 g i Z * ap2 (sumF (shiftBody (GS s))) (fstT Z) (pairT (succ (fstT Z)) (succ i)) := by
  rw [inst2_pB]
  refine (congrAp2 (sumF (colB (aS g s))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  refine sum_scale (colB (aS g s)) (shiftBody (GS s)) (fstT Z) (inst2 g i Z) (pairT (succ (fstT Z)) (succ i))
    (pairT i Z) (.allI (.impI ?_))
  simp only [shift_pairT, shift_inst2, shift_succ'', shift_fstT]
  exact col_point g s _ _ _

/-- In the column of `k = i + 1 ≤ N`: `Σ_{d∣k} μ⁺(d) g = Σ_{d∣k} μ⁻(d) g + [k = 1] g`. -/
theorem col_cancel {i Z : PTm n} (hi : Γ ⊢[PRAAx] lt i (fstT Z)) :
    Γ ⊢[PRAAx] inst2 (pB (aS g true)) i (pairT (fstT Z) Z) ≐
      inst2 (pB (aS g false)) i (pairT (fstT Z) Z) + inst2 g i Z * eqb (succ i) one := by
  have cP := natEq (col_eq (Γ := Γ) g true i Z)
  have cN := natEq (col_eq (Γ := Γ) g false i Z)
  have g0 : ∀ s : Bool, Γ ⊢[PRAAx] inst2 (GS s) zero (pairT (succ (fstT Z)) (succ i)) ≐ zero := by
    intro s; rw [inst2_GS]; exact zero_mul_l (zero_mul_l sg_zero _) _
  have z1 := natEq (g0 true); have z2 := natEq (g0 false)
  have shP := natEq (sum_shift (Γ := Γ) (GS true) (fstT Z) (pairT (succ (fstT Z)) (succ i)))
  have shN := natEq (sum_shift (Γ := Γ) (GS false) (fstT Z) (pairT (succ (fstT Z)) (succ i)))
  have hk : Γ ⊢[PRAAx] succ i ≐ succ (pred (succ i)) := congrSucc (pred_succ _).eqSymm
  have hle : Γ ⊢[PRAAx] le (succ (succ i)) (succ (fstT Z)) := (succ_monus_succ _ _).eqTrans hi
  have cg : Γ ⊢[PRAAx] ap2 (sumF (GS true)) (succ (fstT Z)) (pairT (succ (fstT Z)) (succ i)) ≐
      ap2 (sumF (GS false)) (succ (fstT Z)) (pairT (succ (fstT Z)) (succ i)) + eqb (succ i) one :=
    cancel_gen hk hle hle
  have c := natEq cg
  apply deriveNat; ipra_simps
  linear_combination cP - cN + 𝔞 (inst2 g i Z) * (-shP + shN - z1 + z2 + c)

/-- `g(i, snd y) [i + 1 = 1]`. -/
def dlB : PTm 2 := lB g * eqb (succ (var 0)) one

theorem inst2_dl (i y : PTm n) : inst2 (dlB g) i y = inst2 g i (sndT y) * eqb (succ i) one := by
  simp only [dlB]
  rw [inst2_mulB, inst2_lB]
  simp [inst2]

theorem zero_inst2 (i y : PTm n) : inst2 (zero : PTm 2) i y = zero := by simp [inst2]

theorem dl_sum {Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z))) :
    Γ ⊢[PRAAx] ap2 (sumF (dlB g)) (fstT Z) (pairT (fstT Z) Z) ≐ inst2 g zero Z := by
  refine (congrAp2 (sumF (dlB g)) hN (.eqRefl _)).eqTrans ((sum_shift (dlB g) _ _).eqTrans ?_)
  have z : Γ ⊢[PRAAx] ap2 (sumF (shiftBody (dlB g))) (pred (fstT Z)) (pairT (fstT Z) Z) ≐ zero := by
    refine (sum_congr_bounded (shiftBody (dlB g)) (zero : PTm 2) _ (pairT (fstT Z) Z) _ (.allI (.impI ?_))).eqTrans
      (sum_zeroB _ _)
    rw [inst2_shiftBody, inst2_dl, zero_inst2]
    have ne : (lt (var 0) (Syn.shift (pred (fstT Z))) :: Γ.map Fm.shift) ⊢[PRAAx]
        neg (succ (succ (var 0)) ≐ one) :=
      .impI (succ_ne_zero' _ ((pred_succ _).eqSymm.eqTrans ((congrPred Prf.hyp0).eqTrans (pred_succ _))))
    exact (congrMul (.eqRefl _) (eqb_of_ne ne)).eqTrans (mul_zero _)
  rw [inst2_dl]
  have e0 : Γ ⊢[PRAAx] inst2 g zero (sndT (pairT (fstT Z) Z)) * eqb (succ zero) one ≐ inst2 g zero Z :=
    (congrMul (congrInst2 g (.eqRefl _) (snd_pair _ _)) (eqb_of_eq (.eqRefl _))).eqTrans (by apply deriveNat; ipra_simps; ring)
  exact (congrAdd e0 z).eqTrans (add_zero _)

/-- Divisor inversion for any body: `Σ_{d≤N} μ⁺(d) T_g(d) = Σ_{d≤N} μ⁻(d) T_g(d) + g(0)`, `N = fst Z ≥ 1`. -/
theorem mobius_rows {Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z))) :
    Γ ⊢[PRAAx] ap2 (sumF (mtS g true)) (fstT Z) Z ≐ ap2 (sumF (mtS g false)) (fstT Z) Z + inst2 g zero Z := by
  have rows : ∀ s : Bool, Γ ⊢[PRAAx] dsum (aS g s) (fstT Z) (fstT Z) Z ≐ ap2 (sumF (mtS g s)) (fstT Z) Z :=
    fun s => dsum_rows (aS g s) (mtS g s) _ _ Z Z (.allI (.impI (by
      simp only [shift_fstT]
      exact row_mt g s _ _)))
  have fP := fubini (Γ := Γ) (aS g true) (fstT Z) (fstT Z) Z
  have fN := fubini (Γ := Γ) (aS g false) (fstT Z) (fstT Z) Z
  have cP : Γ ⊢[PRAAx] ap2 (sumF (pB (aS g true))) (fstT Z) (pairT (fstT Z) Z) ≐
      ap2 (sumF (addBody (pB (aS g false)) (dlB g))) (fstT Z) (pairT (fstT Z) Z) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [inst2_addBody, shift_pairT, shift_fstT]
    refine (col_cancel g Prf.hyp0).eqTrans (congrAdd (.eqRefl _) ?_)
    rw [inst2_dl]
    exact congrMul (congrInst2 g (.eqRefl _) (snd_pair _ _)).eqSymm (.eqRefl _)
  have sa := sum_add (Γ := Γ) (pB (aS g false)) (dlB g) (fstT Z) (pairT (fstT Z) Z)
  exact (rows true).eqSymm.eqTrans (fP.eqTrans (cP.eqTrans (sa.eqTrans
    (congrAdd (fN.eqSymm.eqTrans (rows false)) (dl_sum g hN)))))

end Generic

/-! ## The energy instance -/

/-- `g^±(i, ⟨N, x⟩) = ⌊N!/(i+1)⌋ M^±(⌊N/(i+1)⌋, x)`. -/
def gM (Ms : PTm 2) : PTm 2 :=
  quo (fact (fstT (var 1))) (succ (var 0)) * Syn.subst ![quo (fstT (var 1)) (succ (var 0)), sndT (var 1)] Ms

theorem inst2_gM (Ms : PTm 2) (i Z : PTm n) : inst2 (gM Ms) i Z =
    quo (fact (fstT Z)) (succ i) * inst2 Ms (quo (fstT Z) (succ i)) (sndT Z) := by
  simp only [gM]
  rw [inst2_mulB]
  have h1 : inst2 (quo (fact (fstT (var 1))) (succ (var 0)) : PTm 2) i Z = quo (fact (fstT Z)) (succ i) := by
    simp [inst2]
  have h2 : inst2 (Syn.subst ![quo (fstT (var 1)) (succ (var 0)), sndT (var 1)] Ms : PTm 2) i Z =
      inst2 Ms (quo (fstT Z) (succ i)) (sndT Z) := by
    simp only [inst2, Syn.subst_subst]
    congr 1; funext k; fin_cases k <;> simp
  rw [h1, h2]

theorem quo_one (z : PTm n) : Γ ⊢[PRAAx] quo z (succ zero) ≐ z :=
  quo_eq (q := z) (r := zero) (congrSucc (pred_succ _).eqSymm) (by apply deriveNat; ipra_simps; ring) (le_refl _)

/-- `g^±(0) = N! M^±(N, x)`. -/
theorem gM_zero (Ms : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] inst2 (gM Ms) zero (pairT N x) ≐ fact N * inst2 Ms N x := by
  rw [inst2_gM]
  have f := fst_pair (Γ := Γ) N x
  have s := snd_pair (Γ := Γ) N x
  exact congrMul ((quo_one _).eqTrans (congrAp2 factF f (.eqRefl _)))
    (congrInst2 Ms ((quo_one _).eqTrans f) s)

/-- `T^±(d) = Σ_{d∣k≤N} ⌊N!/k⌋ M^±(⌊N/k⌋, x)` (the two signs of `N! T_d`). -/
abbrev Tpm (Ms : PTm 2) (N x d : PTm n) : PTm n := ap2 (sumF (tB (gM Ms))) N (pairT d (pairT N x))

/-- `μ⁺T⁺ + μ⁻T⁻` at `d + 1`, over `0 = d`, `1 = ⟨N, x⟩`. -/
abbrev posB (Mp Mn : PTm 2) : PTm 2 := addBody (mtS (gM Mp) true) (mtS (gM Mn) false)
/-- `μ⁺T⁻ + μ⁻T⁺` at `d + 1`. -/
abbrev negB (Mp Mn : PTm 2) : PTm 2 := addBody (mtS (gM Mp) false) (mtS (gM Mn) true)

/-- `Σ_{d≤N} μ(d) T'_d = N! M(N)` in two-sign form, `N ≥ 1`. -/
theorem mobius_energy (Mp Mn : PTm 2) {N x : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF (posB Mp Mn)) N (pairT N x) + fact N * inst2 Mn N x ≐
      ap2 (sumF (negB Mp Mn)) N (pairT N x) + fact N * inst2 Mp N x := by
  have f := fst_pair (Γ := Γ) N x
  have hZ : Γ ⊢[PRAAx] fstT (pairT N x) ≐ succ (pred (fstT (pairT N x))) :=
    f.eqTrans (hN.eqTrans (congrSucc (congrPred f.eqSymm)))
  have rP := natEq ((congrAp2 (sumF (mtS (gM Mp) true)) f.eqSymm (.eqRefl _)).eqTrans
    ((mobius_rows (gM Mp) hZ).eqTrans (congrAdd (congrAp2 (sumF (mtS (gM Mp) false)) f (.eqRefl _)) (gM_zero Mp N x))))
  have rN := natEq ((congrAp2 (sumF (mtS (gM Mn) true)) f.eqSymm (.eqRefl _)).eqTrans
    ((mobius_rows (gM Mn) hZ).eqTrans (congrAdd (congrAp2 (sumF (mtS (gM Mn) false)) f (.eqRefl _)) (gM_zero Mn N x))))
  have s1 := natEq (sum_add (Γ := Γ) (mtS (gM Mp) true) (mtS (gM Mn) false) N (pairT N x))
  have s2 := natEq (sum_add (Γ := Γ) (mtS (gM Mp) false) (mtS (gM Mn) true) N (pairT N x))
  apply deriveNat; ipra_simps
  linear_combination s1 - s2 + rP - rN

end LeanProofs.IPRA.AnalyticNumberTheory.EnergyMobius
