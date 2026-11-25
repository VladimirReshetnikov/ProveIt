import IPRADerivations.AnalyticNumberTheory.EnergyJordan
import IPRADerivations.AnalyticNumberTheory.EnergyMobius
import IPRADerivations.Analysis.WeightedCauchySchwarz
import IPRADerivations.AnalyticNumberTheory.AbsDiff
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# Recovery of `M` from the energy: `(N!)² M(N)² ≤ 8 Q_N` (`thm:energy`)

Packet: `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`, `energy.tex`, proof of `thm:energy`:
"Weighted Cauchy–Schwarz now gives `M(N)² ≤ E_N Σ_{d≤N} μ(d)²/J_2(d) ≤ 8E_N`. It is an inequality between rationals,
obtainable by sums of squares and clearing denominators" (the packet's metatheory: `EnergyInequality.recover_eight`).

`M = M⁺ − M⁻` is any signed sequence given by two nonnegative bodies `M^±(n, x)`. With `X = ⟨N, x⟩`, `F = (N!)²`,
`T'_d = T⁺(d) − T⁻(d) = N! T_d` (`EnergyMobius`) and `a_d = |T'_d|`, the cleared energy is

  `Q_N = Σ_{d≤N} J₂(d) a_d² = (N!)² E_N`                                   (`QN`).

The cleared Cauchy–Schwarz data (`Analysis.WeightedCauchySchwarz.weighted_cs`) are `b_d = |μ(d)| N!`,
`w_d = J₂(d)`, `c_d = 4 ⌊F/d²⌋`:

* `b_d² ≤ w_d c_d` (`hb_pt`): `|μ(d)| ≤ 1` (`mu_abs_le`), `d² ⌊F/d²⌋ = F` since `d ∣ N!` (`sq_exact`), and
  `d² ≤ 4 J₂(d)` (`EnergyJordan.jordan_quarter`);
* `Σ_d c_d = 4 T(N, F) ≤ 8F` (`sum_c`, from `SquareReciprocal.square_bound`, `T_le`);
* `N! |M(N)| ≤ |Σ μ⁺T⁺ + μ⁻T⁻ − Σ μ⁺T⁻ + μ⁻T⁺| ≤ Σ_d |μ(d)| a_d` (`EnergyMobius.mobius_energy`,
  `AbsDiff.absd_sum`, `absd_alg`), so `(N!)² |M(N)| ≤ Σ_d a_d b_d`;
* `energy_recovery`: `(N!)⁴ M(N)² ≤ (Σ a b)² ≤ Q_N · 8F`, and one factor `F` cancels.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.EnergyRecovery

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.EnergyMobius (muS subst_muS tB gM mtS inst2_mtS posB negB mobius_energy
  quo_one)
open LeanProofs.IPRA.AnalyticNumberTheory.EnergyJordan (J2 jordan_quarter pos_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd absd_le le_absd_l le_absd_r scale_absd absd_sum adB inst2_adB)
open LeanProofs.IPRA.Analysis.WeightedCauchySchwarz (weighted_cs)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.SquareReciprocal (sqB inst2_sq square_bound sqInv cancel_le T_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (dvd_fact fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN inst2_mulB)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd')
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The bodies, over `0 = d'` (`d = d' + 1`), `1 = X = ⟨N, x⟩` -/

/-- `T^±(d)`. -/
abbrev tS (Ms : PTm 2) : PTm 2 := ap2 (sumF (tB (gM Ms))) (fstT (var 1)) (pairT (succ (var 0)) (var 1))
/-- `a_d = |T⁺(d) − T⁻(d)| = |N! T_d|`. -/
abbrev aB (Mp Mn : PTm 2) : PTm 2 := absd (tS Mp) (tS Mn)
/-- `|μ(d)| = μ⁺(d) + μ⁻(d)`. -/
abbrev amB : PTm 2 := muS true (succ (fstT (var 1))) (succ (var 0)) + muS false (succ (fstT (var 1))) (succ (var 0))
/-- `b_d = |μ(d)| N!`. -/
abbrev bB : PTm 2 := amB * fact (fstT (var 1))
/-- `w_d = J₂(d)`. -/
abbrev wB : PTm 2 := J2 (succ (var 0))
/-- `c_d = 4 ⌊(N!)²/d²⌋`. -/
abbrev cB : PTm 2 := num 4 * quo (fact (fstT (var 1)) * fact (fstT (var 1))) (succ (var 0) * succ (var 0))

/-- `Q_N = Σ_{d≤N} J₂(d) a_d² = (N!)² E_N`. -/
abbrev QN (Mp Mn : PTm 2) (N x : PTm n) : PTm n := ap2 (sumF (wB * (aB Mp Mn * aB Mp Mn))) N (pairT N x)

/-- `|M(N)| = |M⁺(N) − M⁻(N)|`. -/
abbrev Mabs (Mp Mn : PTm 2) (N x : PTm n) : PTm n := absd (inst2 Mp N x) (inst2 Mn N x)

theorem inst2_aB (Mp Mn : PTm 2) (d X : PTm n) : inst2 (aB Mp Mn) d X =
    absd (ap2 (sumF (tB (gM Mp))) (fstT X) (pairT (succ d) X)) (ap2 (sumF (tB (gM Mn))) (fstT X) (pairT (succ d) X)) := by
  simp [inst2]

theorem inst2_amB (d X : PTm n) : inst2 amB d X =
    muS true (succ (fstT X)) (succ d) + muS false (succ (fstT X)) (succ d) := by
  simp [inst2, subst_muS]

theorem inst2_bB (d X : PTm n) : inst2 bB d X =
    (muS true (succ (fstT X)) (succ d) + muS false (succ (fstT X)) (succ d)) * fact (fstT X) := by
  simp [inst2, subst_muS]

theorem inst2_wB (d X : PTm n) : inst2 wB d X = J2 (succ d) := by simp [inst2]

theorem inst2_cB (d X : PTm n) : inst2 cB d X =
    num 4 * quo (fact (fstT X) * fact (fstT X)) (succ d * succ d) := by simp [inst2]

/-! ## `|μ(d)| ≤ 1` -/

alias eqb_le_one := Common.eqb_le_one

theorem eqb01_le (r : PTm n) : Γ ⊢[PRAAx] le (eqb r zero + eqb r one) one := by
  refine .orE (eq_or_ne r zero) ?_ ?_
  · have ne : ((r ≐ zero) :: Γ) ⊢[PRAAx] neg (r ≐ one) :=
      .impI (succ_ne_zero' _ (Prf.hyp0.eqSymm.eqTrans Prf.hyp1))
    exact le_congr ((congrAdd (eqb_of_eq Prf.hyp0) (eqb_of_ne ne)).eqTrans (add_zero _)).eqSymm (.eqRefl _)
      (le_refl _)
  · exact le_congr ((congrAdd (eqb_of_ne Prf.hyp0) (.eqRefl _)).eqTrans (zero_add _)).eqSymm (.eqRefl _)
      (eqb_le_one _ _)

theorem mu_abs_le (B d : PTm n) : Γ ⊢[PRAAx] le (muS true B d + muS false B d) one := by
  show Γ ⊢[PRAAx] le (muP B d + muN B d) one
  have h := le_mul_mono (eqb_le_one (Γ := Γ) (Mobius.sq B d) zero) (eqb01_le (Γ := Γ) (rem (Mobius.om B d) two))
  exact le_congr (by ipra_ring) (by ipra_ring) h

/-! ## `b_d² ≤ w_d c_d` -/

theorem sq_alg {D f q : PTm n} (hf : Γ ⊢[PRAAx] f ≐ D * q) : Γ ⊢[PRAAx] f * f ≐ (D * D) * (q * q) + zero := by
  ipra_lc (𝔞 f + 𝔞 D * 𝔞 q) * natEq hf

theorem sq_alg' {D f q Qt : PTm n} (hf : Γ ⊢[PRAAx] f ≐ D * q) (hq : Γ ⊢[PRAAx] Qt ≐ q * q) :
    Γ ⊢[PRAAx] (D * D) * Qt ≐ f * f := by
  have e := natEq hf; have e' := natEq hq
  apply deriveNat; ipra_simps
  linear_combination 𝔞 D * 𝔞 D * e' - (𝔞 f + 𝔞 D * 𝔞 q) * e

/-- `d² ⌊(N!)²/d²⌋ = (N!)²` for `1 ≤ d ≤ N`. -/
theorem sq_exact {d' N : PTm n} (h : Γ ⊢[PRAAx] le (succ d') N) :
    Γ ⊢[PRAAx] (succ d' * succ d') * quo (fact N * fact N) (succ d' * succ d') ≐ fact N * fact N := by
  have fe := eq_of_dvd' (pos_succ d') (dvd_fact h)
  have q : Γ ⊢[PRAAx] quo (fact N * fact N) (succ d' * succ d') ≐
      quo (fact N) (succ d') * quo (fact N) (succ d') :=
    quo_eq (pos_mul (pos_succ d') (pos_succ d')) (sq_alg fe)
      (le_of_eq_add (d := d' * succ d' + d') (by ipra_ring))
  exact sq_alg' fe q

/-- Abstract form: `m ≤ 1`, `D q = f²`, `D ≤ 4J` give `(m f)² ≤ J · 4q`. -/
theorem hb_alg {m f J D q : PTm n} (hm : Γ ⊢[PRAAx] le m one) (hF : Γ ⊢[PRAAx] D * q ≐ f * f)
    (hJ : Γ ⊢[PRAAx] le D (num 4 * J)) : Γ ⊢[PRAAx] le ((m * f) * (m * f)) (J * (num 4 * q)) := by
  have a := le_mul_mono (le_mul_mono hm hm) (le_refl (f * f))
  have b := le_mul_mono hJ (le_refl q)
  have s1 : Γ ⊢[PRAAx] le ((m * f) * (m * f)) (f * f) :=
    le_congr (by ipra_ring) (by ipra_ring) a
  exact le_trans s1 (le_congr hF (by ipra_ring) b)

theorem hb_pt {d' N x : PTm n} (hd : Γ ⊢[PRAAx] lt d' N) :
    Γ ⊢[PRAAx] le (inst2 bB d' (pairT N x) * inst2 bB d' (pairT N x))
      (inst2 wB d' (pairT N x) * inst2 cB d' (pairT N x)) := by
  rw [inst2_bB, inst2_wB, inst2_cB]
  have h : Γ ⊢[PRAAx] le (succ d') (fstT (pairT N x)) := le_congr (.eqRefl _) (fst_pair _ _).eqSymm hd
  exact hb_alg (mu_abs_le _ _) (sq_exact h) (jordan_quarter d')

/-! ## `Σ c_d ≤ 8 (N!)²` -/

theorem four_pos : Γ ⊢[PRAAx] (num 4 : PTm n) ≐ succ (pred (num 4)) := congrSucc (pred_succ (num 3)).eqSymm

theorem T_alg {N T F : PTm n} (h : Γ ⊢[PRAAx] le (num 4 * N * T + num 4 * F) (num 7 * N * F)) :
    Γ ⊢[PRAAx] le (num 4 * (N * T)) (num 4 * (N * (two * F))) := by
  refine le_of_eq_add (d := N * F + num 4 * F + monus (num 7 * N * F) (num 4 * N * T + num 4 * F)) ?_
  ipra_lc natEq (eq_add_of_le h)

/-- `T(N, F) = Σ_{d≤N} ⌊F/d²⌋ ≤ 2F` for `N ≥ 1`. -/
theorem T_le {N F : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] le (SquareReciprocal.T N F) (two * F) := by
  refine .orE (zero_or_succ (pred N)) ?_ ?_
  · let Θ : List (Fm PTm n) := (pred N ≐ zero) :: Γ
    have e1 : Θ ⊢[PRAAx] SquareReciprocal.T N F ≐ SquareReciprocal.T (succ zero) F :=
      congrAp2 (sumF sqB) (hN.wk.eqTrans (congrSucc Prf.hyp0)) (.eqRefl _)
    have e2 : Θ ⊢[PRAAx] SquareReciprocal.T (succ zero) F ≐ F :=
      (T_succ zero F).eqTrans ((congrAdd (sum_zero _ _) ((congrAp2 quoF (.eqRefl _) (one_mul _)).eqTrans
        (quo_one F))).eqTrans (zero_add _))
    exact le_congr (e1.eqTrans e2).eqSymm (.eqRefl _) (le_of_eq_add (d := F) (by ipra_ring))
  · let Θ : List (Fm PTm n) := (pred N ≐ succ (pred (pred N))) :: Γ
    have hN' : Θ ⊢[PRAAx] N ≐ succ (succ (pred (pred N))) := hN.wk.eqTrans (congrSucc Prf.hyp0)
    have e1 : Θ ⊢[PRAAx] SquareReciprocal.T N F ≐ SquareReciprocal.T (succ (succ (pred (pred N)))) F :=
      congrAp2 (sumF sqB) hN' (.eqRefl _)
    have sb := square_bound (Γ := Θ) (pred (pred N)) F
    unfold sqInv at sb
    have c := cancel_le (pos_succ _) (cancel_le four_pos (T_alg sb))
    exact le_congr e1.eqSymm (.eqRefl _) c

theorem c_pt (j N x : PTm n) :
    Γ ⊢[PRAAx] inst2 cB j (pairT N x) ≐ num 4 * inst2 sqB j (fact N * fact N) := by
  rw [inst2_cB, inst2_sq]
  have f := congrAp2 (Γ := Γ) factF (fst_pair N x) (.eqRefl zero)
  exact congrMul (.eqRefl _) (congrAp2 quoF (congrMul f f) (.eqRefl _))

theorem sum_c {N x : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] le (ap2 (sumF cB) N (pairT N x)) (num 8 * (fact N * fact N)) := by
  have s := sum_scale (Γ := Γ) cB sqB N (num 4) (fact N * fact N) (pairT N x) (.allI (.impI ?_))
  · refine le_congr s.eqSymm (by ipra_ring) (le_mul_mono (le_refl (num 4)) (T_le hN))
  · have h4 : Syn.shift (num 4 : PTm n) = num 4 := by simp [Syn.shift]
    have hF : Syn.shift (fact N * fact N) = fact (Syn.shift N) * fact (Syn.shift N) := by simp [Syn.shift]
    rw [shift_pairT, h4, hF]
    exact c_pt _ _ _

/-! ## `N! |M(N)| ≤ Σ_d |μ(d)| a_d` -/

/-- `|(pA + qB) − (qA + pB)| ≤ (p + q)|A − B|`. -/
theorem absd_alg (p q A B : PTm n) :
    Γ ⊢[PRAAx] le (absd (p * A + q * B) (q * A + p * B)) ((p + q) * absd A B) := by
  have hA := le_absd_l (Γ := Γ) A B
  have hB := le_absd_r (Γ := Γ) A B
  refine absd_le ?_ ?_
  · exact le_congr (.eqRefl _) (by ipra_ring)
      (add_le_add₂ (le_mul_mono (le_refl p) hA) (le_mul_mono (le_refl q) hB))
  · exact le_congr (.eqRefl _) (by ipra_ring)
      (add_le_add₂ (le_mul_mono (le_refl q) hA) (le_mul_mono (le_refl p) hB))

/-- `P + u = R + v` gives `|v − u| ≤ |P − R|`. -/
theorem shift_alg {P R u v : PTm n} (e : Γ ⊢[PRAAx] P + u ≐ R + v) : Γ ⊢[PRAAx] le (absd v u) (absd P R) := by
  refine absd_le ?_ ?_
  · refine le_of_eq_add (d := monus (R + absd P R) P) ?_
    ipra_lc natEq (eq_add_of_le (le_absd_l (Γ := Γ) P R)) + natEq e
  · refine le_of_eq_add (d := monus (P + absd P R) R) ?_
    ipra_lc natEq (eq_add_of_le (le_absd_r (Γ := Γ) P R)) - natEq e

theorem abs_pt (Mp Mn : PTm 2) (d X : PTm n) :
    Γ ⊢[PRAAx] le (inst2 (adB (posB Mp Mn) (negB Mp Mn)) d X) (inst2 (amB * aB Mp Mn) d X) := by
  have L : inst2 (adB (posB Mp Mn) (negB Mp Mn)) d X =
      absd (muS true (succ (fstT X)) (succ d) * ap2 (sumF (tB (gM Mp))) (fstT X) (pairT (succ d) X) +
          muS false (succ (fstT X)) (succ d) * ap2 (sumF (tB (gM Mn))) (fstT X) (pairT (succ d) X))
        (muS false (succ (fstT X)) (succ d) * ap2 (sumF (tB (gM Mp))) (fstT X) (pairT (succ d) X) +
          muS true (succ (fstT X)) (succ d) * ap2 (sumF (tB (gM Mn))) (fstT X) (pairT (succ d) X)) := by
    simp only [inst2_adB, posB, negB, inst2_addBody, inst2_mtS]
  have R : inst2 (amB * aB Mp Mn) d X =
      (muS true (succ (fstT X)) (succ d) + muS false (succ (fstT X)) (succ d)) *
        absd (ap2 (sumF (tB (gM Mp))) (fstT X) (pairT (succ d) X))
          (ap2 (sumF (tB (gM Mn))) (fstT X) (pairT (succ d) X)) := by
    rw [inst2_mulB, inst2_amB, inst2_aB]
  rw [L, R]
  exact absd_alg _ _ _ _

theorem inst2_factB (j X : PTm n) : inst2 (fact (fstT (var 1)) : PTm 2) j X = fact (fstT X) := by simp [inst2]

theorem ab_pt (Mp Mn : PTm 2) (j N x : PTm n) :
    Γ ⊢[PRAAx] inst2 (aB Mp Mn * bB) j (pairT N x) ≐ fact N * inst2 (amB * aB Mp Mn) j (pairT N x) := by
  simp only [inst2_mulB, inst2_amB, inst2_factB]
  have f := congrAp2 (Γ := Γ) factF (fst_pair N x) (.eqRefl zero)
  refine (congrMul (.eqRefl _) (congrMul (.eqRefl _) f)).eqTrans ?_
  ipra_ring

/-! ## The recovery inequality -/

/-- `F · F · Y ≤ Q · 8F`-shaped closing step. -/
theorem close_alg {f m AB Qv C : PTm n} (h1 : Γ ⊢[PRAAx] le (f * (f * m)) AB)
    (h2 : Γ ⊢[PRAAx] le (AB * AB) (Qv * C)) (h3 : Γ ⊢[PRAAx] le C (num 8 * (f * f))) :
    Γ ⊢[PRAAx] le ((f * f) * ((f * f) * (m * m))) ((f * f) * (num 8 * Qv)) := by
  have a := le_mul_mono h1 h1
  have b := le_mul_mono (le_refl Qv) h3
  exact le_congr (by ipra_ring) (by ipra_ring)
    (le_trans a (le_trans h2 b))

/-- `thm:energy`, recovery direction, cleared: `(N!)² M(N)² ≤ 8 Q_N` for `N ≥ 1`. -/
theorem energy_recovery (Mp Mn : PTm 2) {N x : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] le ((fact N * fact N) * (Mabs Mp Mn N x * Mabs Mp Mn N x)) (num 8 * QN Mp Mn N x) := by
  -- `N! |M| ≤ |P − R| ≤ Σ |μ| a`
  have me := mobius_energy (Γ := Γ) Mp Mn (x := x) hN
  have s1 := le_trans (scale_absd (Γ := Γ) (fact N) (inst2 Mp N x) (inst2 Mn N x)) (shift_alg me)
  have s2 := absd_sum (Γ := Γ) (posB Mp Mn) (negB Mp Mn) N (pairT N x)
  have s3 := sum_le_params (Γ := Γ) (adB (posB Mp Mn) (negB Mp Mn)) (amB * aB Mp Mn) (pairT N x) (pairT N x) N
    (.allI (.impI (abs_pt Mp Mn _ _)))
  have s4 := le_trans s1 (le_trans s2 s3)
  -- `(N!)² |M| ≤ Σ a b`
  have ab := sum_scale (Γ := Γ) (aB Mp Mn * bB) (amB * aB Mp Mn) N (fact N) (pairT N x) (pairT N x) (.allI (.impI (by
    have hF : Syn.shift (fact N) = fact (Syn.shift N) := by simp [Syn.shift]
    rw [shift_pairT, hF]
    exact ab_pt Mp Mn _ _ _)))
  have h1 := le_congr (.eqRefl _) ab.eqSymm (le_mul_mono (le_refl (fact N)) s4)
  -- Cauchy–Schwarz
  have cs := weighted_cs (Γ := Γ) (a := aB Mp Mn) (b := bB) (w := wB) (c := cB) (x := pairT N x) (N := N)
    (.allI (.impI (by
      rw [shift_pairT]
      exact hb_pt Prf.hyp0)))
  have h3 := sum_c (Γ := Γ) (x := x) hN
  have fin := close_alg h1 cs h3
  exact cancel_le (pos_mul (fact_pos N) (fact_pos N)) fin

/-- Variables `0 = N'` (`N = N' + 1`), `1 = x`: `(N!)² M(N)² ≤ 8 Q_N`. -/
abbrev recoveryFormula (Mp Mn : PTm 2) : Fm PTm 2 :=
  le ((fact (succ (var 0)) * fact (succ (var 0))) * (Mabs Mp Mn (succ (var 0)) (var 1) * Mabs Mp Mn (succ (var 0)) (var 1)))
    (num 8 * QN Mp Mn (succ (var 0)) (var 1))

/-- The recovery inequality as a closed sentence of iPRA, for every pair of bodies `M^±`. -/
theorem energy_recovery_closed (Mp Mn : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (recoveryFormula Mp Mn) :=
  closeUniv 2 (energy_recovery Mp Mn (pos_succ _))

end LeanProofs.IPRA.AnalyticNumberTheory.EnergyRecovery
