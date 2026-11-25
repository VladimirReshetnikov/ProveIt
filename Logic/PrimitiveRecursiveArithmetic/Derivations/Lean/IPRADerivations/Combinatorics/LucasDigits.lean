import IPRADerivations.Combinatorics.LucasStep
import IPRADerivations.AnalyticNumberTheory.ConvolutionAssoc
import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.Foundations.MixedRadix
import IPRADerivations.Core.LinearCombination

/-!
# Lucas's binomial congruence

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, `el:lucas`:

  "Let `p` be prime and write `n = ∑ n_i p^i` and `k = ∑ k_i p^i` with digits in `[0, p)`, padding with zeros to
  the same finite length. Then `C(n, k) ≡ ∏_i C(n_i, k_i) (mod p)`, where a binomial coefficient with lower index
  exceeding the upper is zero."

The digit `i` of `N` in base `p` is `⌊N/p^i⌋ mod p`, and the product over the digits below `L` is

    D_L(N, K) = ∏_{i < L} C(⌊N/p^i⌋ mod p, ⌊K/p^i⌋ mod p)                                         (`DP`).

* **`lucas_digits`**: `C(N, K) ≡ D_L(N, K) · C(⌊N/p^L⌋, ⌊K/p^L⌋) (mod p)` for every `L`, by induction on `L` with
  `LucasStep.lucas_step` applied to `⌊N/p^L⌋`, `⌊K/p^L⌋` (and `⌊⌊N/p^L⌋/p⌋ = ⌊N/p^{L+1}⌋`);
* **`lucas`**: `C(N, K) ≡ D_L(N, K) (mod p)` when `N, K < p^L`;
* `lucas_self`: the length `L = N + K` always suffices (`N + K < p^{N+K}`).

The coefficients are the guarded `gb` of `Combinatorics/Vandermonde`, zero when the lower index exceeds the upper.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.LucasDigits

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero)
open LeanProofs.IPRA.Combinatorics.LucasStep (lucas_step)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (prime_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (lt_pw pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (quo_quo)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_mul_congr2)
open LeanProofs.IPRA.Foundations.BoundedReflection (eq_of_eqb)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The digit product; parameter `⟨p, ⟨N, K⟩⟩` -/

abbrev Y (p N K : PTm n) : PTm n := pairT p (pairT N K)

theorem Y_p (p N K : PTm n) : Γ ⊢[PRAAx] fstT (Y p N K) ≐ p := fst_pair _ _
theorem Y_N (p N K : PTm n) : Γ ⊢[PRAAx] fstT (sndT (Y p N K)) ≐ N :=
  (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
theorem Y_K (p N K : PTm n) : Γ ⊢[PRAAx] sndT (sndT (Y p N K)) ≐ K :=
  (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)

/-- `C(⌊N/p^i⌋ mod p, ⌊K/p^i⌋ mod p)`, over `0 = i`, `1 = ⟨p, ⟨N, K⟩⟩`. -/
abbrev dgB : PTm 2 :=
  gb (rem (quo (fstT (sndT (var 1))) (pw (fstT (var 1)) (var 0))) (fstT (var 1)))
    (rem (quo (sndT (sndT (var 1))) (pw (fstT (var 1)) (var 0))) (fstT (var 1)))

theorem inst2_dg (i y : PTm n) :
    inst2 dgB i y = gb (rem (quo (fstT (sndT y)) (pw (fstT y) i)) (fstT y))
      (rem (quo (sndT (sndT y)) (pw (fstT y) i)) (fstT y)) := by simp [inst2]

theorem dg_at (i p N K : PTm n) :
    Γ ⊢[PRAAx] inst2 dgB i (Y p N K) ≐ gb (rem (quo N (pw p i)) p) (rem (quo K (pw p i)) p) := by
  rw [inst2_dg]
  exact congrGb
    (congrAp2 remF (congrAp2 quoF (Y_N p N K) (congrPw (Y_p p N K) (.eqRefl _))) (Y_p p N K))
    (congrAp2 remF (congrAp2 quoF (Y_K p N K) (congrPw (Y_p p N K) (.eqRefl _))) (Y_p p N K))

/-- `D_L(N, K) = ∏_{i < L} C(⌊N/p^i⌋ mod p, ⌊K/p^i⌋ mod p)`. -/
abbrev DP (p L N K : PTm n) : PTm n := ap2 (prodF dgB) L (Y p N K)

/-! ## Base and step -/

theorem base_alg {G G' D : PTm n} (hD : Γ ⊢[PRAAx] D ≐ one) (hG : Γ ⊢[PRAAx] G' ≐ G) :
    Γ ⊢[PRAAx] G ≐ D * G' := by
  ipra_lc -(𝔞 G') * natEq hD - natEq hG

theorem lucas_base (p N K : PTm n) :
    Γ ⊢[PRAAx] rem (gb N K) p ≐
      rem (DP p zero N K * gb (quo N (pw p zero)) (quo K (pw p zero))) p := by
  have q1 : ∀ X : PTm n, Γ ⊢[PRAAx] quo X (pw p zero) ≐ X := fun X =>
    (congrAp2 quoF (.eqRefl _) (pw_zero p)).eqTrans (AnalyticNumberTheory.RSA.quo_one X)
  exact congrAp2 remF (base_alg (prod_zero dgB (Y p N K)) (congrGb (q1 N) (q1 K))) (.eqRefl _)

theorem step_alg {X G D P' G' : PTm n} (hP : Γ ⊢[PRAAx] P' ≐ X * D) (hG : Γ ⊢[PRAAx] G' ≐ G) :
    Γ ⊢[PRAAx] X * (G * D) ≐ P' * G' := by
  ipra_lc -(𝔞 G') * natEq hP - 𝔞 X * 𝔞 D * natEq hG

theorem lucas_succ {p L N K : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (ih : Γ ⊢[PRAAx] rem (gb N K) p ≐ rem (DP p L N K * gb (quo N (pw p L)) (quo K (pw p L))) p) :
    Γ ⊢[PRAAx] rem (gb N K) p ≐
      rem (DP p (succ L) N K * gb (quo N (pw p (succ L))) (quo K (pw p (succ L)))) p := by
  have ppos := prime_eq_succ_pred hp
  have wpos := pw_pos' ppos L
  have ls := lucas_step hp (quo N (pw p L)) (quo K (pw p L))
  have s1 := rem_mul_congr2 ppos (.eqRefl (rem (DP p L N K) p)) ls
  have qq : ∀ X : PTm n, Γ ⊢[PRAAx] quo (quo X (pw p L)) p ≐ quo X (pw p (succ L)) := fun X =>
    (quo_quo wpos ppos).eqTrans (congrAp2 quoF (.eqRefl _) (pw_succ p L).eqSymm)
  have eP : Γ ⊢[PRAAx] DP p (succ L) N K ≐
      DP p L N K * gb (rem (quo N (pw p L)) p) (rem (quo K (pw p L)) p) :=
    (Foundations.MixedRadix.prod_succ' dgB L (Y p N K)).eqTrans (congrMul (.eqRefl _) (dg_at L p N K))
  exact ih.eqTrans (s1.eqTrans (congrAp2 remF (step_alg eP (congrGb (qq N) (qq K)).eqSymm) (.eqRefl _)))

/-! ## The induction on the length -/

/-- `[C(N, K) mod p = (D_L · C(⌊N/p^L⌋, ⌊K/p^L⌋)) mod p]`, over `0 = L`, `1 = ⟨p, ⟨N, K⟩⟩`. -/
abbrev stB : PTm 2 :=
  eqb (rem (gb (fstT (sndT (var 1))) (sndT (sndT (var 1)))) (fstT (var 1)))
    (rem (ap2 (prodF dgB) (var 0) (var 1) *
      gb (quo (fstT (sndT (var 1))) (pw (fstT (var 1)) (var 0)))
        (quo (sndT (sndT (var 1))) (pw (fstT (var 1)) (var 0)))) (fstT (var 1)))

theorem inst2_st (L y : PTm n) :
    inst2 stB L y = eqb (rem (gb (fstT (sndT y)) (sndT (sndT y))) (fstT y))
      (rem (ap2 (prodF dgB) L y *
        gb (quo (fstT (sndT y)) (pw (fstT y) L)) (quo (sndT (sndT y)) (pw (fstT y) L))) (fstT y)) := by
  simp [inst2]

theorem st_at (L p N K : PTm n) :
    Γ ⊢[PRAAx] inst2 stB L (Y p N K) ≐
      eqb (rem (gb N K) p) (rem (DP p L N K * gb (quo N (pw p L)) (quo K (pw p L))) p) := by
  rw [inst2_st]
  exact AnalyticNumberTheory.Euler.congrEqb
    (congrAp2 remF (congrGb (Y_N p N K) (Y_K p N K)) (Y_p p N K))
    (congrAp2 remF (congrMul (.eqRefl _)
      (congrGb (congrAp2 quoF (Y_N p N K) (congrPw (Y_p p N K) (.eqRefl _)))
        (congrAp2 quoF (Y_K p N K) (congrPw (Y_p p N K) (.eqRefl _))))) (Y_p p N K))

theorem st_zero (p N K : PTm n) : Γ ⊢[PRAAx] inst2 stB zero (Y p N K) ≐ one :=
  (st_at zero p N K).eqTrans (eqb_of_eq (lucas_base p N K))

theorem st_succ {p L N K : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (ih : Γ ⊢[PRAAx] inst2 stB L (Y p N K) ≐ one) : Γ ⊢[PRAAx] inst2 stB (succ L) (Y p N K) ≐ one :=
  (st_at (succ L) p N K).eqTrans
    (eqb_of_eq (lucas_succ hp (eq_of_eqb ((st_at L p N K).eqSymm.eqTrans ih))))

/-- **Lucas's congruence with a remaining block**: for a prime `p` and every `L`,
`C(N, K) ≡ D_L(N, K) · C(⌊N/p^L⌋, ⌊K/p^L⌋) (mod p)`. -/
theorem lucas_digits {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (L N K : PTm n) :
    Γ ⊢[PRAAx] rem (gb N K) p ≐ rem (DP p L N K * gb (quo N (pw p L)) (quo K (pw p L))) p := by
  have sY : Syn.shift (Y p N K) = Y (Syn.shift p) (Syn.shift N) (Syn.shift K) := by simp [Syn.shift]
  have hall : Γ ⊢[PRAAx] Fm.all (inst2 stB (var 0) (Syn.shift (Y p N K)) ≐ one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact st_zero p N K
    · simp only [Fm.subst_eq, subst_inst2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      rw [sY]
      exact st_succ (prime_shift hp).wk Prf.hyp0
  have h2 := Prf.allE L hall
  simp only [Fm.subst_eq, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact eq_of_eqb ((st_at L p N K).eqSymm.eqTrans h2)

/-! ## Lucas's congruence -/

theorem quo_small {X M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (h : Γ ⊢[PRAAx] lt X M) :
    Γ ⊢[PRAAx] quo X M ≐ zero :=
  quo_eq hM (q := zero) (r := X) (by ipra_ring) h

theorem last_alg {D G : PTm n} (hG : Γ ⊢[PRAAx] G ≐ one) : Γ ⊢[PRAAx] D * G ≐ D := by
  ipra_lc 𝔞 D * natEq hG

/-- **Lucas's binomial congruence**: for a prime `p` and `N, K < p^L`,
`C(N, K) ≡ ∏_{i < L} C(N_i, K_i) (mod p)` with the base-`p` digits `N_i = ⌊N/p^i⌋ mod p`. -/
theorem lucas {p L N K : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hN : Γ ⊢[PRAAx] lt N (pw p L))
    (hK : Γ ⊢[PRAAx] lt K (pw p L)) : Γ ⊢[PRAAx] rem (gb N K) p ≐ rem (DP p L N K) p := by
  have wpos := pw_pos' (prime_eq_succ_pred hp) L
  have g1 : Γ ⊢[PRAAx] gb (quo N (pw p L)) (quo K (pw p L)) ≐ one :=
    (congrGb (quo_small wpos hN) (quo_small wpos hK)).eqTrans (gb_zero zero)
  exact (lucas_digits hp L N K).eqTrans (congrAp2 remF (last_alg g1) (.eqRefl _))

/-- The length `N + K` always suffices. -/
theorem lucas_self {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N K : PTm n) :
    Γ ⊢[PRAAx] rem (gb N K) p ≐ rem (DP p (N + K) N K) p := by
  have hp2 : Γ ⊢[PRAAx] le two p := by have h := hp; unfold prime at h; exact Prf.andE₁ h
  have l := lt_pw hp2 (N + K)
  have lN : Γ ⊢[PRAAx] lt N (pw p (N + K)) :=
    le_trans ((succ_monus_succ _ _).eqTrans (le_add_right N K)) l
  have lK : Γ ⊢[PRAAx] lt K (pw p (N + K)) :=
    le_trans ((succ_monus_succ _ _).eqTrans (le_congr (.eqRefl _) (add_comm K N) (le_add_right K N))) l
  exact lucas hp lN lK

end LeanProofs.IPRA.Combinatorics.LucasDigits
