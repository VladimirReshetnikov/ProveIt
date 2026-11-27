import IPRADerivations.AnalyticNumberTheory.SieveWeightFacts
import IPRADerivations.AnalyticNumberTheory.SieveInversion
import IPRADerivations.AnalyticNumberTheory.SieveClosedForms

/-!
# The sieve weights defined by inversion, and their sums over multiples

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:sieve-inversion` and
`eq:explicit-sieve-weights`: the weights are defined from a vector `y` by
`λ_d / d = Σ_{r ∈ D, d ∣ r} μ(r/d) y_r`, and `y_s = Σ_{d ∈ D, s ∣ d} λ_d / d` is recovered.

For a natural body `y = [gcd(r, q) = 1] y₀(r, P)` (the form `SieveClosedForms.gU y₀`, so that `y` is supported on
numbers coprime to `q = fst P`) and a parameter-independent body `a` (one of `μ⁺`, `μ⁻`), with `z = snd (snd P)`:

* `uB y a`: the weight `U_d = Σ_{r ≤ z} [d ≥ 1][d ∣ r] a(r/d) [r ≥ 1] y_r`, the row of `SieveInversion.wB y a` at
  `s = 1`;
* `wB_s`: the summand of `SieveInversion.wB` at `s` is `[s ∣ d]` times the summand at `s = 1`;
* `wB_g`: `[d ≥ 1][gcd(d, q) = 1]` times that summand is the summand: the weights vanish unless `d ≥ 1` is
  coprime to `q` (`SieveWeightFacts.g_supp`);
* `row_s`: the row at `s` is `[s ∣ d] [d ≥ 1][gcd(d, q) = 1] U_d`;
* `Ab_sum`: `Σ_{d ≤ z} [d ≥ 1][s ∣ d] · [gcd(d, q) = 1] U_d` is the double sum of `SieveInversion.dual_inversion`,
  where the left side is the sum over `d` in `SieveDiagonal.diag_term` for the weight `gU (uB y a)`;
* `Bb_sum`: the same for the second sum of `diag_term`, which carries `[e ≥ 1]` in the weight and the factor `φ(s)`.

With `SieveInversion.dual_inversion` these give `Σ_{s ∣ d} (U⁺_d − U⁻_d) = y_s`; that combination, and the choice of
`y`, are not part of this module.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightRows

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg zero_mul_l congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (rem_one)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveInversion (hS inst2_hS wB wB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveDiagonal (Ab Ab_at Bb Bb_at)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveClosedForms (gU inst2_gU sgV inst2_sgV)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightFacts (g_supp)
open LeanProofs.IPRA.Probability.Independence (row_pt sum_scale dsum)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Algebra over opaque terms -/

theorem sg_idem (d : PTm n) : Γ ⊢[PRAAx] sg d * sg d ≐ sg d :=
  Common.mul_self_eq_of_zero_or_one (Common.sg_zero_or_one d)

theorem r1_alg {SE H H1 A A' K : PTm n} (h1 : Γ ⊢[PRAAx] H1 ≐ one) (hA : Γ ⊢[PRAAx] A ≐ A') :
    Γ ⊢[PRAAx] (SE * (H * A)) * K ≐ H * ((SE * (H1 * A')) * K) := by
  ipra_lc 𝔞 SE * 𝔞 H * 𝔞 K * natEq hA - 𝔞 SE * 𝔞 H * 𝔞 K * 𝔞 A' * natEq h1

theorem r2_alg {S gd E H A R G Y0 : PTm n} (hS : Γ ⊢[PRAAx] S * S ≐ S)
    (hg : Γ ⊢[PRAAx] S * (gd * (E * G)) ≐ S * (E * G)) :
    Γ ⊢[PRAAx] (S * gd) * (((S * E) * (H * A)) * (R * (G * Y0))) ≐ ((S * E) * (H * A)) * (R * (G * Y0)) := by
  ipra_lc 𝔞 S * (𝔞 H * 𝔞 A * 𝔞 R * 𝔞 Y0) * natEq hg + 𝔞 E * 𝔞 G * (𝔞 H * 𝔞 A * 𝔞 R * 𝔞 Y0) * natEq hS

theorem r3_alg (H S g W : PTm n) : Γ ⊢[PRAAx] H * ((S * g) * W) ≐ (H * (S * g)) * W := by
  ipra_ring

theorem r4_alg (S H g T : PTm n) : Γ ⊢[PRAAx] (S * H) * (g * T) ≐ (H * (S * g)) * T := by
  ipra_ring

theorem r5_alg (H S g T F : PTm n) : Γ ⊢[PRAAx] H * ((S * g) * T) * F ≐ F * ((H * (S * g)) * T) := by
  ipra_ring

/-! ## The summand at `s` and at `s = 1` -/

section Rows

variable (y0 a : PTm 2)

/-- The summand at `s` is `[s ∣ d]` times the summand at `s = 1`, for a parameter-independent `a`. -/
theorem wB_s (y : PTm 2)
    (ha : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (i p p' : PTm k), Δ ⊢[PRAAx] inst2 a i p ≐ inst2 a i p')
    (d r s p : PTm n) :
    Γ ⊢[PRAAx] inst3 (wB y a) d r (pairT s p) ≐ eqb (rem d s) zero * inst3 (wB y a) d r (pairT one p) := by
  have e1 : Γ ⊢[PRAAx] inst3 (wB y a) d r (pairT s p) ≐
      ((sg d * eqb (rem r d) zero) * (eqb (rem d s) zero * inst2 a (quo r d) s)) * (sg r * inst2 y r p) := by
    have h := (wB_at (Γ := Γ) y a d r s p).eqTrans (congrMul (cv_at hS a d r s) (.eqRefl _))
    rw [inst2_hS] at h
    exact h
  have e2 : Γ ⊢[PRAAx] inst3 (wB y a) d r (pairT one p) ≐
      ((sg d * eqb (rem r d) zero) * (eqb (rem d one) zero * inst2 a (quo r d) one)) * (sg r * inst2 y r p) := by
    have h := (wB_at (Γ := Γ) y a d r one p).eqTrans (congrMul (cv_at hS a d r one) (.eqRefl _))
    rw [inst2_hS] at h
    exact h
  have h1 : Γ ⊢[PRAAx] eqb (rem d one) zero ≐ one := eqb_of_eq (rem_one d)
  exact e1.eqTrans ((r1_alg h1 (ha _ _ _)).eqTrans (congrMul (.eqRefl _) e2.eqSymm))

/-- `[d ≥ 1] · ([gcd(d, q) = 1] · ([d ∣ r] [gcd(r, q) = 1])) = [d ≥ 1] · ([d ∣ r] [gcd(r, q) = 1])`. -/
theorem sg_supp {d r q : PTm n} (hq : Γ ⊢[PRAAx] le one q) :
    Γ ⊢[PRAAx] sg d * (eqb (gcd d q) one * (eqb (rem r d) zero * eqb (gcd r q) one)) ≐
      sg d * (eqb (rem r d) zero * eqb (gcd r q) one) := by
  refine .orE (zero_or_succ d) ?_ ?_
  · have s0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact (zero_mul_l s0 _).eqTrans (zero_mul_l s0 _).eqSymm
  · exact congrMul (.eqRefl _) (g_supp (hq.wk (ψ := d ≐ succ (pred d))) Prf.hyp0)

/-- `[d ≥ 1][gcd(d, q) = 1]` times the summand at `s = 1` is that summand, when `y = [gcd(r, q) = 1] y₀`. -/
theorem wB_g {d r p : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT p)) :
    Γ ⊢[PRAAx] (sg d * eqb (gcd d (fstT p)) one) * inst3 (wB (gU y0) a) d r (pairT one p) ≐
      inst3 (wB (gU y0) a) d r (pairT one p) := by
  have e2 : Γ ⊢[PRAAx] inst3 (wB (gU y0) a) d r (pairT one p) ≐
      ((sg d * eqb (rem r d) zero) * (eqb (rem d one) zero * inst2 a (quo r d) one)) *
        (sg r * (eqb (gcd r (fstT p)) one * inst2 y0 r p)) := by
    have h := (wB_at (Γ := Γ) (gU y0) a d r one p).eqTrans (congrMul (cv_at hS a d r one) (.eqRefl _))
    rw [inst2_hS, inst2_gU] at h
    exact h
  exact (congrMul (.eqRefl _) e2).eqTrans ((r2_alg (sg_idem d) (sg_supp hq)).eqTrans e2.eqSymm)

/-- The summand at `s`, for `y = [gcd(r, q) = 1] y₀`: `[s ∣ d] [d ≥ 1][gcd(d, q) = 1]` times the summand at `1`. -/
theorem w_pt (ha : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (i p p' : PTm k), Δ ⊢[PRAAx] inst2 a i p ≐ inst2 a i p')
    {d r s p : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT p)) :
    Γ ⊢[PRAAx] inst3 (wB (gU y0) a) d r (pairT s p) ≐
      (eqb (rem d s) zero * (sg d * eqb (gcd d (fstT p)) one)) * inst3 (wB (gU y0) a) d r (pairT one p) :=
  (wB_s a (gU y0) ha d r s p).eqTrans
    ((congrMul (.eqRefl _) (wB_g y0 a hq).eqSymm).eqTrans (r3_alg _ _ _ _))

/-! ## Rows -/

/-- The row at `s` is `[s ∣ d] [d ≥ 1][gcd(d, q) = 1]` times the row at `s = 1`. -/
theorem row_s (ha : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (i p p' : PTm k), Δ ⊢[PRAAx] inst2 a i p ≐ inst2 a i p')
    {d s p : PTm n} (N : PTm n) (hq : Γ ⊢[PRAAx] le one (fstT p)) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB (wB (gU y0) a))) N (pairT d (pairT s p)) ≐
      (eqb (rem d s) zero * (sg d * eqb (gcd d (fstT p)) one)) *
        ap2 (sumF (rowB (wB (gU y0) a))) N (pairT d (pairT one p)) := by
  refine sum_scale (rowB (wB (gU y0) a)) (rowB (wB (gU y0) a)) N _ (pairT d (pairT one p)) (pairT d (pairT s p))
    (.allI (.impI ?_))
  have hq' : (Γ.map Fm.shift) ⊢[PRAAx] le one (fstT (Syn.shift p)) := by
    simpa [Fm.shift, Syn.shift] using hq.shift
  have hK : Syn.shift (eqb (rem d s) zero * (sg d * eqb (gcd d (fstT p)) one)) =
      eqb (rem (Syn.shift d) (Syn.shift s)) zero * (sg (Syn.shift d) * eqb (gcd (Syn.shift d) (fstT (Syn.shift p))) one) := by
    ipra_ind_simp [Syn.shift, subst_eqb, subst_gcd', subst_ap2, subst_fstT]
  have s1 : Syn.shift (pairT d (pairT one p)) = pairT (Syn.shift d) (pairT one (Syn.shift p)) := by
    simp [Syn.shift]
  have s2 : Syn.shift (pairT d (pairT s p)) = pairT (Syn.shift d) (pairT (Syn.shift s) (Syn.shift p)) := by
    simp [Syn.shift]
  rw [hK, s1, s2]
  exact (row_pt (wB (gU y0) a) _ _ _).eqTrans
    ((w_pt y0 a ha hq'.wk).eqTrans (congrMul (.eqRefl _) (row_pt (wB (gU y0) a) _ _ _).eqSymm))

/-- The weight `U_d = Σ_{r ≤ z} [d ≥ 1][d ∣ r] a(r/d) [r ≥ 1] y_r` over `0 = d`, `1 = P`, `z = snd (snd P)`. -/
def uB (y : PTm 2) : PTm 2 :=
  ap2 (sumF (rowB (wB y a))) (succ (sndT (sndT (var 1)))) (pairT (var 0) (pairT one (var 1)))

theorem inst2_uB (y : PTm 2) (d P : PTm n) :
    inst2 (uB a y) d P = ap2 (sumF (rowB (wB y a))) (succ (sndT (sndT P))) (pairT d (pairT one P)) := by
  simp [inst2, uB]

/-! ## The sums over multiples -/

/-- The summand of the first sum of `SieveDiagonal.diag_term` at `d`, for the weight `gU (uB y a)`, is the row of
`wB` at `s`. -/
theorem Ab_row (ha : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (i p p' : PTm k), Δ ⊢[PRAAx] inst2 a i p ≐ inst2 a i p')
    {d s X P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) :
    Γ ⊢[PRAAx] inst2 (Ab (sndB (gU (uB a (gU y0))))) d (pairT s (pairT X P)) ≐
      inst2 (oB (wB (gU y0) a)) d (pairT (succ (sndT (sndT P))) (pairT s P)) := by
  have l : Γ ⊢[PRAAx] inst2 (Ab (sndB (gU (uB a (gU y0))))) d (pairT s (pairT X P)) ≐
      (sg d * eqb (rem d s) zero) * (eqb (gcd d (fstT P)) one *
        ap2 (sumF (rowB (wB (gU y0) a))) (succ (sndT (sndT P))) (pairT d (pairT one P))) := by
    refine (Ab_at _ d s (pairT X P)).eqTrans (congrMul (.eqRefl _) ?_)
    rw [inst2_sndB]
    refine (congrInst2 _ (.eqRefl _) (snd_pair X P)).eqTrans ?_
    rw [inst2_gU, inst2_uB]
    exact .eqRefl _
  exact l.eqTrans ((r4_alg _ _ _ _).eqTrans
    ((row_s y0 a ha (succ (sndT (sndT P))) hq).eqSymm.eqTrans (oB_at _ _ _ _).eqSymm))

/-- `Σ_{d ≤ z} [d ≥ 1][s ∣ d] [gcd(d, q) = 1] U_d` is the double sum of `SieveInversion.dual_inversion`. -/
theorem Ab_sum (ha : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (i p p' : PTm k), Δ ⊢[PRAAx] inst2 a i p ≐ inst2 a i p')
    {s X P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) :
    Γ ⊢[PRAAx] ap2 (sumF (Ab (sndB (gU (uB a (gU y0)))))) (succ (sndT (sndT P))) (pairT s (pairT X P)) ≐
      dsum (wB (gU y0) a) (succ (sndT (sndT P))) (succ (sndT (sndT P))) (pairT s P) := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  have hq' : (Γ.map Fm.shift) ⊢[PRAAx] le one (fstT (Syn.shift P)) := by
    simpa [Fm.shift, Syn.shift] using hq.shift
  have s1 : Syn.shift (pairT s (pairT X P)) = pairT (Syn.shift s) (pairT (Syn.shift X) (Syn.shift P)) := by
    simp [Syn.shift]
  have s2 : Syn.shift (pairT (succ (sndT (sndT P))) (pairT s P)) =
      pairT (succ (sndT (sndT (Syn.shift P)))) (pairT (Syn.shift s) (Syn.shift P)) := by
    simp [Syn.shift]
  rw [s1, s2]
  exact Ab_row y0 a ha hq'.wk

/-- The summand of the second sum of `diag_term` at `e`, for the weight `sgV (uB y a)`: `φ(s)` times the row at
`s`. -/
theorem Bb_row (ha : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (i p p' : PTm k), Δ ⊢[PRAAx] inst2 a i p ≐ inst2 a i p')
    {e s X P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) :
    Γ ⊢[PRAAx] inst2 (Bb (sndB (sgV (uB a (gU y0))))) e (pairT s (pairT X P)) ≐
      phi s * inst2 (oB (wB (gU y0) a)) e (pairT (succ (sndT (sndT P))) (pairT s P)) := by
  have l : Γ ⊢[PRAAx] inst2 (Bb (sndB (sgV (uB a (gU y0))))) e (pairT s (pairT X P)) ≐
      eqb (rem e s) zero * ((sg e * eqb (gcd e (fstT P)) one) *
        ap2 (sumF (rowB (wB (gU y0) a))) (succ (sndT (sndT P))) (pairT e (pairT one P))) * phi s := by
    refine (Bb_at _ e s (pairT X P)).eqTrans (congrMul (congrMul (.eqRefl _) ?_) (.eqRefl _))
    rw [inst2_sndB]
    refine (congrInst2 _ (.eqRefl _) (snd_pair X P)).eqTrans ?_
    rw [inst2_sgV, inst2_uB]
    exact .eqRefl _
  exact l.eqTrans ((r5_alg _ _ _ _ _).eqTrans (congrMul (.eqRefl _)
    ((row_s y0 a ha (succ (sndT (sndT P))) hq).eqSymm.eqTrans (oB_at _ _ _ _).eqSymm)))

/-- `Σ_{e ≤ z} [s ∣ e] [e ≥ 1][gcd(e, q) = 1] U_e φ(s) = φ(s) ·` the double sum of `dual_inversion`. -/
theorem Bb_sum (ha : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (i p p' : PTm k), Δ ⊢[PRAAx] inst2 a i p ≐ inst2 a i p')
    {s X P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) :
    Γ ⊢[PRAAx] ap2 (sumF (Bb (sndB (sgV (uB a (gU y0)))))) (succ (sndT (sndT P))) (pairT s (pairT X P)) ≐
      phi s * dsum (wB (gU y0) a) (succ (sndT (sndT P))) (succ (sndT (sndT P))) (pairT s P) := by
  refine sum_scale _ (oB (wB (gU y0) a)) (succ (sndT (sndT P))) (phi s) _ _ (.allI (.impI ?_))
  have hq' : (Γ.map Fm.shift) ⊢[PRAAx] le one (fstT (Syn.shift P)) := by
    simpa [Fm.shift, Syn.shift] using hq.shift
  have s1 : Syn.shift (pairT s (pairT X P)) = pairT (Syn.shift s) (pairT (Syn.shift X) (Syn.shift P)) := by
    simp [Syn.shift]
  have s2 : Syn.shift (pairT (succ (sndT (sndT P))) (pairT s P)) =
      pairT (succ (sndT (sndT (Syn.shift P)))) (pairT (Syn.shift s) (Syn.shift P)) := by
    simp [Syn.shift]
  have s3 : Syn.shift (phi s) = phi (Syn.shift s) := by simp only [Syn.shift, subst_ap2]
  rw [s1, s2, s3]
  exact Bb_row y0 a ha hq'.wk

end Rows

end LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightRows
