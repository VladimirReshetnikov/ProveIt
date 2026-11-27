import IPRADerivations.AnalyticNumberTheory.SieveWeightFacts
import IPRADerivations.AnalyticNumberTheory.SieveClosedForms

/-!
# The explicit vector `y` of the sieve weights

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`,
`eq:explicit-sieve-weights`: "Now make the explicit rational choice `y_r = μ(r) / (φ(r) G)`", for `r ∈ D` (squarefree,
`r ≤ z`, coprime to `q`), and `eq:sieve-normalization`, which uses "`μ(r)² = 1` on `D`".

With the common denominator `B = z!` (`SieveWeightFacts.phi_quo`) and the parameter `P = ⟨q, ⟨a, z⟩⟩`, the vector
`B G · y` has the natural positive and negative parts

  `Y^±_r = [gcd(r, q) = 1] · [r ≥ 1] μ^±(r) · (z! / φ(r))`          (`YP`, `YN`; bodies `gU y0P`, `gU y0N`),

where `μ^±(r) = μ^±_{r+1}(r)` are the bodies `aPB`, `aNB` of `SymmetrySum`.

* `eqb_idem`, `muP_idem`, `muN_idem`, `mu_disj`: `μ^±` take the values `0`, `1` and `μ⁺ μ⁻ = 0`
  (so `μ² = μ⁺ + μ⁻` and `(μ⁺ − μ⁻)² = μ⁺ + μ⁻`);
* `aP_indep`, `aN_indep`: `μ^±` do not depend on the parameter;
* `YP_at`, `YN_at`: the values of `Y^±`;
* `Y_disj`: `Y⁺_r Y⁻_r = 0`;
* `phi_YP`, `phi_YN`: `φ(r) (Y^±_r)² = z! · Y^±_r` for `r ≤ z`: the summand of the quadratic form
  `Σ_r φ(r) y_r²` is `z!` times the summand of `Σ_r μ(r)² [gcd(r, q) = 1] z!/φ(r)`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightValues

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN congrSg zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveClosedForms (gU inst2_gU)
open LeanProofs.IPRA.Probability.Expectation (inst2_mul')

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The values of `μ^±` -/

theorem eqb_idem (a b : PTm n) : Γ ⊢[PRAAx] eqb a b * eqb a b ≐ eqb a b :=
  Common.mul_self_eq_of_zero_or_one (Common.eqb_zero_or_one a b)

theorem prod_idem {x y : PTm n} (hx : Γ ⊢[PRAAx] x * x ≐ x) (hy : Γ ⊢[PRAAx] y * y ≐ y) :
    Γ ⊢[PRAAx] (x * y) * (x * y) ≐ x * y := by
  ipra_lc 𝔞 y * 𝔞 y * natEq hx + 𝔞 x * natEq hy

theorem muP_idem (N x : PTm n) : Γ ⊢[PRAAx] muP N x * muP N x ≐ muP N x :=
  prod_idem (eqb_idem _ _) (eqb_idem _ _)

theorem muN_idem (N x : PTm n) : Γ ⊢[PRAAx] muN N x * muN N x ≐ muN N x :=
  prod_idem (eqb_idem _ _) (eqb_idem _ _)

/-- `[t = 0] [t = 1] = 0`. -/
theorem eqb_zero_one (t : PTm n) : Γ ⊢[PRAAx] eqb t zero * eqb t one ≐ zero := by
  refine .orE (eq_or_ne t zero) ?_ ?_
  · have h0 : ((t ≐ zero) :: Γ) ⊢[PRAAx] t ≐ zero := Prf.hyp0
    have hne : ((t ≐ zero) :: Γ) ⊢[PRAAx] neg (t ≐ one) :=
      .impI (succ_ne_zero ((Prf.hyp0 : ((t ≐ one) :: (t ≐ zero) :: Γ) ⊢[PRAAx] t ≐ one).eqSymm.eqTrans h0.wk))
    exact (congrMul (.eqRefl _) (eqb_of_ne hne)).eqTrans (mul_zero _)
  · exact zero_mul_l (eqb_of_ne Prf.hyp0) _

theorem disj_alg {s e0 e1 : PTm n} (h : Γ ⊢[PRAAx] e0 * e1 ≐ zero) : Γ ⊢[PRAAx] (s * e0) * (s * e1) ≐ zero := by
  ipra_lc 𝔞 s * 𝔞 s * natEq h

/-- `μ⁺ μ⁻ = 0`. -/
theorem mu_disj (N x : PTm n) : Γ ⊢[PRAAx] muP N x * muN N x ≐ zero :=
  disj_alg (eqb_zero_one _)

theorem aP_indep (i p p' : PTm n) : Γ ⊢[PRAAx] inst2 aPB i p ≐ inst2 aPB i p' := by
  rw [inst2_aP, inst2_aP]; exact .eqRefl _

theorem aN_indep (i p p' : PTm n) : Γ ⊢[PRAAx] inst2 aNB i p ≐ inst2 aNB i p' := by
  rw [inst2_aN, inst2_aN]; exact .eqRefl _

/-! ## The vector `y` -/

/-- `z! / φ(r)` over `0 = r`, `1 = P`, `z = snd (snd P)`. -/
def wq : PTm 2 := quo (fact (sndT (sndT (var 1)))) (phi (var 0))

theorem inst2_wq (r P : PTm n) : inst2 wq r P = quo (fact (sndT (sndT P))) (phi r) := by
  simp [inst2, wq]

/-- `[r ≥ 1] μ⁺(r) · z!/φ(r)`. -/
def y0P : PTm 2 := (sg (var 0) * aPB) * wq
/-- `[r ≥ 1] μ⁻(r) · z!/φ(r)`. -/
def y0N : PTm 2 := (sg (var 0) * aNB) * wq

theorem inst2_sgv (r P : PTm n) : inst2 (sg (var 0) : PTm 2) r P = sg r := by simp [inst2]

theorem inst2_y0P (r P : PTm n) :
    inst2 y0P r P = (sg r * muP (succ r) r) * quo (fact (sndT (sndT P))) (phi r) := by
  rw [y0P, inst2_mul', inst2_mul', inst2_sgv, inst2_aP, inst2_wq]

theorem inst2_y0N (r P : PTm n) :
    inst2 y0N r P = (sg r * muN (succ r) r) * quo (fact (sndT (sndT P))) (phi r) := by
  rw [y0N, inst2_mul', inst2_mul', inst2_sgv, inst2_aN, inst2_wq]

/-- `Y⁺_r`: the positive part of `z! G · y_r`. -/
abbrev YP : PTm 2 := gU y0P
/-- `Y⁻_r`: the negative part. -/
abbrev YN : PTm 2 := gU y0N

theorem YP_at (r P : PTm n) : inst2 YP r P =
    eqb (gcd r (fstT P)) one * ((sg r * muP (succ r) r) * quo (fact (sndT (sndT P))) (phi r)) := by
  rw [inst2_gU, inst2_y0P]

theorem YN_at (r P : PTm n) : inst2 YN r P =
    eqb (gcd r (fstT P)) one * ((sg r * muN (succ r) r) * quo (fact (sndT (sndT P))) (phi r)) := by
  rw [inst2_gU, inst2_y0N]

/-! ## The products -/

theorem y_disj_alg {g s mP mN w : PTm n} (h : Γ ⊢[PRAAx] mP * mN ≐ zero) :
    Γ ⊢[PRAAx] (g * ((s * mP) * w)) * (g * ((s * mN) * w)) ≐ zero := by
  ipra_lc 𝔞 g * 𝔞 g * 𝔞 s * 𝔞 s * 𝔞 w * 𝔞 w * natEq h

/-- `Y⁺_r Y⁻_r = 0`. -/
theorem Y_disj (r P : PTm n) : Γ ⊢[PRAAx] inst2 YP r P * inst2 YN r P ≐ zero := by
  rw [YP_at, YN_at]
  exact y_disj_alg (mu_disj _ _)

/-- `φ (g ((s m) w))² = B (g ((s m) w))` from `g² = g`, `s² = s`, `m² = m` and `B = φ w`. -/
theorem phi_alg {φ g s m w B : PTm n} (hg : Γ ⊢[PRAAx] g * g ≐ g) (hs : Γ ⊢[PRAAx] s * s ≐ s)
    (hm : Γ ⊢[PRAAx] m * m ≐ m) (hB : Γ ⊢[PRAAx] B ≐ φ * w) :
    Γ ⊢[PRAAx] φ * ((g * ((s * m) * w)) * (g * ((s * m) * w))) ≐ B * (g * ((s * m) * w)) := by
  ipra_lc 𝔞 φ * 𝔞 w * 𝔞 w * (𝔞 s * 𝔞 s * 𝔞 m * 𝔞 m * natEq hg + 𝔞 g * 𝔞 m * 𝔞 m * natEq hs + 𝔞 g * 𝔞 s * natEq hm) -
    𝔞 g * 𝔞 s * 𝔞 m * 𝔞 w * natEq hB

theorem zero_alg {φ g s m w B : PTm n} (hs : Γ ⊢[PRAAx] s ≐ zero) :
    Γ ⊢[PRAAx] φ * ((g * ((s * m) * w)) * (g * ((s * m) * w))) ≐ B * (g * ((s * m) * w)) := by
  ipra_lc (𝔞 φ * (𝔞 g * ((𝔞 s + 0) * 𝔞 m * 𝔞 w)) * 𝔞 g * 𝔞 m * 𝔞 w - 𝔞 B * 𝔞 g * 𝔞 m * 𝔞 w) * natEq hs

/-- `φ(r) (Y⁺_r)² = z! · Y⁺_r` for `r ≤ z`. -/
theorem phi_YP {r P : PTm n} (hrz : Γ ⊢[PRAAx] le r (sndT (sndT P))) :
    Γ ⊢[PRAAx] phi r * (inst2 YP r P * inst2 YP r P) ≐ fact (sndT (sndT P)) * inst2 YP r P := by
  rw [YP_at]
  refine .orE (zero_or_succ r) ?_ ?_
  · exact zero_alg ((congrSg Prf.hyp0).eqTrans sg_zero)
  · have hr : ((r ≐ succ (pred r)) :: Γ) ⊢[PRAAx] r ≐ succ (pred r) := Prf.hyp0
    have s1 : ((r ≐ succ (pred r)) :: Γ) ⊢[PRAAx] sg r ≐ one := sg_pos hr
    exact phi_alg (eqb_idem _ _) ((congrMul s1 s1).eqTrans ((one_mul one).eqTrans s1.eqSymm)) (muP_idem _ _)
      (phi_quo hr (hrz.wk (ψ := r ≐ succ (pred r))))

/-- `φ(r) (Y⁻_r)² = z! · Y⁻_r` for `r ≤ z`. -/
theorem phi_YN {r P : PTm n} (hrz : Γ ⊢[PRAAx] le r (sndT (sndT P))) :
    Γ ⊢[PRAAx] phi r * (inst2 YN r P * inst2 YN r P) ≐ fact (sndT (sndT P)) * inst2 YN r P := by
  rw [YN_at]
  refine .orE (zero_or_succ r) ?_ ?_
  · exact zero_alg ((congrSg Prf.hyp0).eqTrans sg_zero)
  · have hr : ((r ≐ succ (pred r)) :: Γ) ⊢[PRAAx] r ≐ succ (pred r) := Prf.hyp0
    have s1 : ((r ≐ succ (pred r)) :: Γ) ⊢[PRAAx] sg r ≐ one := sg_pos hr
    exact phi_alg (eqb_idem _ _) ((congrMul s1 s1).eqTrans ((one_mul one).eqTrans s1.eqSymm)) (muN_idem _ _)
      (phi_quo hr (hrz.wk (ψ := r ≐ succ (pred r))))

end LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightValues

export_ipra AnalyticNumberTheory.SieveWeightValues (YN_at YP_at)
