import IPRADerivations.AnalyticNumberTheory.SymmetrySum
import IPRADerivations.AnalyticNumberTheory.ComparisonEnvelope

/-!
# From the additive logarithm to the harmonic logarithm (`pnt_ipra_constructive_2026-11-14`, towards `sb:symmetry-bound`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `pnt_ipra.tex` §"Rational logarithm intervals" and
`selberg.tex`, Lemma `sb:symmetry`. The exact Selberg identity (`SymmetrySum`) is stated for the completely additive
`L_w` of the harmonic weight `w(p) = λ_K(p)` (`HarmonicChebyshev.wt`), while the analytic estimates
(`HarmonicLogSquareSum`, `SelbergComparison`) are stated for the harmonic logarithm itself, `u_k = F λ_K(k)`.
The two agree up to `k/K` (`HarmonicChebyshev.harmonic_lw`, `HarmonicMertensLower.lw_lower`):

  `L_w(k) ≤ u_k ≤ L_w(k) + k ⌊F/K⌋`.

This module transfers that to the square sums `B(m) = Σ_{k≤m} L_w(k)²` and `Q(m) = Σ_{k≤m} u_k²`:

* `sum_le_add_const`: a pointwise `f ≤ g + c` sums to `Σ f ≤ Σ g + N c`;
* `bridge_lo`: `B(m) ≤ Q(m)`;
* `bridge_hi`: `Q(m) ≤ B(m) + m · 2m ⌊F/K⌋ u_m` (`u² ≤ L² + 2 m q u_m` pointwise), i.e. an error `O(m² λ(m)/K)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.WeightBridge

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono wt harmonic_lw)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertensLower (lw_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U QB Qs inst2_QB)
open LeanProofs.IPRA.AnalyticNumberTheory.ComparisonEnvelope (le_mul2)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (bS inst2_bS Bs)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetrySum (bL inst2_bL)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (shift_fact')
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lw)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.Foundations.AuxiliaryEnvelope (sum_le_const)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## A sum with an additive constant -/

/-- `g(k, fst z) + snd z`. -/
def gcB (g : PTm 2) : PTm 2 := Syn.subst ![var 0, fstT (var 1)] g + sndT (var 1)
/-- `snd z`. -/
abbrev sndB : PTm 2 := sndT (var 1)

theorem inst2_gcB (g : PTm 2) (k z : PTm n) : inst2 (gcB g) k z = inst2 g k (fstT z) + sndT z := by
  have hg : Syn.subst ![k, z] (Syn.subst ![var 0, fstT (var 1)] g) = inst2 g k (fstT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  simp only [inst2, gcB, PTm.subst_add, hg]
  simp
theorem inst2_sndB (k z : PTm n) : inst2 sndB k z = sndT z := by simp [inst2]

/-- A pointwise `f(k) ≤ g(k) + c` for `k < N` gives `Σ_{k<N} f ≤ Σ_{k<N} g + N c`. -/
theorem sum_le_add_const (f g : PTm 2) {x y c N : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift y) + Syn.shift c))) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) N x) (ap2 (sumF g) N y + N * c) := by
  have s1 := sum_le_params f (gcB g) x (pairT y c) N (.allI (.impI (by
    rw [inst2_gcB, shift_pairT]
    exact le_congr (.eqRefl _) (congrAdd (congrInst2 g (.eqRefl _) (fst_pair _ _)) (snd_pair _ _)).eqSymm
      (Prf.impE h.allOpen.wk Prf.hyp0))))
  have s2 := sum_add2 (Γ := Γ) g sndB (gcB g) (K := N) (x := y) (x' := pairT y c) (z := pairT y c)
    (.allI (.impI (by
      rw [inst2_gcB, inst2_sndB, shift_pairT]
      exact congrAdd (congrInst2 g (.eqRefl _) (fst_pair _ _)) (.eqRefl _))))
  have s3 := sum_le_const (Γ := Γ) sndB (N := N) (L := c) (x := pairT y c) (.allI (.impI (by
    rw [inst2_sndB, shift_pairT]
    exact le_congr (snd_pair _ _).eqSymm (.eqRefl _) (le_refl _))))
  have e2 := natEq s2
  ipra_le sl s1 + sl s3 with e2

/-! ## Pointwise comparison -/

theorem qb_at (k K F : PTm n) :
    Γ ⊢[PRAAx] inst2 QB k (pairT K F) ≐ U (succ k) K F * U (succ k) K F := by
  rw [inst2_QB]
  have e : Γ ⊢[PRAAx] monus (S (fstT (pairT K F) * succ k) (sndT (pairT K F))) (S (fstT (pairT K F)) (sndT (pairT K F)))
      ≐ U (succ k) K F :=
    congrMonus (congrAp2 (sumF hB) (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))
      (congrAp2 (sumF hB) (fst_pair _ _) (snd_pair _ _))
  exact congrMul e e

/-- `L_w(k+1) ≤ u_{k+1}`. -/
theorem lw_le_u {k K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hkL : Γ ⊢[PRAAx] le (K * succ k) L) :
    Γ ⊢[PRAAx] le (Lw wt (succ k) (pairT K (fact L))) (U (succ k) K (fact L)) := by
  have h1 : Γ ⊢[PRAAx] le one (succ k) := le_of_eq_add (d := k) (by ipra_ring)
  have h := harmonic_lw h1 hK hkL
  have m1 : Γ ⊢[PRAAx] le (S K (fact L)) (S (K * succ k) (fact L)) :=
    S_mono (fact L) (le_of_eq_add (d := K * k) (by ipra_ring))
  have Eu := natEq (eq_add_of_le m1)
  ipra_le sl h with Eu

/-- `u_{k+1} ≤ L_w(k+1) + (k+1) ⌊F/K⌋`. -/
theorem u_le_lw {k K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hkL : Γ ⊢[PRAAx] le (K * succ k) L) :
    Γ ⊢[PRAAx] le (U (succ k) K (fact L)) (Lw wt (succ k) (pairT K (fact L)) + succ k * quo (fact L) K) := by
  have h1 : Γ ⊢[PRAAx] le one (succ k) := le_of_eq_add (d := k) (by ipra_ring)
  have h := lw_lower h1 hK hkL
  have m1 : Γ ⊢[PRAAx] le (S K (fact L)) (S (K * succ k) (fact L)) :=
    S_mono (fact L) (le_of_eq_add (d := K * k) (by ipra_ring))
  have Eu := natEq (eq_add_of_le m1)
  ipra_le sl h with -Eu

/-- `L_w(k+1)² ≤ u_{k+1}²`. -/
theorem pt_lo {k K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hkL : Γ ⊢[PRAAx] le (K * succ k) L) :
    Γ ⊢[PRAAx] le (Lw wt (succ k) (pairT K (fact L)) * Lw wt (succ k) (pairT K (fact L)))
      (U (succ k) K (fact L) * U (succ k) K (fact L)) :=
  le_mul2 (lw_le_u hK hkL) (lw_le_u hK hkL)

/-- `u_{k+1}² ≤ L_w(k+1)² + 2 m ⌊F/K⌋ u_m` for `k + 1 ≤ m`, `Km ≤ L`. -/
theorem pt_hi {k K L m : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hkm : Γ ⊢[PRAAx] le (succ k) m)
    (hmL : Γ ⊢[PRAAx] le (K * m) L) :
    Γ ⊢[PRAAx] le (U (succ k) K (fact L) * U (succ k) K (fact L))
      (Lw wt (succ k) (pairT K (fact L)) * Lw wt (succ k) (pairT K (fact L)) +
        two * (m * (quo (fact L) K * U m K (fact L)))) := by
  have hkL := le_trans (le_scale K hkm) hmL
  have hlu := lw_le_u hK hkL
  have hul0 := u_le_lw hK hkL
  have hq := mul_le_mul_right (quo (fact L) K) hkm
  have hul : Γ ⊢[PRAAx] le (U (succ k) K (fact L)) (Lw wt (succ k) (pairT K (fact L)) + m * quo (fact L) K) := by
    ipra_le sl hul0 + sl hq
  have m1 : Γ ⊢[PRAAx] le (S K (fact L)) (S (K * succ k) (fact L)) :=
    S_mono (fact L) (le_of_eq_add (d := K * k) (by ipra_ring))
  have m2 : Γ ⊢[PRAAx] le (S (K * succ k) (fact L)) (S (K * m) (fact L)) := S_mono (fact L) (le_scale K hkm)
  have m3 : Γ ⊢[PRAAx] le (S K (fact L)) (S (K * m) (fact L)) := le_trans m1 m2
  have Eu := natEq (eq_add_of_le m1)
  have Eum := natEq (eq_add_of_le m3)
  have hum : Γ ⊢[PRAAx] le (U (succ k) K (fact L)) (U m K (fact L)) := by
    ipra_le sl m2 with Eum - Eu
  have p1 := le_scale (U (succ k) K (fact L)) hul
  have p2 := le_scale (Lw wt (succ k) (pairT K (fact L))) hul
  have p3 := le_scale (m * quo (fact L) K) hlu
  have p4 := le_scale (two * (m * quo (fact L) K)) hum
  ipra_le sl p1 + sl p2 + sl p3 + sl p4

/-! ## The square sums -/

/-- `B(m) ≤ Q(m)` for `K ≥ 1`, `Km ≤ L`. -/
theorem bridge_lo {m K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hmL : Γ ⊢[PRAAx] le (K * m) L) :
    Γ ⊢[PRAAx] le (Bs (bL wt) m (pairT K (fact L))) (Qs m K (fact L)) := by
  have hK' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have hmL' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Syn.shift m) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hmL.shift
  refine sum_le_params (bS (bL wt)) QB (pairT K (fact L)) (pairT K (fact L)) m (.allI (.impI ?_))
  rw [shift_pairT, shift_fact', inst2_bS, inst2_bL]
  exact le_congr (.eqRefl _) (qb_at _ _ _).eqSymm
    (pt_lo hK'.wk (le_trans (le_scale _ (Prf.hyp0 : (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx] _))
      hmL'.wk))

/-- `Q(m) ≤ B(m) + m · 2m ⌊F/K⌋ u_m` for `K ≥ 1`, `Km ≤ L`. -/
theorem bridge_hi {m K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hmL : Γ ⊢[PRAAx] le (K * m) L) :
    Γ ⊢[PRAAx] le (Qs m K (fact L))
      (Bs (bL wt) m (pairT K (fact L)) + m * (two * (m * (quo (fact L) K * U m K (fact L))))) := by
  have hK' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have hmL' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Syn.shift m) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hmL.shift
  refine sum_le_add_const QB (bS (bL wt)) (.allI (.impI ?_))
  rw [shift_pairT, shift_fact', inst2_bS, inst2_bL,
    show Syn.shift (two * (m * (quo (fact L) K * U m K (fact L)))) =
      two * (Syn.shift m * (quo (fact (Syn.shift L)) (Syn.shift K) * U (Syn.shift m) (Syn.shift K) (fact (Syn.shift L))))
      by simp [Syn.shift]]
  exact le_congr (qb_at _ _ _).eqSymm (.eqRefl _)
    (pt_hi hK'.wk (Prf.hyp0 : (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx] _) hmL'.wk)

end LeanProofs.IPRA.AnalyticNumberTheory.WeightBridge
