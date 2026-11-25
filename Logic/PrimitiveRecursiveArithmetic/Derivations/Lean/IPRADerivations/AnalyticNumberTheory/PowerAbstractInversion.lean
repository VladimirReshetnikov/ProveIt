import IPRADerivations.AnalyticNumberTheory.PowerDivisorInversion

/-!
# Möbius inversion from an abstract row identity (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, proof of Theorem
`thm:powerdivisor`: "substitute the first into the right side … and group pairs by `s = de`. The coefficient of
`A(⌊N/s^h⌋)` is `Σ_{d∣s} μ(d) = [s = 1]` … To verify inversion [for residues], a product `s = de` is a unit exactly when
both factors are units, and the residue selected in two steps is `b_s`. Thus every surviving coefficient reduces to the
same divisor sum as before."

`PowerDivisorInversion` derives the inversion for the rows `B_h(⌊N/d^h⌋)` of one coefficient body. Its column argument
only uses the row identity `sg(d) R(d) = Σ_{m≤N} [d ∣ m] sg(m) sg(d) G(m)`. This module makes that explicit, for arbitrary
bodies `R(d)` (the row values) and `G(m)` (the column terms) at the parameter `P = ⟨⟨N, h⟩, y⟩`:

* `RowHyp`: the row identity `R(d) = Σ_{m<N+1} [d ∣ m] sg(m) G(m)` for every `d ≥ 1`, in every context extending the
  shifted one (a schema, since it is used under the bound variable `d`);
* `rs_columns_g`: `Σ_{d<N+1} sg(d) w(d) R(d) = Σ_{m<N+1} sg(m) G(m) Σ_{d<N+1} sg(d)[d ∣ m] w(d)` (`Core/Fubini`);
* `inversion_g`: `Σ_{d≤N} μ⁺(d) R(d) = Σ_{d≤N} μ⁻(d) R(d) + T` whenever `G(1) = T` and `T = 0` at `N = 0`
  (`MobiusBounds.cancel_gen`).

The progression rows (`PowerResidueInversion`) instantiate `R(d) = [gcd(d^h, q) = 1] B_{h;q,b_{d^h}}(⌊N/d^h⌋)` and
`G(m) = [gcd(m^h, q) = 1] A_{q,b_{m^h}}(⌊N/m^h⌋)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerAbstractInversion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorInversion (Zp kB inst2_kB wP wN pB_at kB_mu)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (GP GN G_at cancel_gen congrMu)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN congrEqb' congrSg)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eqb_comm')
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorRow (sum_cut sg_mul_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (multiples_upto)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (riB inst2_riB reindex_eq cM)
open LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement (quo_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (G R w : PTm 2)

/-! ## The bodies -/

/-- `sg(d) w(d) R(d)` over `0 = d`, `1 = P`. -/
def rBg : PTm 2 := sg (var 0) * w * R

/-- `Σ_{d<N+1} sg(d) w(d) R(d)`. -/
abbrev RSg (N h y : PTm n) : PTm n := ap2 (sumF (rBg R w)) (succ N) (Zp N h y)

/-- `(sg(d) w(d)) ([d ∣ m] sg(m) G(m))` over `0 = d`, `1 = m`, `2 = P`. -/
def a3g : PTm 3 := (sg (var 0) * Syn.subst ![var 0, var 2] w) *
  (eqb (rem (var 1) (var 0)) zero * sg (var 1) * Syn.subst ![var 1, var 2] G)

/-- `[d ∣ m] sg(m) G(m)` over `0 = m`, `1 = ⟨d, P⟩`. -/
def dmBg : PTm 2 := eqb (rem (var 0) (fstT (var 1))) zero * sg (var 0) * Syn.subst ![var 0, sndT (var 1)] G

theorem inst2_rBg (d P : PTm n) : inst2 (rBg R w) d P = sg d * inst2 w d P * inst2 R d P := by
  simp [inst2, rBg]

theorem inst3_a3g (d m P : PTm n) : inst3 (a3g G w) d m P = (sg d * inst2 w d P) *
    (eqb (rem m d) zero * sg m * inst2 G m P) := by
  have hw : Syn.subst ![d, m, P] (Syn.subst ![var 0, var 2] w) = inst2 w d P := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  have hg : Syn.subst ![d, m, P] (Syn.subst ![var 1, var 2] G) = inst2 G m P := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst3, a3g, PTm.subst_mul, hw, hg]
  simp

theorem inst2_dmBg (m W : PTm n) :
    inst2 (dmBg G) m W = eqb (rem m (fstT W)) zero * sg m * inst2 G m (sndT W) := by
  have hg : Syn.subst ![m, W] (Syn.subst ![var 0, sndT (var 1)] G) = inst2 G m (sndT W) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext j; fin_cases j <;> simp
  simp only [inst2, dmBg, PTm.subst_mul, hg]
  simp

/-- The row identity `R(d) = Σ_{m<N+1} [d ∣ m] sg(m) G(m)` for `d ≥ 1`, in every context `Δ ⊇ Θ`. -/
def RowHyp {k : ℕ} (Θ : List (Fm PTm k)) (N h y : PTm k) : Prop :=
  (Δ : List (Fm PTm k)) → (d : PTm k) → Θ ⊆ Δ → (Δ ⊢[PRAAx] d ≐ succ (pred d)) →
    (Δ ⊢[PRAAx] inst2 R d (Zp N h y) ≐ ap2 (sumF (dmBg G)) (succ N) (pairT d (Zp N h y)))

/-! ## Reindexing a row by the multiples of `d` -/

/-- `sg(k) G(dk)` over `0 = k`, `1 = ⟨d, P⟩`. -/
def hBg : PTm 2 := sg (var 0) * Syn.subst ![fstT (var 1) * var 0, sndT (var 1)] G

theorem inst2_hBg (k W : PTm n) : inst2 (hBg G) k W = sg k * inst2 G (fstT W * k) (sndT W) := by
  have hg : Syn.subst ![k, W] (Syn.subst ![fstT (var 1) * var 0, sndT (var 1)] G) = inst2 G (fstT W * k) (sndT W) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext j; fin_cases j <;> simp
  simp only [inst2, hBg, PTm.subst_mul, hg]
  simp

theorem hBg_at (k d P : PTm n) : Γ ⊢[PRAAx] inst2 (hBg G) k (pairT d P) ≐ sg k * inst2 G (d * k) P := by
  rw [inst2_hBg]
  exact congrMul (.eqRefl _) (congrInst2 G (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))

/-- `Σ_{e<N} sg(e+1) G(d(e+1)) = Σ_{m<N+1} [d ∣ m] sg(m) G(m)` for `d ≥ 1`, when `G(m) = 0` for `m > N`. -/
theorem multiples_g {d N h y : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (hz : (Δ : List (Fm PTm (n + 1))) → (t : PTm (n + 1)) → Γ.map Fm.shift ⊆ Δ →
      (Δ ⊢[PRAAx] lt (Syn.shift N) t) → (Δ ⊢[PRAAx] inst2 G t (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) ≐ zero)) :
    Γ ⊢[PRAAx] ap2 (sumF (shiftBody (hBg G))) N (pairT d (Zp N h y)) ≐
      ap2 (sumF (dmBg G)) (succ N) (pairT d (Zp N h y)) := by
  have hd0 : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift d ≐ succ (pred (Syn.shift d)) := by
    simpa [Fm.shift, Syn.shift] using hd.shift
  -- the vanishing term `k = 0`
  have s3 : Γ ⊢[PRAAx] ap2 (sumF (hBg G)) (succ N) (pairT d (Zp N h y)) ≐
      ap2 (sumF (shiftBody (hBg G))) N (pairT d (Zp N h y)) := by
    refine (sum_shift _ _ _).eqTrans ((congrAdd ?_ (.eqRefl _)).eqTrans (zero_add _))
    exact (hBg_at G _ _ _).eqTrans ((congrMul sg_zero (.eqRefl _)).eqTrans (zero_mul _))
  -- reindex the multiples of `d` up to `Nd`
  have cm : Γ ⊢[PRAAx] cM (succ (N * d)) d ≐ succ N :=
    (multiples_upto (Q := N * d) hd).eqTrans (congrSucc (quo_mul hd (mul_comm _ _)))
  have s4 : Γ ⊢[PRAAx] ap2 (sumF (riB (hBg G))) (succ (N * d)) (pairT d (pairT d (Zp N h y))) ≐
      ap2 (sumF (hBg G)) (succ N) (pairT d (Zp N h y)) :=
    (reindex_eq (hBg G) (succ (N * d)) hd).eqTrans (congrAp2 _ cm (.eqRefl _))
  -- the reindexed terms are `[d ∣ m] sg(m) G(m)`
  have s5 : Γ ⊢[PRAAx] ap2 (sumF (riB (hBg G))) (succ (N * d)) (pairT d (pairT d (Zp N h y))) ≐
      ap2 (sumF (dmBg G)) (succ (N * d)) (pairT d (Zp N h y)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [show Syn.shift (pairT d (pairT d (Zp N h y))) =
        pairT (Syn.shift d) (pairT (Syn.shift d) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y))) by simp [Syn.shift],
      show Syn.shift (pairT d (Zp N h y)) = pairT (Syn.shift d) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) by
        simp [Syn.shift],
      inst2_riB, inst2_dmBg]
    let P : PTm (n + 1) := Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)
    let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ (N * d))) :: Γ.map Fm.shift
    have hd' : Λ ⊢[PRAAx] Syn.shift d ≐ succ (pred (Syn.shift d)) := hd0.wk
    have f1 : Λ ⊢[PRAAx] fstT (pairT (Syn.shift d) (pairT (Syn.shift d) P)) ≐ Syn.shift d := fst_pair _ _
    have f2 : Λ ⊢[PRAAx] sndT (pairT (Syn.shift d) (pairT (Syn.shift d) P)) ≐ pairT (Syn.shift d) P := snd_pair _ _
    have f3 : Λ ⊢[PRAAx] fstT (pairT (Syn.shift d) P) ≐ Syn.shift d := fst_pair _ _
    have f4 : Λ ⊢[PRAAx] sndT (pairT (Syn.shift d) P) ≐ P := snd_pair _ _
    have l : Λ ⊢[PRAAx] eqb (rem (var 0) (fstT (pairT (Syn.shift d) (pairT (Syn.shift d) P)))) zero *
        inst2 (hBg G) (quo (var 0) (fstT (pairT (Syn.shift d) (pairT (Syn.shift d) P))))
          (sndT (pairT (Syn.shift d) (pairT (Syn.shift d) P))) ≐
        eqb (rem (var 0) (Syn.shift d)) zero *
          (sg (quo (var 0) (Syn.shift d)) * inst2 G (Syn.shift d * quo (var 0) (Syn.shift d)) P) :=
      congrMul (congrEqb' (congrAp2 remF (.eqRefl _) f1) (.eqRefl _))
        ((congrInst2 (hBg G) (congrAp2 quoF (.eqRefl _) f1) f2).eqTrans (hBg_at G _ _ _))
    have r : Λ ⊢[PRAAx] eqb (rem (var 0) (fstT (pairT (Syn.shift d) P))) zero * sg (var 0) *
        inst2 G (var 0) (sndT (pairT (Syn.shift d) P)) ≐ eqb (rem (var 0) (Syn.shift d)) zero * sg (var 0) *
          inst2 G (var 0) P :=
      congrMul (congrMul (congrEqb' (congrAp2 remF (.eqRefl _) f3) (.eqRefl _)) (.eqRefl _))
        (congrInst2 G (.eqRefl _) f4)
    refine l.eqTrans (Prf.eqTrans ?_ r.eqSymm)
    refine .orE (eqb_cases (Γ := Λ) (rem (var 0) (Syn.shift d)) zero) ?_ ?_
    · have z : ((eqb (rem (var 0) (Syn.shift d)) zero ≐ zero) :: Λ) ⊢[PRAAx]
          eqb (rem (var 0) (Syn.shift d)) zero ≐ zero := Prf.hyp0
      exact ((congrMul z (.eqRefl _)).eqTrans (zero_mul _)).eqTrans
        ((congrMul (congrMul z (.eqRefl _)) (.eqRefl _)).eqTrans
          ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))).eqSymm
    · let C : List (Fm PTm (n + 1)) := (eqb (rem (var 0) (Syn.shift d)) zero ≐ one) :: Λ
      have o : C ⊢[PRAAx] eqb (rem (var 0) (Syn.shift d)) zero ≐ one := Prf.hyp0
      have r0 : C ⊢[PRAAx] rem (var 0) (Syn.shift d) ≐ zero := eq_of_eqb o
      have dv : C ⊢[PRAAx] Syn.shift d * quo (var 0) (Syn.shift d) ≐ var 0 :=
        ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) r0.eqSymm)).eqTrans (div_eq hd'.wk).eqSymm
      have sgq : C ⊢[PRAAx] sg (quo (var 0) (Syn.shift d)) ≐ sg (var 0) :=
        (sg_mul_pos hd'.wk _).eqSymm.eqTrans (congrSg dv)
      exact (congrMul (.eqRefl _) (congrMul sgq (congrInst2 G dv (.eqRefl _)))).eqTrans (mul_assoc _ _ _).eqSymm
  -- the terms beyond `N` vanish
  have hNd : Γ ⊢[PRAAx] le (succ N) (succ (N * d)) := by
    have m := mul_le_mul_right N (le_congr (.eqRefl _) hd.eqSymm (by ipra_le 𝔞 (pred d)) : Γ ⊢[PRAAx] le one d)
    ipra_le sl m
  have s6 : Γ ⊢[PRAAx] ap2 (sumF (dmBg G)) (succ (N * d)) (pairT d (Zp N h y)) ≐
      ap2 (sumF (dmBg G)) (succ N) (pairT d (Zp N h y)) := by
    refine sum_cut (dmBg G) hNd (.allI ?_)
    rw [show Syn.shift (pairT d (Zp N h y)) = pairT (Syn.shift d) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) by
        simp [Syn.shift],
      show Syn.shift (succ N) = succ (Syn.shift N) by simp [Syn.shift], inst2_dmBg]
    have z := hz (Γ.map Fm.shift) (succ (Syn.shift N) + var 0) (List.Subset.refl _) (by ipra_le 𝔞 (var 0))
    exact (congrMul (.eqRefl _) ((congrInst2 G (.eqRefl _) (snd_pair _ _)).eqTrans z)).eqTrans (mul_zero _)
  exact s3.eqSymm.eqTrans (s4.eqSymm.eqTrans (s5.eqTrans s6))

/-! ## Rows -/

/-- Row `d`: `sg(d) w(d) R(d) = Σ_{m<N+1} a3(d, m)`. -/
theorem row_pt_g {N h y : PTm n} (hrow : RowHyp G R Γ N h y) (d : PTm n) :
    Γ ⊢[PRAAx] inst2 (rBg R w) d (Zp N h y) ≐ ap2 (sumF (rowB (a3g G w))) (succ N) (pairT d (Zp N h y)) := by
  rw [inst2_rBg]
  refine .orE (lt_or_le zero d) ?_ ?_
  · let C : List (Fm PTm n) := lt zero d :: Γ
    have hd : C ⊢[PRAAx] d ≐ succ (pred d) := pos_of_one_le Prf.hyp0
    have ri := hrow C d (List.subset_cons_self _ _) hd
    refine (congrMul (.eqRefl _) ri).eqTrans ?_
    refine (sum_const_mul (dmBg G) (succ N) (sg d * inst2 w d (Zp N h y)) (pairT d (Zp N h y))).eqSymm.eqTrans ?_
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [show Syn.shift (pairT (sg d * inst2 w d (Zp N h y)) (pairT d (Zp N h y))) =
        pairT (sg (Syn.shift d) * inst2 w (Syn.shift d) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)))
          (pairT (Syn.shift d) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y))) by simp [Syn.shift],
      show Syn.shift (pairT d (Zp N h y)) = pairT (Syn.shift d) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) by
        simp [Syn.shift],
      inst2_cmB, inst2_rowB, inst3_a3g, inst2_dmBg]
    let P : PTm (n + 1) := Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)
    let K : PTm (n + 1) := sg (Syn.shift d) * inst2 w (Syn.shift d) P
    let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ N)) :: C.map Fm.shift
    have f1 : Λ ⊢[PRAAx] fstT (pairT K (pairT (Syn.shift d) P)) ≐ K := fst_pair _ _
    have f2 : Λ ⊢[PRAAx] sndT (pairT K (pairT (Syn.shift d) P)) ≐ pairT (Syn.shift d) P := snd_pair _ _
    have f3 : Λ ⊢[PRAAx] fstT (pairT (Syn.shift d) P) ≐ Syn.shift d := fst_pair _ _
    have f4 : Λ ⊢[PRAAx] sndT (pairT (Syn.shift d) P) ≐ P := snd_pair _ _
    have lhs : Λ ⊢[PRAAx] fstT (pairT K (pairT (Syn.shift d) P)) *
        (eqb (rem (var 0) (fstT (sndT (pairT K (pairT (Syn.shift d) P))))) zero * sg (var 0) *
          inst2 G (var 0) (sndT (sndT (pairT K (pairT (Syn.shift d) P))))) ≐
        K * (eqb (rem (var 0) (Syn.shift d)) zero * sg (var 0) * inst2 G (var 0) P) :=
      congrMul f1 (congrMul (congrMul (congrEqb' (congrAp2 remF (.eqRefl _) ((congrFst f2).eqTrans f3)) (.eqRefl _))
        (.eqRefl _)) (congrInst2 G (.eqRefl _) ((congrSnd f2).eqTrans f4)))
    have rhs : Λ ⊢[PRAAx] (sg (fstT (pairT (Syn.shift d) P)) *
        inst2 w (fstT (pairT (Syn.shift d) P)) (sndT (pairT (Syn.shift d) P))) *
        (eqb (rem (var 0) (fstT (pairT (Syn.shift d) P))) zero * sg (var 0) *
          inst2 G (var 0) (sndT (pairT (Syn.shift d) P))) ≐
        K * (eqb (rem (var 0) (Syn.shift d)) zero * sg (var 0) * inst2 G (var 0) P) :=
      congrMul (congrMul (congrSg f3) (congrInst2 w f3 f4))
        (congrMul (congrMul (congrEqb' (congrAp2 remF (.eqRefl _) f3) (.eqRefl _)) (.eqRefl _))
          (congrInst2 G (.eqRefl _) f4))
    exact lhs.eqTrans rhs.eqSymm
  · let C : List (Fm PTm n) := le d zero :: Γ
    have hd : C ⊢[PRAAx] d ≐ zero := (monus_zero d).eqSymm.eqTrans Prf.hyp0
    have s0 : C ⊢[PRAAx] sg d ≐ zero := (congrSg hd).eqTrans sg_zero
    refine ((congrMul (congrMul s0 (.eqRefl _)) (.eqRefl _)).eqTrans
      ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))).eqTrans ?_
    refine (sum_zero_of_all _ _ (.allI ?_) _).eqSymm
    rw [show Syn.shift (pairT d (Zp N h y)) = pairT (Syn.shift d) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) by
        simp [Syn.shift], inst2_rowB, inst3_a3g]
    have s0' : (C.map Fm.shift) ⊢[PRAAx] sg (fstT (pairT (Syn.shift d) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)))) ≐
        zero := by
      have b : (C.map Fm.shift) ⊢[PRAAx] sg (Syn.shift d) ≐ zero := by simpa [Fm.shift, Syn.shift] using s0.shift
      exact (congrSg (fst_pair _ _)).eqTrans b
    exact (congrMul ((congrMul s0' (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans (zero_mul _)

/-! ## Columns -/

/-- Column `m`: `Σ_{d<N+1} a3(d, m) = sg(m) G(m) · Σ_{d<N+1} sg(d)[d ∣ m] w(d)`. -/
theorem col_pt_g (m N h y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (a3g G w))) (succ N) (pairT m (Zp N h y)) ≐
      (sg m * inst2 G m (Zp N h y)) * ap2 (sumF (kB w)) (succ N) (pairT m (Zp N h y)) := by
  refine Prf.eqTrans ?_ (sum_const_mul (kB w) (succ N) (sg m * inst2 G m (Zp N h y)) (pairT m (Zp N h y)))
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [show Syn.shift (pairT m (Zp N h y)) = pairT (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) by
      simp [Syn.shift],
    show Syn.shift (pairT (sg m * inst2 G m (Zp N h y)) (pairT m (Zp N h y))) =
      pairT (sg (Syn.shift m) * inst2 G (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)))
        (pairT (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y))) by simp [Syn.shift],
    inst2_colB, inst3_a3g, inst2_cmB, inst2_kB]
  let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift
  let P : PTm (n + 1) := Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)
  have f1 : Λ ⊢[PRAAx] fstT (pairT (Syn.shift m) P) ≐ Syn.shift m := fst_pair _ _
  have f2 : Λ ⊢[PRAAx] sndT (pairT (Syn.shift m) P) ≐ P := snd_pair _ _
  have g1 : Λ ⊢[PRAAx] fstT (pairT (sg (Syn.shift m) * inst2 G (Syn.shift m) P) (pairT (Syn.shift m) P)) ≐
      sg (Syn.shift m) * inst2 G (Syn.shift m) P := fst_pair _ _
  have g2 : Λ ⊢[PRAAx] sndT (pairT (sg (Syn.shift m) * inst2 G (Syn.shift m) P) (pairT (Syn.shift m) P)) ≐
      pairT (Syn.shift m) P := snd_pair _ _
  have lhs : Λ ⊢[PRAAx] (sg (var 0) * inst2 w (var 0) (sndT (pairT (Syn.shift m) P))) *
      (eqb (rem (fstT (pairT (Syn.shift m) P)) (var 0)) zero * sg (fstT (pairT (Syn.shift m) P)) *
        inst2 G (fstT (pairT (Syn.shift m) P)) (sndT (pairT (Syn.shift m) P))) ≐
      (sg (var 0) * inst2 w (var 0) P) *
        (eqb (rem (Syn.shift m) (var 0)) zero * sg (Syn.shift m) * inst2 G (Syn.shift m) P) :=
    congrMul (congrMul (.eqRefl _) (congrInst2 w (.eqRefl _) f2))
      (congrMul (congrMul (congrEqb' (congrAp2 remF f1 (.eqRefl _)) (.eqRefl _)) (congrSg f1)) (congrInst2 G f1 f2))
  have rhs : Λ ⊢[PRAAx] fstT (pairT (sg (Syn.shift m) * inst2 G (Syn.shift m) P) (pairT (Syn.shift m) P)) *
      ((sg (var 0) * eqb (rem (fstT (sndT (pairT (sg (Syn.shift m) * inst2 G (Syn.shift m) P)
        (pairT (Syn.shift m) P)))) (var 0)) zero) *
        inst2 w (var 0) (sndT (sndT (pairT (sg (Syn.shift m) * inst2 G (Syn.shift m) P) (pairT (Syn.shift m) P))))) ≐
      (sg (Syn.shift m) * inst2 G (Syn.shift m) P) *
        ((sg (var 0) * eqb (rem (Syn.shift m) (var 0)) zero) * inst2 w (var 0) P) :=
    congrMul g1 (congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF ((congrFst g2).eqTrans f1) (.eqRefl _))
      (.eqRefl _))) (congrInst2 w (.eqRefl _) ((congrSnd g2).eqTrans f2)))
  refine lhs.eqTrans (Prf.eqTrans ?_ rhs.eqSymm)
  ipra_ring

/-- `Σ_{d<N+1} sg(d) w(d) R(d) = Σ_{m<N+1} sg(m) G(m) · Σ_{d<N+1} sg(d)[d ∣ m] w(d)`. -/
theorem rs_columns_g {N h y : PTm n}
    (hrow : RowHyp G R (Γ.map Fm.shift) (Syn.shift N) (Syn.shift h) (Syn.shift y)) :
    Γ ⊢[PRAAx] RSg R w N h y ≐ ap2 (sumF (pB (a3g G w))) (succ N) (pairT (succ N) (Zp N h y)) := by
  have r : Γ ⊢[PRAAx] RSg R w N h y ≐ ap2 (sumF (oB (a3g G w))) (succ N) (pairT (succ N) (Zp N h y)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [show Syn.shift (Zp N h y) = Zp (Syn.shift N) (Syn.shift h) (Syn.shift y) by simp [Syn.shift],
      show Syn.shift (pairT (succ N) (Zp N h y)) = pairT (succ (Syn.shift N)) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) by
        simp [Syn.shift]]
    have hr' : RowHyp G R (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) (Syn.shift N) (Syn.shift h) (Syn.shift y) :=
      fun Δ d s hd => hrow Δ d (fun _ hx => s (List.mem_cons_of_mem _ hx)) hd
    exact (row_pt_g G R w hr' (var 0)).eqTrans (oB_at (a3g G w) _ _ _).eqSymm
  exact r.eqTrans (fubini (a3g G w) (succ N) (succ N) (Zp N h y))

/-! ## The inversion -/

/-- The delta term `sg(m) G(m)`. -/
abbrev sGBg : PTm 2 := sg (var 0) * G

theorem inst2_sGBg (m P : PTm n) : inst2 (sGBg G) m P = sg m * inst2 G m P := by simp [inst2]

/-- Column `m ≤ N` of the difference: `col⁺(m) = col⁻(m) + [m = 1] sg(m) G(m)`. -/
theorem col_cancel_g {m N h y : PTm n} (hm : Γ ⊢[PRAAx] lt m (succ N)) :
    Γ ⊢[PRAAx] inst2 (pB (a3g G wP)) m (pairT (succ N) (Zp N h y)) ≐
      inst2 (pB (a3g G wN)) m (pairT (succ N) (Zp N h y)) + inst2 (dB (sGBg G)) m (pairT one (Zp N h y)) := by
  have cp := (pB_at (Γ := Γ) (a3g G wP) m (succ N) (Zp N h y)).eqTrans
    ((col_pt_g G wP m N h y).eqTrans (congrMul (.eqRefl _) (Prf.andE₁ (kB_mu m N h y))))
  have cn := (pB_at (Γ := Γ) (a3g G wN) m (succ N) (Zp N h y)).eqTrans
    ((col_pt_g G wN m N h y).eqTrans (congrMul (.eqRefl _) (Prf.andE₂ (kB_mu m N h y))))
  have dl : Γ ⊢[PRAAx] inst2 (dB (sGBg G)) m (pairT one (Zp N h y)) ≐ eqb one m * (sg m * inst2 G m (Zp N h y)) := by
    rw [inst2_dB, inst2_sGBg]
    exact congrMul (congrEqb' (fst_pair _ _) (.eqRefl _))
      (congrMul (.eqRefl _) (congrInst2 G (.eqRefl _) (snd_pair _ _)))
  refine cp.eqTrans (Prf.eqTrans ?_ (congrAdd cn dl).eqSymm)
  refine .orE (lt_or_le zero m) ?_ ?_
  · let C : List (Fm PTm n) := lt zero m :: Γ
    have hk : C ⊢[PRAAx] m ≐ succ (pred m) := pos_of_one_le Prf.hyp0
    have cg := cancel_gen (Γ := C) hk (N := succ N) (K := succ N) hm.wk hm.wk
    refine (congrMul (.eqRefl _) cg).eqTrans ((mul_add _ _ _).eqTrans (congrAdd (.eqRefl _) ?_))
    exact (mul_comm _ _).eqTrans (congrMul (eqb_comm' m one) (.eqRefl _))
  · let C : List (Fm PTm n) := le m zero :: Γ
    have hz : C ⊢[PRAAx] m ≐ zero := (monus_zero m).eqSymm.eqTrans Prf.hyp0
    have hX : C ⊢[PRAAx] sg m * inst2 G m (Zp N h y) ≐ zero :=
      (congrMul ((congrSg hz).eqTrans sg_zero) (.eqRefl _)).eqTrans (zero_mul _)
    refine ((congrMul hX (.eqRefl _)).eqTrans (zero_mul _)).eqTrans ?_
    refine (Prf.eqTrans ?_ (congrAdd ((congrMul hX (.eqRefl _)).eqTrans (zero_mul _))
      ((congrMul (.eqRefl _) hX).eqTrans (mul_zero _))).eqSymm)
    exact (add_zero _).eqSymm

/-- Abstract finite inversion: `Σ_{d≤N} μ⁺(d) R(d) = Σ_{d≤N} μ⁻(d) R(d) + T` from the row identity, `G(1) = T` and
`T = 0` at `N = 0`. -/
theorem inversion_g {N h y T : PTm n}
    (hrow : RowHyp G R (Γ.map Fm.shift) (Syn.shift N) (Syn.shift h) (Syn.shift y))
    (hG1 : Γ ⊢[PRAAx] inst2 G one (Zp N h y) ≐ T) (hT0 : (le N zero :: Γ) ⊢[PRAAx] T ≐ zero) :
    Γ ⊢[PRAAx] RSg R wP N h y ≐ RSg R wN N h y + T := by
  refine (rs_columns_g G R wP hrow).eqTrans ?_
  refine Prf.eqTrans ?_ (congrAdd (rs_columns_g G R wN hrow).eqSymm (.eqRefl _))
  have sp := sum_add2 (Γ := Γ) (pB (a3g G wN)) (dB (sGBg G)) (pB (a3g G wP)) (K := succ N)
    (x := pairT (succ N) (Zp N h y)) (x' := pairT one (Zp N h y)) (z := pairT (succ N) (Zp N h y))
    (.allI (.impI (by
      rw [show Syn.shift (pairT (succ N) (Zp N h y)) =
          pairT (succ (Syn.shift N)) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) by simp [Syn.shift],
        show Syn.shift (pairT one (Zp N h y)) = pairT one (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) by
          simp [Syn.shift]]
      have hm : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift N)) := by
        have b := (Prf.hyp0 : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] _)
        simpa [Syn.shift] using b
      exact col_cancel_g G hm)))
  refine sp.eqTrans (congrAdd (.eqRefl _) ?_)
  refine .orE (lt_or_le zero N) ?_ ?_
  · have h1 : (lt zero N :: Γ) ⊢[PRAAx] lt one (succ N) := by
      have b : (lt zero N :: Γ) ⊢[PRAAx] lt zero N := Prf.hyp0; ipra_le sl b
    refine (sum_delta (sGBg G) h1).eqTrans ?_
    rw [inst2_sGBg]
    exact ((congrMul (sg_succ _) hG1.wk).eqTrans (one_mul _))
  · let C : List (Fm PTm n) := le N zero :: Γ
    have hz : C ⊢[PRAAx] N ≐ zero := (monus_zero N).eqSymm.eqTrans Prf.hyp0
    have d0 : C ⊢[PRAAx] ap2 (sumF (dB (sGBg G))) (succ N) (pairT one (Zp N h y)) ≐ zero := by
      refine (congrAp2 _ (congrSucc hz) (.eqRefl _)).eqTrans ((sum_succ _ _ _).eqTrans ?_)
      refine (congrAdd (sum_zero _ _) ?_).eqTrans (add_zero _)
      change C ⊢[PRAAx] inst2 (dB (sGBg G)) zero (pairT one (Zp N h y)) ≐ zero
      rw [inst2_dB]
      have e : C ⊢[PRAAx] eqb (fstT (pairT one (Zp N h y))) zero ≐ zero :=
        (congrEqb' (fst_pair _ _) (.eqRefl _)).eqTrans
          (LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc.eqb_succ_zero zero)
      exact (congrMul e (.eqRefl _)).eqTrans (zero_mul _)
    exact d0.eqTrans hT0.eqSymm

end LeanProofs.IPRA.AnalyticNumberTheory.PowerAbstractInversion
