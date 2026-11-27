import IPRADerivations.AnalyticNumberTheory.WeightedBound
import IPRADerivations.AnalyticNumberTheory.AbelParts

/-!
# The variation of `|R(x/n)|` (`pnt_ipra_constructive_2026-11-14`, `sb:weighted-sum`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:weighted-sum`:
"Monotonicity of `ψ` gives `|g_n − g_{n+1}| ≤ ψ(x/n) − ψ(x/(n+1)) + x/(n(n+1))`. … Therefore
`Σ_{n=1}^N n|g_n − g_{n+1}| ≤ x Σ_{m≤x} Λ(m)/m + x Σ_{n=1}^N 1/(n+1)`." With `g_n = |ψ(⌊x/n⌋) − F⌊x/n⌋|` and
`h_n = ψ(⌊x/n⌋) + F⌊x/n⌋` (both functions of `⌊x/n⌋`, `h` decreasing in `n`):

* `absd_absd`, `pure_dec`: `||P − Q| − |P' − Q'|| ≤ (P + Q) ∸ (P' + Q')` when `P' ≤ P`, `Q' ≤ Q`;
* `var_le`: `Σ_{n≤x} n |g_n − g_{n+1}| ≤ Σ_{n≤x} n (h_n ∸ h_{n+1})`;
* `dn_eq`: `Σ_{n≤x} n (h_n ∸ h_{n+1}) = Σ_{1≤n≤x} h_n` (`AbelParts.abel_parts` with the coefficient `[n ≥ 1]`; `h_{x+1} = 0`);
* `h_le`: `Σ_{1≤n≤x} h_n ≤ 5x S(x, F)`, since `ψ(m) ≤ 4mF` and `F⌊x/n⌋ ≤ x F/n` exactly (`n ∣ F = L!`);
* `variation`: `Σ_{n≤x} n |g_n − g_{n+1}| ≤ 5x (u_x + F)` (`harm_one`: `S(x, F) ≤ u_x + F`).
-/

set_option linter.unusedSectionVars false

namespace LeanProofs.IPRA.AnalyticNumberTheory.WeightedVariation

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h quo_anti)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd absd_le le_absd_l le_absd_r absd_symm absd_triangle adB inst2_adB)
open LeanProofs.IPRA.AnalyticNumberTheory.AbelParts (agB upB dnB inst2_agB inst2_upB inst2_dnB inst2_g1 abel_parts)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedBound (psiB qB inst2_psiB inst2_qB)
open LeanProofs.IPRA.AnalyticNumberTheory.ComparisonEnvelope (harm_one)
open LeanProofs.IPRA.AnalyticNumberTheory.ErrorEquation (eU')
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (Q4)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (Bs inst2_bS)
open LeanProofs.IPRA.Probability.Lotus (cmB sum_const_mul)
open LeanProofs.IPRA.Probability.Independence (cm_pt)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Elementary facts -/

theorem quo_self_succ (x : PTm n) : Γ ⊢[PRAAx] quo x (succ x) ≐ zero :=
  Prf.andE₁ (div_mod_unique (q := zero) (r := x) (by ipra_ring) (le_refl _))

theorem absd_absd (a b c d : PTm n) : Γ ⊢[PRAAx] le (absd (absd a b) (absd c d)) (absd a c + absd b d) := by
  have t1 := absd_triangle (Γ := Γ) a c b; have t2 := absd_triangle (Γ := Γ) c d b
  have s1 := natEq (absd_symm (Γ := Γ) d b)
  have t3 := absd_triangle (Γ := Γ) c a d; have t4 := absd_triangle (Γ := Γ) a b d
  have s2 := natEq (absd_symm (Γ := Γ) c a)
  exact absd_le (by ipra_le sl t1 + sl t2 with s1) (by ipra_le sl t3 + sl t4 with s2)

theorem pure_dec {P Q P' Q' : PTm n} (hp : Γ ⊢[PRAAx] le P' P) (hq : Γ ⊢[PRAAx] le Q' Q) :
    Γ ⊢[PRAAx] le (absd (absd P Q) (absd P' Q')) (monus (P + Q) (P' + Q')) := by
  refine le_trans (absd_absd P Q P' Q') ?_
  have e1 := natEq (eq_add_of_le hp); have z1 := natEq hp
  have e2 := natEq (eq_add_of_le hq); have z2 := natEq hq
  have hpq : Γ ⊢[PRAAx] le (P' + Q') (P + Q) := by ipra_le sl hp + sl hq
  have eM := natEq (eq_add_of_le hpq)
  ipra_le 0 with -eM + e1 + e2 - z1 - z2

theorem psi_le_le {a b : PTm n} (y : PTm n) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (Psi wt a y) (Psi wt b y) :=
  sum_le_bound _ ((succ_monus_succ _ _).eqTrans h)

theorem qdec {k : PTm n} (x : PTm n) (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) :
    Γ ⊢[PRAAx] le (quo x (succ k)) (quo x k) :=
  quo_anti hk (le_succ_self k)

theorem absdC {m : ℕ} {Δ : List (Fm PTm m)} {a a' b b' : PTm m} (h₁ : Δ ⊢[PRAAx] a ≐ a') (h₂ : Δ ⊢[PRAAx] b ≐ b') :
    Δ ⊢[PRAAx] absd a b ≐ absd a' b' :=
  congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁)

theorem zero_mul_l' {m : ℕ} {Δ : List (Fm PTm m)} {a b : PTm m} (h : Δ ⊢[PRAAx] le a b) (c : PTm m) :
    Δ ⊢[PRAAx] c * monus a b ≐ zero :=
  (congrMul (.eqRefl c) h).eqTrans (mul_zero _)

/-! ## Bodies at `⌊x/n⌋` -/

/-- `f(⌊x/n⌋, y)` over `0 = n`, `1 = (x, y)`. -/
def gZ (f : PTm 2) : PTm 2 := Syn.subst ![quo (fstT (var 1)) (var 0), sndT (var 1)] f

theorem inst2_gZ (f : PTm 2) (k z : PTm n) : inst2 (gZ f) k z = inst2 f (quo (fstT z) k) (sndT z) := by
  simp only [inst2, gZ, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp

theorem gZ_at (f : PTm 2) (k x y : PTm n) : Γ ⊢[PRAAx] inst2 (gZ f) k (pairT x y) ≐ inst2 f (quo x k) y := by
  rw [inst2_gZ]; exact congrInst2 f (congrAp2 quoF (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

/-- `g_n = |ψ(⌊x/n⌋) − F⌊x/n⌋|`. -/
abbrev gB : PTm 2 := gZ (adB psiB qB)
/-- `h_n = ψ(⌊x/n⌋) + F⌊x/n⌋`. -/
abbrev hB : PTm 2 := gZ (psiB + qB)
/-- The coefficient `[n ≥ 1]`. -/
abbrev sgB : PTm 2 := sg (var 0)

theorem inst2_sgB (k z : PTm n) : inst2 sgB k z = sg k := by simp [inst2]

/-- `Σ_{k≤n} [k ≥ 1] = n`. -/
theorem sg_sum (N z : PTm n) : Γ ⊢[PRAAx] ap2 (sumF sgB) (succ N) z ≐ N := by
  refine .eqTrans ?_ (SymmetryInstances.sum_sg_one N z)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_sgB, MobiusSummatory.inst2_gS, Mobius.one_inst]
  ipra_ring

/-! ## Values at a point -/

section Point
variable {x K L : PTm n}

abbrev Pv (k x K L : PTm n) : PTm n := Psi wt (quo x k) (pairT K (fact L))
abbrev Qv (k x L : PTm n) : PTm n := fact L * quo x k

theorem g_at (k : PTm n) : Γ ⊢[PRAAx] inst2 gB k (pairT x (pairT K (fact L))) ≐ absd (Pv k x K L) (Qv k x L) := by
  refine (gZ_at _ _ _ _).eqTrans ?_
  rw [inst2_adB, inst2_psiB, inst2_qB]
  exact absdC (.eqRefl _) (congrMul (snd_pair _ _) (.eqRefl _))

theorem h_at (k : PTm n) : Γ ⊢[PRAAx] inst2 hB k (pairT x (pairT K (fact L))) ≐ Pv k x K L + Qv k x L := by
  refine (gZ_at _ _ _ _).eqTrans ?_
  rw [inst2_add, inst2_psiB, inst2_qB]
  exact congrAdd (.eqRefl _) (congrMul (snd_pair _ _) (.eqRefl _))

theorem h_end : Γ ⊢[PRAAx] inst2 hB (succ x) (pairT x (pairT K (fact L))) ≐ zero := by
  refine (h_at (succ x)).eqTrans ?_
  have q := quo_self_succ (Γ := Γ) x
  have p0 := WeightedBound.psi_zero (Δ := Γ) (pairT K (fact L))
  rw [inst2_psiB] at p0
  have p : Γ ⊢[PRAAx] Pv (succ x) x K L ≐ zero := (congrAp2 _ (congrSucc q) (.eqRefl _)).eqTrans p0
  have r : Γ ⊢[PRAAx] Qv (succ x) x L ≐ zero := (congrMul (.eqRefl _) q).eqTrans (mul_zero _)
  exact (congrAdd p r).eqTrans (add_zero _)

/-- `h` decreases: `h_{k+1} ≤ h_k` for `k ≥ 1`. -/
theorem P_dec {k : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) : Γ ⊢[PRAAx] le (Pv (succ k) x K L) (Pv k x K L) :=
  psi_le_le _ (qdec x hk)

theorem Q_dec {k : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) : Γ ⊢[PRAAx] le (Qv (succ k) x L) (Qv k x L) :=
  le_scale _ (qdec x hk)

end Point

/-! ## The variation sum -/

/-- `n |g_n − g_{n+1}|`. -/
abbrev nabsB : PTm 2 := var 0 * absd gB (Syn.subst ![succ (var 0), var 1] gB)
/-- `n (h_n ∸ h_{n+1})`. -/
abbrev ndhB : PTm 2 := var 0 * monus hB (Syn.subst ![succ (var 0), var 1] hB)

theorem inst2_nabs (k z : PTm n) : inst2 nabsB k z = k * absd (inst2 gB k z) (inst2 gB (succ k) z) := by
  simp only [nabsB, inst2, PTm.subst_mul, PTm.subst_add, PTm.subst_monus, Syn.subst_var]
  rw [inst2_g1]; simp [inst2]

theorem inst2_ndh (k z : PTm n) : inst2 ndhB k z = k * monus (inst2 hB k z) (inst2 hB (succ k) z) := by
  simp only [ndhB, inst2, PTm.subst_mul, PTm.subst_monus, Syn.subst_var]
  rw [inst2_g1]; simp [inst2]

theorem var_pt {x K L : PTm n} (k : PTm n) :
    Γ ⊢[PRAAx] le (inst2 nabsB k (pairT x (pairT K (fact L)))) (inst2 ndhB k (pairT x (pairT K (fact L)))) := by
  rw [inst2_nabs, inst2_ndh]
  refine .orE (zero_or_succ k) ?_ ?_
  · exact le_congr (zero_mul_l Prf.hyp0 _).eqSymm (zero_mul_l Prf.hyp0 _).eqSymm (le_refl _)
  · have hk : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
    have d := pure_dec (P_dec (x := x) (K := K) (L := L) hk) (Q_dec (x := x) (L := L) hk)
    refine le_scale k (le_congr (absdC (g_at k) (g_at (succ k))).eqSymm
      (congrMonus (h_at k) (h_at (succ k))).eqSymm d)

theorem var_le (x K L : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF nabsB) (succ x) (pairT x (pairT K (fact L))))
      (ap2 (sumF ndhB) (succ x) (pairT x (pairT K (fact L)))) :=
  sum_le_params _ _ _ _ _ (.allI (.impI (by
    simp only [shift_pairT, shift_fact']
    exact var_pt _)))

/-- `Σ_{n≤x} n(h_n ∸ h_{n+1}) = Σ_{1≤n≤x} h_n`. -/
theorem dn_eq (x K L : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF ndhB) (succ x) (pairT x (pairT K (fact L))) ≐
      ap2 (sumF (agB sgB hB)) (succ x) (pairT x (pairT K (fact L))) := by
  -- the upward part vanishes
  have up : Γ ⊢[PRAAx] le (ap2 (sumF (upB sgB hB)) (succ x) (pairT x (pairT K (fact L)))) (succ x * zero) :=
    sum_le_const _ (.allI (.impI (by
      simp only [shift_pairT, shift_fact']
      rw [inst2_upB, show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]]
      refine .orE (zero_or_succ (var 0)) ?_ ?_
      · have a0 : ((var 0 ≐ zero) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
            ap2 (sumF sgB) (succ (var 0)) (pairT (Syn.shift x) (pairT (Syn.shift K) (fact (Syn.shift L)))) ≐ zero :=
          (congrAp2 (sumF sgB) (congrSucc Prf.hyp0) (.eqRefl _)).eqTrans (sg_sum zero _)
        exact le_congr (zero_mul_l a0 _).eqSymm (.eqRefl _) (le_refl _)
      · have hk : ((var 0 ≐ succ (pred (var 0))) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
            var 0 ≐ succ (pred (var 0)) := Prf.hyp0
        have hd := le_congr (h_at (succ (var 0))).eqSymm (h_at (var 0)).eqSymm
          (by have p := P_dec (x := Syn.shift x) (K := Syn.shift K) (L := Syn.shift L) hk
              have q := Q_dec (x := Syn.shift x) (L := Syn.shift L) hk
              ipra_le sl p + sl q)
        exact le_congr (zero_mul_l' hd _).eqSymm (.eqRefl _) (le_refl _))))
  have c := sum_congr_bounded (Γ := Γ) ndhB (dnB sgB hB) (pairT x (pairT K (fact L))) (pairT x (pairT K (fact L)))
    (succ x) (.allI (.impI (by
      rw [inst2_ndh, inst2_dnB]
      exact congrMul (sg_sum _ _).eqSymm (.eqRefl _))))
  ipra_lc natEq c - natEq (abel_parts sgB hB x (pairT x (pairT K (fact L)))) -
    𝔞 (ap2 (sumF sgB) (succ x) (pairT x (pairT K (fact L)))) * natEq (h_end (x := x) (K := K) (L := L)) +
    natEq (le_antisymm (le_congr (.eqRefl _) (mul_zero _) up) (zero_le _))

/-! ## `Σ h_n ≤ 5x S(x, F)` -/

/-- `[n ≥ 1] ⌊F/n⌋` over `0 = n`, `1 = F`. -/
abbrev sF : PTm 2 := sg (var 0) * quo (var 1) (var 0)

theorem inst2_sF (k F : PTm n) : inst2 sF k F = sg k * quo F k := by simp [inst2]

theorem sF_sum (x F : PTm n) : Γ ⊢[PRAAx] ap2 (sumF sF) (succ x) F ≐ S x F := by
  refine (bs_shift sF x F).eqTrans ?_
  rw [inst2_sF]
  refine (congrAdd (zero_mul_l sg_zero _) (.eqRefl _)).eqTrans ((zero_add _).eqTrans ?_)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_bS, inst2_sF, inst2_h]
  exact (congrMul (sg_succ _) (.eqRefl _)).eqTrans (one_mul _)

theorem h_pt {k x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
    (hkL : Γ ⊢[PRAAx] le k L) :
    Γ ⊢[PRAAx] le (inst2 (agB sgB hB) k (pairT x (pairT K (fact L)))) (inst2 (cmB sF) k (pairT (num 5 * x) (fact L))) := by
  rw [inst2_agB, inst2_sgB]
  refine le_congr (congrMul (.eqRefl _) (h_at k)).eqSymm (cm_pt _ _ _ _).eqSymm ?_
  rw [inst2_sF]
  refine .orE (zero_or_succ k) ?_ ?_
  · exact le_congr (zero_mul_l ((congrSg Prf.hyp0).eqTrans sg_zero) _).eqSymm (.eqRefl _) (zero_le _)
  · let D := (k ≐ succ (pred k)) :: Γ
    have hk : D ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
    have hm : D ⊢[PRAAx] le (quo x k) x :=
      le_congr (congrAp2 quoF (.eqRefl _) hk).eqSymm (.eqRefl _) (DivisorHyperbola.quo_le_self _ _)
    have p := psi_k hK.wk hP.wk hm
    have ef := natEq ((fact_quo (le_congr hk (.eqRefl _) hkL.wk)).eqTrans
      (congrMul hk.eqSymm (congrAp2 quoF (.eqRefl _) hk.eqSymm)))
    have dm := div_mod_at (Γ := D) (x := x) hk
    have hdm : D ⊢[PRAAx] le (k * quo x k) x := le_of_eq_add (d := rem x k) (Prf.andE₁ dm)
    have fm : D ⊢[PRAAx] le (fact L * quo x k) (x * quo (fact L) k) := by
      have q := le_scale (quo (fact L) k) hdm
      ipra_le sl q with 𝔞 (quo x k) * ef
    have s := natEq ((congrSg hk).eqTrans (sg_succ (pred k)))
    ipra_le sl p + 5 * sl fm with (5 * 𝔞 x * 𝔞 (quo (fact L) k) - 𝔞 (Psi wt (quo x k) (pairT K (fact L))) -
      𝔞 (fact L) * 𝔞 (quo x k)) * s

/-- `Σ_{1≤n≤x} h_n ≤ 5x S(x, F)`. -/
theorem h_le {x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
    (hxL : Γ ⊢[PRAAx] le x L) :
    Γ ⊢[PRAAx] le (ap2 (sumF (agB sgB hB)) (succ x) (pairT x (pairT K (fact L)))) (num 5 * x * S x (fact L)) := by
  have hK' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have hP' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * pw two (two * (two * Syn.shift x))) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hP.shift
  have hxL' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift x) (Syn.shift L) := by simpa [Fm.shift, Syn.shift] using hxL.shift
  have p := sum_le_params (Γ := Γ) (agB sgB hB) (cmB sF) (pairT x (pairT K (fact L))) (pairT (num 5 * x) (fact L))
    (succ x) (.allI (.impI (by
      simp only [ConvSummatory.shift_succ_x, shift_pairT, shift_fact']
      rw [show Syn.shift (num 5 * x : PTm n) = num 5 * Syn.shift x by simp [Syn.shift]]
      have hv : (lt (var 0) (succ (Syn.shift x)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift L) :=
        le_trans ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) hxL'.wk
      exact h_pt hK'.wk hP'.wk hv)))
  have c := natEq (sum_const_mul (Γ := Γ) sF (succ x) (num 5 * x) (fact L))
  have f := natEq (sF_sum (Γ := Γ) x (fact L))
  ipra_le sl p with c + 5 * 𝔞 x * f

/-- `Σ_{n≤x} n |g_n − g_{n+1}| ≤ 5x (u_x + F)`. -/
theorem variation {x K L : PTm n} (hx : Γ ⊢[PRAAx] le one x) (hK : Γ ⊢[PRAAx] le one K)
    (hx4 : Γ ⊢[PRAAx] le (Q4 x) K) (hL : Γ ⊢[PRAAx] le (K * Q4 x) L)
    (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L) :
    Γ ⊢[PRAAx] le (ap2 (sumF nabsB) (succ x) (pairT x (pairT K (fact L))))
      (num 5 * x * (U x K (fact L) + fact L)) := by
  have hKx : Γ ⊢[PRAAx] le (K * x) L := le_trans (le_scale K (le_Q4 x)) hL
  have hxL : Γ ⊢[PRAAx] le x L := le_trans (le_of_eq_add (d := (pred K) * x) (by
    ipra_lc 𝔞 x * natEq (pos_of_lt_zero hK))) hKx
  have v := var_le (Γ := Γ) x K L
  have d := natEq (dn_eq (Γ := Γ) x K L)
  have h := h_le hK hP hxL
  have ho := harm_one hK hx hKx
  have e := natEq (eU' (K := K) (L := L) (Γ := Γ) hx)
  have hs := le_scale (num 5 * x) ho
  ipra_le sl v + sl h + sl hs with d + 5 * 𝔞 x * e

end LeanProofs.IPRA.AnalyticNumberTheory.WeightedVariation
