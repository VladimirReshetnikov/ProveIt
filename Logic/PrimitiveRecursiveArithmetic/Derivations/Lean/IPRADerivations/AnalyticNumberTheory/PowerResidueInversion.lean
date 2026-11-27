import IPRADerivations.AnalyticNumberTheory.PowerResidueRows

/-!
# Möbius inversion for progression rows (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, proof of Theorem
`thm:powerdivisor`: "The reverse formula uses `μ(d) B_{h,q,b_d}`. To verify inversion, a product `s = de` is a unit
exactly when both factors are units, and the residue selected in two steps is `b_s`. Thus every surviving coefficient
reduces to the same divisor sum as before."

For `q ≥ 2`, a reduced residue `b < q`, `h ≥ 1` and the parameter `P = ⟨⟨N, h⟩, ⟨⟨q, b⟩, ⟨h, y⟩⟩⟩`:

* `Gt`: `G(m) = [gcd(m^h, q) = 1] A_{q,b_{m^h}}(⌊N/m^h⌋)` (`Gt_at`), vanishing for `m > N` (`Gt_vanish`), with
  `G(1) = A_{q,b}(N)` (`Gt_one`);
* `Rt`: `R(d) = [gcd(d^h, q) = 1] B_{h;q,b_{d^h}}(⌊N/d^h⌋)` (`Rt_at`);
* `term_twist`: for a unit `D = d^h`, `[gcd(E,q)=1] A_{q,(b_D)_E}(⌊⌊N/D⌋/E⌋) = sg(e+1) G(d(e+1))` with `E = (e+1)^h`
  (`PowerResidue.res_comp`, and `DE` is a unit exactly when `E` is), `term_zero`: for a nonunit `D` every multiple `m`
  of `d` has `G(m) = 0`;
* `row_res`: the row identity `R(d) = Σ_{m≤N} [d ∣ m] sg(m) G(m)` (`PowerResidueRows.masked_B` at `b_D`, then
  `PowerAbstractInversion.multiples_g`);
* `inversion_res`: `Σ_{d≤N} μ⁺(d) R(d) = Σ_{d≤N} μ⁻(d) R(d) + A_{q,b}(N)`, i.e.
  `A_{q,b}(N) = Σ_{d≤N} μ(d) [gcd(d^h,q)=1] B_{h;q,b_{d^h}}(⌊N/d^h⌋)` (`PowerAbstractInversion.inversion_g`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueInversion

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.PowerAbstractInversion
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueRows
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidue (res res_lt res_cop res_comp res_unique gcd_one_left)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (cop_mul cop_of_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerTwistPrefix (tBt tbtB tbtB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorInversion (Zp wP wN)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorRow (sum_cut lt_succ_pw pw_pos1)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (quo_small)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb' congrSg)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwap (quo_lt')
open LeanProofs.IPRA.Combinatorics.Binomial (eq_of_rem_zero)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable (a : PTm 2)

/-! ## Congruence of the representative -/

theorem res_congr {D D' q b : PTm n} (h : Γ ⊢[PRAAx] D ≐ D') : Γ ⊢[PRAAx] res D q b ≐ res D' q b := by
  have c : Γ ⊢[PRAAx] Syn.subst ![D, q, b] (res (var 0) (var 1) (var 2) : PTm 3) ≐
      Syn.subst ![D', q, b] (res (var 0) (var 1) (var 2) : PTm 3) :=
    Prf.eqCongr _ fun k => by
      fin_cases k
      · exact h
      · exact .eqRefl _
      · exact .eqRefl _
  simp only [PTm.subst_mul, PTm.subst_add, PTm.subst_monus, LeanProofs.IPRA.PTm.subst_pred, subst_eqb, subst_ex2,
    subst_ap2, Bezout.subst_cur, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var] at c
  exact c

theorem shift_res' (d h q b : PTm n) :
    Syn.shift (res (pw d h) q b) = res (pw (Syn.shift d) (Syn.shift h)) (Syn.shift q) (Syn.shift b) := by
  ipra_ind_simp [Syn.shift, subst_eqb, subst_ex2, subst_ap2, Bezout.subst_cur]

/-! ## The column and row bodies -/

/-- `[gcd(m^h,q)=1] A_{q,b_{m^h}}(⌊N/m^h⌋)` over `0 = m`, `1 = N`, `2 = q`, `3 = b`, `4 = h`, `5 = y`. -/
def GtC : PTm 6 :=
  eqb (gcd (pw (var 0) (var 4)) (var 2)) one * Apre (mask a) (quo (var 1) (pw (var 0) (var 4)))
    (pairT (pairT (var 2) (res (pw (var 0) (var 4)) (var 2) (var 3))) (var 5))

/-- `[gcd(d^h,q)=1] B_{h;q,b_{d^h}}(⌊N/d^h⌋)` over the same variables. -/
def RtC : PTm 6 :=
  eqb (gcd (pw (var 0) (var 4)) (var 2)) one *
    MB a (quo (var 1) (pw (var 0) (var 4))) (var 2) (res (pw (var 0) (var 4)) (var 2) (var 3)) (var 4) (var 5)

/-- The bodies at `P = ⟨⟨N, h⟩, ⟨⟨q, b⟩, ⟨h, y⟩⟩⟩`. -/
def Gt : PTm 2 := Syn.subst ![var 0, fstT (fstT (var 1)), fstT (fstT (sndT (var 1))), sndT (fstT (sndT (var 1))),
  fstT (sndT (sndT (var 1))), sndT (sndT (sndT (var 1)))] (GtC a)
def Rt : PTm 2 := Syn.subst ![var 0, fstT (fstT (var 1)), fstT (fstT (sndT (var 1))), sndT (fstT (sndT (var 1))),
  fstT (sndT (sndT (var 1))), sndT (sndT (sndT (var 1)))] (RtC a)

theorem inst2_Gt (m P : PTm n) :
    inst2 (Gt a) m P = Syn.subst ![m, fstT (fstT P), fstT (fstT (sndT P)), sndT (fstT (sndT P)), fstT (sndT (sndT P)),
      sndT (sndT (sndT P))] (GtC a) := by
  simp only [inst2, Gt, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

theorem inst2_Rt (m P : PTm n) :
    inst2 (Rt a) m P = Syn.subst ![m, fstT (fstT P), fstT (fstT (sndT P)), sndT (fstT (sndT P)), fstT (sndT (sndT P)),
      sndT (sndT (sndT P))] (RtC a) := by
  simp only [inst2, Rt, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

theorem GtC_eval (m N q b h y : PTm n) :
    Syn.subst ![m, N, q, b, h, y] (GtC a) = eqb (gcd (pw m h) q) one *
      Apre (mask a) (quo N (pw m h)) (pairT (pairT q (res (pw m h) q b)) y) := by
  ipra_ind_simp [GtC, subst_eqb, subst_ex2, subst_ap2, subst_pairT, Bezout.subst_cur]
  rfl

theorem RtC_eval (m N q b h y : PTm n) :
    Syn.subst ![m, N, q, b, h, y] (RtC a) = eqb (gcd (pw m h) q) one *
      MB a (quo N (pw m h)) q (res (pw m h) q b) h y := by
  ipra_ind_simp [RtC, subst_eqb, subst_ex2, subst_ap2, subst_pairT, Bezout.subst_cur]
  rfl

theorem proj_eqs (N q b h y : PTm n) :
    (Γ ⊢[PRAAx] fstT (fstT (Zp N h (Xp q b h y))) ≐ N) ∧ (Γ ⊢[PRAAx] fstT (fstT (sndT (Zp N h (Xp q b h y)))) ≐ q) ∧
      (Γ ⊢[PRAAx] sndT (fstT (sndT (Zp N h (Xp q b h y)))) ≐ b) ∧
      (Γ ⊢[PRAAx] fstT (sndT (sndT (Zp N h (Xp q b h y)))) ≐ h) ∧
      (Γ ⊢[PRAAx] sndT (sndT (sndT (Zp N h (Xp q b h y)))) ≐ y) :=
  ⟨(fst_pair _ _).fstE, xp_fields (snd_pair _ _)⟩

theorem Gt_at (m N q b h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (Gt a) m (Zp N h (Xp q b h y)) ≐ eqb (gcd (pw m h) q) one *
      Apre (mask a) (quo N (pw m h)) (pairT (pairT q (res (pw m h) q b)) y) := by
  rw [inst2_Gt, ← GtC_eval]
  obtain ⟨e1, e2, e3, e4, e5⟩ := proj_eqs (Γ := Γ) N q b h y
  exact Prf.eqCongr (GtC a) fun k => by
    fin_cases k
    · exact .eqRefl _
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5

theorem Rt_at (m N q b h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (Rt a) m (Zp N h (Xp q b h y)) ≐ eqb (gcd (pw m h) q) one *
      MB a (quo N (pw m h)) q (res (pw m h) q b) h y := by
  rw [inst2_Rt, ← RtC_eval]
  obtain ⟨e1, e2, e3, e4, e5⟩ := proj_eqs (Γ := Γ) N q b h y
  exact Prf.eqCongr (RtC a) fun k => by
    fin_cases k
    · exact .eqRefl _
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5

/-- `G(t) = 0` for `t > N`. -/
theorem Gt_vanish {t N q b h y : PTm n} (hh : Γ ⊢[PRAAx] le one h) (ht : Γ ⊢[PRAAx] lt N t) :
    Γ ⊢[PRAAx] inst2 (Gt a) t (Zp N h (Xp q b h y)) ≐ zero := by
  have t1 : Γ ⊢[PRAAx] le one t := by ipra_le sl ht + 𝔞 N
  have tp : Γ ⊢[PRAAx] t ≐ succ (pred t) := pos_of_one_le t1
  have hp : Γ ⊢[PRAAx] h ≐ succ (pred h) := pos_of_one_le hh
  have l1 := lt_succ_pw hp (pred t)
  have l2 : Γ ⊢[PRAAx] lt N (pw t h) :=
    le_trans ht (le_congr tp.eqSymm (congrAp2 powF (.eqRefl _) tp.eqSymm) l1)
  have hq : Γ ⊢[PRAAx] pw t h ≐ succ (pred (pw t h)) := pos_of_one_le (one_le_pw' t1 _)
  refine (Gt_at a _ _ _ _ _ _).eqTrans ?_
  exact (congrMul (.eqRefl _) ((congrAp2 _ (quo_small hq l2) (.eqRefl _)).eqTrans (sum_zero _ _))).eqTrans
    (mul_zero _)

/-- `G(1) = A_{q,b}(N)`. -/
theorem Gt_one {q b : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hb : Γ ⊢[PRAAx] lt b q) (N h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (Gt a) one (Zp N h (Xp q b h y)) ≐ Apre (mask a) N (pairT (pairT q b) y) := by
  refine (Gt_at a _ _ _ _ _ _).eqTrans ?_
  have p1 := pw_one_base (Γ := Γ) h
  have g1 := gcd_one_left (Γ := Γ) q
  have ue : Γ ⊢[PRAAx] eqb (gcd (pw one h) q) one ≐ one :=
    (congrEqb' (congrGcd p1 (.eqRefl _)) (.eqRefl _)).eqTrans (eqb_of_eq g1)
  have h1 : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := pos_of_one_le (le_refl _)
  have qe : Γ ⊢[PRAAx] quo N (pw one h) ≐ N :=
    (congrAp2 quoF (.eqRefl _) p1).eqTrans (quo_mul h1 (one_mul N).eqSymm)
  have re : Γ ⊢[PRAAx] res (pw one h) q b ≐ b :=
    (res_congr p1).eqTrans (res_unique hq g1 hb (congrAp2 remF (one_mul _) (.eqRefl _))).eqSymm
  exact (congrMul ue (congrAp2 _ qe (congrPairT (congrPairT (.eqRefl _) re) (.eqRefl _)))).eqTrans (one_mul _)

/-! ## The row terms -/

/-- For a unit `D = d^h`: `[gcd(E,q)=1] A_{q,(b_D)_E}(⌊⌊N/D⌋/E⌋) = sg(e+1) G(d(e+1))`, `E = (e+1)^h`. -/
theorem term_twist {q b d h : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (hu : Γ ⊢[PRAAx] gcd (pw d h) q ≐ one) (N e y : PTm n) :
    Γ ⊢[PRAAx] eqb (gcd (pw (succ e) h) q) one * Apre (mask a) (quo (quo N (pw d h)) (pw (succ e) h))
        (pairT (pairT q (res (pw (succ e) h) q (res (pw d h) q b))) y) ≐
      sg (succ e) * (eqb (gcd (pw (d * succ e) h) q) one * Apre (mask a) (quo N (pw (d * succ e) h))
        (pairT (pairT q (res (pw (d * succ e) h) q b)) y)) := by
  have hD : Γ ⊢[PRAAx] pw d h ≐ succ (pred (pw d h)) :=
    pos_of_one_le (one_le_pw' (le_congr (.eqRefl _) hd.eqSymm (by ipra_le 𝔞 (pred d))) _)
  have hE : Γ ⊢[PRAAx] pw (succ e) h ≐ succ (pred (pw (succ e) h)) := pw_pos1 e
  have pm : Γ ⊢[PRAAx] pw (d * succ e) h ≐ pw d h * pw (succ e) h := pw_mul_base _ _ _
  have qe : Γ ⊢[PRAAx] quo (quo N (pw d h)) (pw (succ e) h) ≐ quo N (pw (d * succ e) h) :=
    (quo_quo hD hE).eqTrans (congrAp2 quoF (.eqRefl _) pm.eqSymm)
  refine .orE (eqb_cases (Γ := Γ) (gcd (pw (succ e) h) q) one) ?_ ?_
  · let C : List (Fm PTm n) := (eqb (gcd (pw (succ e) h) q) one ≐ zero) :: Γ
    have l : C ⊢[PRAAx] eqb (gcd (pw (succ e) h) q) one * Apre (mask a) (quo (quo N (pw d h)) (pw (succ e) h))
        (pairT (pairT q (res (pw (succ e) h) q (res (pw d h) q b))) y) ≐ zero :=
      (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
    refine l.eqTrans (Prf.eqSymm ?_)
    refine .orE (eqb_cases (Γ := C) (gcd (pw (d * succ e) h) q) one) ?_ ?_
    · have z : ((eqb (gcd (pw (d * succ e) h) q) one ≐ zero) :: C) ⊢[PRAAx]
          eqb (gcd (pw (d * succ e) h) q) one ≐ zero := Prf.hyp0
      exact (congrMul (.eqRefl _) ((congrMul z (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)
    · let C' : List (Fm PTm n) := (eqb (gcd (pw (d * succ e) h) q) one ≐ one) :: C
      have g : C' ⊢[PRAAx] gcd (pw d h * pw (succ e) h) q ≐ one :=
        (congrGcd pm.wk.wk.eqSymm (.eqRefl _)).eqTrans (eq_of_eqb Prf.hyp0)
      have gE : C' ⊢[PRAAx] gcd (pw (succ e) h) q ≐ one := cop_of_mul hq.wk.wk g
      have z : C' ⊢[PRAAx] (one : PTm n) ≐ zero := (eqb_of_eq gE).eqSymm.eqTrans Prf.hyp1
      exact succ_ne_zero' _ z
  · let C : List (Fm PTm n) := (eqb (gcd (pw (succ e) h) q) one ≐ one) :: Γ
    have hE1 : C ⊢[PRAAx] gcd (pw (succ e) h) q ≐ one := eq_of_eqb Prf.hyp0
    have hDE : C ⊢[PRAAx] gcd (pw d h * pw (succ e) h) q ≐ one := cop_mul hq.wk hu.wk hE1
    have u1 : C ⊢[PRAAx] eqb (gcd (pw (d * succ e) h) q) one ≐ one :=
      eqb_of_eq ((congrGcd pm.wk (.eqRefl _)).eqTrans hDE)
    have re : C ⊢[PRAAx] res (pw (succ e) h) q (res (pw d h) q b) ≐ res (pw (d * succ e) h) q b :=
      (res_comp hq.wk hu.wk hE1).eqTrans (res_congr pm.wk.eqSymm)
    refine ((congrMul Prf.hyp0 (congrAp2 _ qe.wk (congrPairT (congrPairT (.eqRefl _) re) (.eqRefl _)))).eqTrans
      (one_mul _)).eqTrans ?_
    exact ((congrMul (sg_succ _) ((congrMul u1 (.eqRefl _)).eqTrans (one_mul _))).eqTrans (one_mul _)).eqSymm

/-- For a nonunit `D = d^h`, every multiple `m` of `d` has `G(m) = 0`. -/
theorem term_zero {q b d h : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (hu : Γ ⊢[PRAAx] eqb (gcd (pw d h) q) one ≐ zero) (m N y : PTm n) :
    Γ ⊢[PRAAx] eqb (rem m d) zero * sg m * inst2 (Gt a) m (Zp N h (Xp q b h y)) ≐ zero := by
  refine .orE (eqb_cases (Γ := Γ) (rem m d) zero) ?_ ?_
  · refine withEq Prf.hyp0 fun e => ?_
    apply deriveNat; ipra_simps; rw [e]; ring
  · let C : List (Fm PTm n) := (eqb (rem m d) zero ≐ one) :: Γ
    have em : C ⊢[PRAAx] m ≐ d * quo m d := eq_of_rem_zero hd.wk (eq_of_eqb Prf.hyp0)
    refine .orE (eqb_cases (Γ := C) (gcd (pw m h) q) one) ?_ ?_
    · let C' : List (Fm PTm n) := (eqb (gcd (pw m h) q) one ≐ zero) :: C
      have g0 : C' ⊢[PRAAx] inst2 (Gt a) m (Zp N h (Xp q b h y)) ≐ zero :=
        (Gt_at a _ _ _ _ _ _).eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))
      exact (congrMul (.eqRefl _) g0).eqTrans (mul_zero _)
    · let C' : List (Fm PTm n) := (eqb (gcd (pw m h) q) one ≐ one) :: C
      have g1 : C' ⊢[PRAAx] gcd (pw m h) q ≐ one := eq_of_eqb Prf.hyp0
      have pmh : C' ⊢[PRAAx] pw m h ≐ pw d h * pw (quo m d) h :=
        (congrAp2 powF (.eqRefl _) em.wk).eqTrans (pw_mul_base _ _ _)
      have g2 : C' ⊢[PRAAx] gcd (pw (quo m d) h * pw d h) q ≐ one :=
        (congrGcd (pmh.eqTrans (mul_comm _ _)).eqSymm (.eqRefl _)).eqTrans g1
      have g3 : C' ⊢[PRAAx] gcd (pw d h) q ≐ one := cop_of_mul hq.wk.wk g2
      have z : C' ⊢[PRAAx] (one : PTm n) ≐ zero := (eqb_of_eq g3).eqSymm.eqTrans hu.wk.wk
      exact succ_ne_zero' _ z

/-! ## The row identity -/

theorem shift_X (q b h y : PTm n) :
    Syn.shift (Xp q b h y) = Xp (Syn.shift q) (Syn.shift b) (Syn.shift h) (Syn.shift y) := by simp [Syn.shift]

/-- `R(d) = Σ_{m<N+1} [d ∣ m] sg(m) G(m)` for `d ≥ 1`. -/
theorem row_res_at {q b h d N y : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hb : Γ ⊢[PRAAx] lt b q)
    (hc : Γ ⊢[PRAAx] gcd b q ≐ one) (hh : Γ ⊢[PRAAx] le one h) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] inst2 (Rt a) d (Zp N h (Xp q b h y)) ≐
      ap2 (sumF (dmBg (Gt a))) (succ N) (pairT d (Zp N h (Xp q b h y))) := by
  refine (Rt_at a _ _ _ _ _ _).eqTrans ?_
  obtain ⟨hq', hb', hc'⟩ := hyps_shift hq hb hc
  have hh' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift h) := by simpa [Fm.shift, Syn.shift] using hh.shift
  have hd' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift d ≐ succ (pred (Syn.shift d)) := by
    simpa [Fm.shift, Syn.shift] using hd.shift
  have shP : Syn.shift (pairT d (Zp N h (Xp q b h y))) =
      pairT (Syn.shift d) (Zp (Syn.shift N) (Syn.shift h) (Xp (Syn.shift q) (Syn.shift b) (Syn.shift h) (Syn.shift y))) := by
    simp [Syn.shift]
  refine .orE (eqb_cases (Γ := Γ) (gcd (pw d h) q) one) ?_ ?_
  · -- a nonunit row: both sides vanish
    let C : List (Fm PTm n) := (eqb (gcd (pw d h) q) one ≐ zero) :: Γ
    have l : C ⊢[PRAAx] eqb (gcd (pw d h) q) one * MB a (quo N (pw d h)) q (res (pw d h) q b) h y ≐ zero :=
      (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
    refine l.eqTrans (sum_zero_of_all _ _ (.allI ?_) _).eqSymm
    rw [shP, inst2_dmBg]
    let Λ : List (Fm PTm (n + 1)) := C.map Fm.shift
    have hu' : Λ ⊢[PRAAx] eqb (gcd (pw (Syn.shift d) (Syn.shift h)) (Syn.shift q)) one ≐ zero := by
      have e := (Prf.hyp0 : C ⊢[PRAAx] _).shift
      simp only [Fm.shift, Fm.subst_eq, subst_eqb, subst_ex2, subst_ap2, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero] at e
      exact e
    have z := term_zero a (Γ := Λ) (b := Syn.shift b) hq'.wk hd'.wk hu' (var 0) (Syn.shift N) (Syn.shift y)
    refine Prf.eqTrans ?_ z
    exact congrMul (congrMul (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _)) (.eqRefl _))
      (congrInst2 (Gt a) (.eqRefl _) (snd_pair _ _))
  · -- a unit row
    let C : List (Fm PTm n) := (eqb (gcd (pw d h) q) one ≐ one) :: Γ
    have hu : C ⊢[PRAAx] gcd (pw d h) q ≐ one := eq_of_eqb Prf.hyp0
    have hbD : C ⊢[PRAAx] lt (res (pw d h) q b) q := res_lt hq.wk
    have hcD : C ⊢[PRAAx] gcd (res (pw d h) q b) q ≐ one := res_cop hq.wk hu hc.wk
    have l0 : C ⊢[PRAAx] eqb (gcd (pw d h) q) one * MB a (quo N (pw d h)) q (res (pw d h) q b) h y ≐
        MB a (quo N (pw d h)) q (res (pw d h) q b) h y := (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _)
    have l1 := masked_B a hq.wk hbD hcD hh.wk (quo N (pw d h)) y
    -- extend the twisted sum from `⌊N/D⌋` to `N`
    have hDp : C ⊢[PRAAx] pw d h ≐ succ (pred (pw d h)) :=
      pos_of_one_le (one_le_pw' (le_congr (.eqRefl _) hd.wk.eqSymm (by ipra_le 𝔞 (pred d))) _)
    have hMN : C ⊢[PRAAx] le (quo N (pw d h)) N := by
      have q := quo_lt' (N := N) hDp
      ipra_le sl q
    have l2 : C ⊢[PRAAx] tBt (tw a) (quo N (pw d h)) h (Xp q (res (pw d h) q b) h y) ≐
        ap2 (sumF (tbtB (tw a))) N (Zp (quo N (pw d h)) h (Xp q (res (pw d h) q b) h y)) := by
      refine (sum_cut (tbtB (tw a)) hMN (.allI ?_)).eqSymm
      rw [show Syn.shift (Zp (quo N (pw d h)) h (Xp q (res (pw d h) q b) h y)) =
          Zp (Syn.shift (quo N (pw d h))) (Syn.shift h) (Syn.shift (Xp q (res (pw d h) q b) h y)) by
          simp only [shift_pairT]]
      have hp' : (C.map Fm.shift) ⊢[PRAAx] Syn.shift h ≐ succ (pred (Syn.shift h)) := by
        have b : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift h ≐ succ (pred (Syn.shift h)) := pos_of_one_le hh'
        exact b.wk
      have hl : (C.map Fm.shift) ⊢[PRAAx] lt (Syn.shift (quo N (pw d h)))
          (pw (succ (Syn.shift (quo N (pw d h)) + var 0)) (Syn.shift h)) :=
        le_trans (by ipra_le 𝔞 (var 0)) (lt_succ_pw hp' _)
      exact (tbtB_at (tw a) _ _ _ _).eqTrans ((congrAp2 _ (quo_small (pw_pos1 _) hl) (.eqRefl _)).eqTrans
        (sum_zero _ _))
    -- the terms are `sg(e+1) G(d(e+1))`
    have l3 : C ⊢[PRAAx] ap2 (sumF (tbtB (tw a))) N (Zp (quo N (pw d h)) h (Xp q (res (pw d h) q b) h y)) ≐
        ap2 (sumF (shiftBody (hBg (Gt a)))) N (pairT d (Zp N h (Xp q b h y))) := by
      refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
      have sZ : Syn.shift (Zp (quo N (pw d h)) h (Xp q (res (pw d h) q b) h y)) =
          Zp (quo (Syn.shift N) (pw (Syn.shift d) (Syn.shift h))) (Syn.shift h)
            (Xp (Syn.shift q) (res (pw (Syn.shift d) (Syn.shift h)) (Syn.shift q) (Syn.shift b)) (Syn.shift h)
              (Syn.shift y)) := by
        simp only [shift_pairT, shift_res']
        simp [Syn.shift]
      rw [sZ, shP, inst2_shiftBody]
      let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift N) :: C.map Fm.shift
      have hu' : Λ ⊢[PRAAx] gcd (pw (Syn.shift d) (Syn.shift h)) (Syn.shift q) ≐ one := by
        have e := hu.shift
        simp only [Fm.shift, Fm.subst_eq, subst_ex2, subst_ap2, ConciseIPRA.PTm.subst_succ,
          ConciseIPRA.PTm.subst_zero] at e
        exact e.wk
      refine (tbtB_at (tw a) _ _ _ _).eqTrans ((tw_A a _ _ _ _ _ _).eqTrans ?_)
      refine (term_twist a (b := Syn.shift b) hq'.wk.wk hd'.wk.wk hu' (Syn.shift N) (var 0) (Syn.shift y)).eqTrans ?_
      exact (congrMul (.eqRefl _) (Gt_at a _ _ _ _ _ _).eqSymm).eqTrans (hBg_at (Gt a) _ _ _).eqSymm
    -- reindex by the multiples of `d`
    have hz : (Δ : List (Fm PTm (n + 1))) → (t : PTm (n + 1)) → C.map Fm.shift ⊆ Δ →
        (Δ ⊢[PRAAx] lt (Syn.shift N) t) →
        (Δ ⊢[PRAAx] inst2 (Gt a) t (Zp (Syn.shift N) (Syn.shift h) (Syn.shift (Xp q b h y))) ≐ zero) := by
      intro Δ t s ht
      rw [shift_X]
      have hh'' : Δ ⊢[PRAAx] le one (Syn.shift h) :=
        hh'.weaken (fun _ hx => s (List.mem_cons_of_mem _ hx))
      exact Gt_vanish a hh'' ht
    have l4 : C ⊢[PRAAx] ap2 (sumF (shiftBody (hBg (Gt a)))) N (pairT d (Zp N h (Xp q b h y))) ≐
        ap2 (sumF (dmBg (Gt a))) (succ N) (pairT d (Zp N h (Xp q b h y))) :=
      multiples_g (Gt a) hd.wk hz
    exact l0.eqTrans (l1.eqTrans (l2.eqTrans (l3.eqTrans l4)))

/-- The row identity as the schema `RowHyp` of `PowerAbstractInversion`. -/
theorem row_res {Θ : List (Fm PTm n)} {q b h : PTm n} (hq : Θ ⊢[PRAAx] le two q) (hb : Θ ⊢[PRAAx] lt b q)
    (hc : Θ ⊢[PRAAx] gcd b q ≐ one) (hh : Θ ⊢[PRAAx] le one h) (N y : PTm n) :
    RowHyp (Gt a) (Rt a) Θ N h (Xp q b h y) := fun Δ d s hd =>
  row_res_at a (hq.weaken s) (hb.weaken s) (hc.weaken s) (hh.weaken s) hd

/-! ## The inversion -/

/-- `Σ_{d≤N} μ⁺(d) R(d) = Σ_{d≤N} μ⁻(d) R(d) + A_{q,b}(N)`, i.e.
`A_{q,b}(N) = Σ_{d≤N} μ(d) [gcd(d^h,q)=1] B_{h;q,b_{d^h}}(⌊N/d^h⌋)`. -/
theorem inversion_res {q b h : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hb : Γ ⊢[PRAAx] lt b q)
    (hc : Γ ⊢[PRAAx] gcd b q ≐ one) (hh : Γ ⊢[PRAAx] le one h) (N y : PTm n) :
    Γ ⊢[PRAAx] RSg (Rt a) wP N h (Xp q b h y) ≐
      RSg (Rt a) wN N h (Xp q b h y) + Apre (mask a) N (pairT (pairT q b) y) := by
  obtain ⟨hq', hb', hc'⟩ := hyps_shift hq hb hc
  have hh' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift h) := by simpa [Fm.shift, Syn.shift] using hh.shift
  have hrow : RowHyp (Gt a) (Rt a) (Γ.map Fm.shift) (Syn.shift N) (Syn.shift h) (Syn.shift (Xp q b h y)) := by
    rw [shift_X]; exact row_res a hq' hb' hc' hh' _ _
  refine inversion_g (Gt a) (Rt a) hrow (Gt_one a hq hb N h y) ?_
  have hz : (le N zero :: Γ) ⊢[PRAAx] N ≐ zero := (monus_zero N).eqSymm.eqTrans Prf.hyp0
  exact (congrAp2 _ hz (.eqRefl _)).eqTrans (sum_zero _ _)

end LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueInversion
