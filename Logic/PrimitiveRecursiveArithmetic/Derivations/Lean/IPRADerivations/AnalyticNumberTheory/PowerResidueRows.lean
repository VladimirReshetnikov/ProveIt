import IPRADerivations.AnalyticNumberTheory.PowerResidue
import IPRADerivations.AnalyticNumberTheory.PowerTwistPrefix
import IPRADerivations.Probability.Lotus
import IPRADerivations.Combinatorics.Binomial
import IPRADerivations.Core.Header

/-!
# Progression rows along perfect powers (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, proof of Theorem
`thm:powerdivisor`: "For residues, a summand `d^h m ≡ b (mod q)` with reduced `b` forces `(d,q) = 1`. For such `d`, find
the unique representative `b_d` with `d^h b_d ≡ b (mod q)` … The forward formula now uses `A_{q,b_d}` at its `d`th term
and skips the nonunits."

For a modulus `q ≥ 2` and a reduced residue `b < q`:

* `mask a`: the progression body `[m ≡ b (mod q)] a(m, y)` at the parameter `⟨⟨q, b⟩, y⟩`, so that
  `A_{q,b}(N) = Apre (mask a) N ⟨⟨q, b⟩, y⟩` (`mask_at`);
* `bvB a`: `b_h(m) = Σ_{j<m} [(j+1)^h ∣ m] a(m/(j+1)^h)` as a body at `⟨h, y⟩`, so that the progression row of `b_h` is
  `B_{h;q,b}(N) = Apre (mask (bvB a)) N ⟨⟨q, b⟩, ⟨h, y⟩⟩` (`MB`);
* `tw a`: the divisor-twisted body `[gcd(D, q) = 1] [m ≡ b_D] a(m, y)` with `D = (j+1)^h` at `⟨j, ⟨⟨q, b⟩, ⟨h, y⟩⟩⟩`
  (`tw_at`), and `tw_A`: its prefix is `[gcd(D, q) = 1] · A_{q,b_D}(M)`;
* `term_core`: `[n ≡ b][D ∣ n] = [D ∣ n][gcd(D, q) = 1][n/D ≡ b_D]` (`PowerResidue.ind_transport` at `n = D (n/D)`);
* `masked_B`: `B_{h;q,b}(N) = Σ_{j<N} [gcd((j+1)^h, q) = 1] A_{q,b_{(j+1)^h}}(⌊N/(j+1)^h⌋)` in the twisted form
  `PowerTwistPrefix.tBt (tw a)`, by `term_core` under the two sums and `PowerTwistPrefix.twist_prefix`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueRows

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorPrefix (Apre cB bval cB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerTwistPrefix (tBt tBpre tbval tcB tbpB tcB_at tbpB_at twist_prefix)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidue (res inv ind_transport)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (rem_small)
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open LeanProofs.IPRA.Combinatorics.Binomial (eq_of_rem_zero)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockChain (one_le_pw')
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (a : PTm 2)

/-! ## The progression body -/

/-- `[m ≡ b] a(m, z)` over `0 = m`, `1 = q`, `2 = b`, `3 = z`. -/
def maskC : PTm 4 := eqb (rem (var 0) (var 1)) (var 2) * Syn.subst ![var 0, var 3] a

/-- The progression body at `⟨⟨q, b⟩, z⟩`. -/
def mask : PTm 2 := Syn.subst ![var 0, fstT (fstT (var 1)), sndT (fstT (var 1)), sndT (var 1)] (maskC a)

theorem inst2_mask (m P : PTm n) :
    inst2 (mask a) m P = Syn.subst ![m, fstT (fstT P), sndT (fstT P), sndT P] (maskC a) := by
  simp only [inst2, mask, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

theorem maskC_eval (m q b z : PTm n) :
    Syn.subst ![m, q, b, z] (maskC a) = eqb (rem m q) b * inst2 a m z := by
  simp only [maskC, PTm.subst_mul, subst_eqb, subst_ap2, Syn.subst_var, inst2, Syn.subst_subst]
  refine congrArg _ ?_
  congr 1; funext k; fin_cases k <;> rfl

theorem mask_at (m q b z : PTm n) :
    Γ ⊢[PRAAx] inst2 (mask a) m (pairT (pairT q b) z) ≐ eqb (rem m q) b * inst2 a m z := by
  rw [inst2_mask, ← maskC_eval]
  have e1 : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT q b) z)) ≐ q := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have e2 : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT q b) z)) ≐ b := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  have e3 : Γ ⊢[PRAAx] sndT (pairT (pairT q b) z) ≐ z := snd_pair _ _
  exact Prf.eqCongr (maskC a) fun k => by
    fin_cases k
    · exact .eqRefl _
    · exact e1
    · exact e2
    · exact e3

/-! ## `b_h` as a body -/

/-- `b_h(m)` over `0 = m`, `1 = ⟨h, y⟩`. -/
def bvB : PTm 2 := ap2 (sumF (cB a)) (var 0) (pairT (pairT (var 0) (fstT (var 1))) (sndT (var 1)))

theorem bvB_at (m h y : PTm n) : Γ ⊢[PRAAx] inst2 (bvB a) m (pairT h y) ≐ bval a m h y := by
  have e : inst2 (bvB a) m (pairT h y) =
      ap2 (sumF (cB a)) m (pairT (pairT m (fstT (pairT h y))) (sndT (pairT h y))) := by simp [inst2, bvB]
  rw [e]
  exact congrAp2 _ (.eqRefl _) (congrPairT (congrPairT (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))

/-- The parameter `⟨⟨q, b⟩, ⟨h, y⟩⟩` of the `B` row. -/
abbrev Xp (q b h y : PTm n) : PTm n := pairT (pairT q b) (pairT h y)

/-- `B_{h;q,b}(N) = Σ_{m ≤ N, m ≡ b} b_h(m)`. -/
abbrev MB (N q b h y : PTm n) : PTm n := Apre (mask (bvB a)) N (Xp q b h y)

/-! ## The twisted body -/

/-- `[gcd(D, q) = 1] [m ≡ b_D] a(m, y)` with `D = (j+1)^h`, over `0 = m`, `1 = j`, `2 = q`, `3 = b`, `4 = h`, `5 = y`. -/
def twC : PTm 6 :=
  eqb (gcd (pw (succ (var 1)) (var 4)) (var 2)) one *
    (eqb (rem (var 0) (var 2)) (res (pw (succ (var 1)) (var 4)) (var 2) (var 3)) * Syn.subst ![var 0, var 5] a)

/-- The twisted body at `⟨j, ⟨⟨q, b⟩, ⟨h, y⟩⟩⟩`. -/
def tw : PTm 2 := Syn.subst ![var 0, fstT (var 1), fstT (fstT (sndT (var 1))), sndT (fstT (sndT (var 1))),
  fstT (sndT (sndT (var 1))), sndT (sndT (sndT (var 1)))] (twC a)

theorem inst2_tw (m P : PTm n) :
    inst2 (tw a) m P = Syn.subst ![m, fstT P, fstT (fstT (sndT P)), sndT (fstT (sndT P)), fstT (sndT (sndT P)),
      sndT (sndT (sndT P))] (twC a) := by
  simp only [inst2, tw, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

theorem twC_eval (m j q b h y : PTm n) :
    Syn.subst ![m, j, q, b, h, y] (twC a) = eqb (gcd (pw (succ j) h) q) one *
      (eqb (rem m q) (res (pw (succ j) h) q b) * inst2 a m y) := by
  simp only [twC, PTm.subst_mul, PTm.subst_add, PTm.subst_monus, LeanProofs.IPRA.PTm.subst_pred, subst_eqb,
    subst_ex2, subst_ap2, Bezout.subst_cur, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
    inst2, Syn.subst_subst]
  refine congrArg _ (congrArg _ ?_)
  congr 1; funext k; fin_cases k <;> rfl

theorem tw_at (m j q b h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (tw a) m (pairT j (Xp q b h y)) ≐ eqb (gcd (pw (succ j) h) q) one *
      (eqb (rem m q) (res (pw (succ j) h) q b) * inst2 a m y) := by
  rw [inst2_tw, ← twC_eval]
  have e1 : Γ ⊢[PRAAx] fstT (pairT j (Xp q b h y)) ≐ j := fst_pair _ _
  have e2 : Γ ⊢[PRAAx] fstT (fstT (sndT (pairT j (Xp q b h y)))) ≐ q :=
    (congrFst ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))).eqTrans (fst_pair _ _)
  have e3 : Γ ⊢[PRAAx] sndT (fstT (sndT (pairT j (Xp q b h y)))) ≐ b :=
    (congrSnd ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))).eqTrans (snd_pair _ _)
  have e4 : Γ ⊢[PRAAx] fstT (sndT (sndT (pairT j (Xp q b h y)))) ≐ h :=
    (congrFst ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
  have e5 : Γ ⊢[PRAAx] sndT (sndT (sndT (pairT j (Xp q b h y)))) ≐ y :=
    (congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
  exact Prf.eqCongr (twC a) fun k => by
    fin_cases k
    · exact .eqRefl _
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5

theorem shift_res (j h q b : PTm n) :
    Syn.shift (res (pw (succ j) h) q b) = res (pw (succ (Syn.shift j)) (Syn.shift h)) (Syn.shift q) (Syn.shift b) := by
  simp only [Syn.shift, PTm.subst_mul, PTm.subst_add, PTm.subst_monus, LeanProofs.IPRA.PTm.subst_pred, subst_eqb, subst_ex2, subst_ap2, Bezout.subst_cur, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

theorem shift_unit (j h q : PTm n) :
    Syn.shift (eqb (gcd (pw (succ j) h) q) one) = eqb (gcd (pw (succ (Syn.shift j)) (Syn.shift h)) (Syn.shift q)) one := by
  simp only [Syn.shift, PTm.subst_mul, PTm.subst_add, PTm.subst_monus, LeanProofs.IPRA.PTm.subst_pred, subst_eqb, subst_ex2, subst_ap2, Bezout.subst_cur, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-- The twisted prefix: `A_tw(M, ⟨j, X⟩) = [gcd(D, q) = 1] · A_{q,b_D}(M)`, `D = (j+1)^h`. -/
theorem tw_A (M j q b h y : PTm n) :
    Γ ⊢[PRAAx] Apre (tw a) M (pairT j (Xp q b h y)) ≐ eqb (gcd (pw (succ j) h) q) one *
      Apre (mask a) M (pairT (pairT q (res (pw (succ j) h) q b)) y) := by
  refine (sum_congr_bounded (shiftBody (tw a)) (cmB (shiftBody (mask a))) _
    (pairT (eqb (gcd (pw (succ j) h) q) one) (pairT (pairT q (res (pw (succ j) h) q b)) y)) M
    (.allI (.impI ?_))).eqTrans (sum_const_mul _ _ _ _)
  rw [inst2_shiftBody, inst2_cmB, inst2_shiftBody]
  simp only [shift_pairT, shift_res, shift_unit]
  refine (tw_at a _ _ _ _ _ _).eqTrans ?_
  exact congrMul (fst_pair _ _).eqSymm ((mask_at a _ _ _ _).eqSymm.eqTrans
    (congrInst2 (mask a) (.eqRefl _) (snd_pair _ _).eqSymm))

/-! ## The pointwise transport -/

/-- `[n ≡ b][D ∣ n] A = [D ∣ n][gcd(D, q) = 1][n/D ≡ b_D] A` for `q ≥ 2`, `b < q` reduced, `D ≥ 1`. -/
theorem term_core {q b m D A : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hb : Γ ⊢[PRAAx] lt b q)
    (hc : Γ ⊢[PRAAx] gcd b q ≐ one) (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) :
    Γ ⊢[PRAAx] eqb (rem m q) b * (eqb (rem m D) zero * A) ≐
      eqb (rem m D) zero * (eqb (gcd D q) one * (eqb (rem (quo m D) q) (res D q b) * A)) := by
  refine .orE (eqb_cases (Γ := Γ) (rem m D) zero) ?_ ?_
  · refine withEq Prf.hyp0 fun e => ?_
    apply deriveNat; ipra_simps; rw [e]; ring
  · let C : List (Fm PTm n) := (eqb (rem m D) zero ≐ one) :: Γ
    have e1 : C ⊢[PRAAx] eqb (rem m D) zero ≐ one := Prf.hyp0
    have em : C ⊢[PRAAx] m ≐ D * quo m D := eq_of_rem_zero hD.wk (eq_of_eqb e1)
    have k : C ⊢[PRAAx] eqb (rem m q) b ≐ eqb (gcd D q) one * eqb (rem (quo m D) q) (res D q b) :=
      (congrEqb' (congrAp2 remF em (.eqRefl _)) (rem_small hq.wk hb.wk).eqSymm).eqTrans (ind_transport hq.wk hc.wk)
    refine withEq e1 fun f1 => withEq k fun f2 => ?_
    apply deriveNat; ipra_simps; rw [f1, f2]; ring

/-! ## The progression row of `b_h` -/

theorem hyps_shift {q b : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hb : Γ ⊢[PRAAx] lt b q)
    (hc : Γ ⊢[PRAAx] gcd b q ≐ one) :
    (Γ.map Fm.shift ⊢[PRAAx] le two (Syn.shift q)) ∧ (Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift b) (Syn.shift q)) ∧
      (Γ.map Fm.shift ⊢[PRAAx] gcd (Syn.shift b) (Syn.shift q) ≐ one) := by
  refine ⟨?_, ?_, ?_⟩
  · have e := hq.shift
    simp only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e
    exact e
  · have e := hb.shift
    simp only [Fm.shift, lt, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e
    exact e
  · have e := hc.shift
    simp only [Fm.shift, Fm.subst_eq, subst_ex2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e
    exact e

/-- `[n ≡ b] b_h(n) = Σ_{j<n} [(j+1)^h ∣ n] tw(n/(j+1)^h, ⟨j, X⟩)`. -/
theorem bval_eq {q b h : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hb : Γ ⊢[PRAAx] lt b q)
    (hc : Γ ⊢[PRAAx] gcd b q ≐ one) (m y : PTm n) :
    Γ ⊢[PRAAx] eqb (rem m q) b * bval a m h y ≐ tbval (tw a) m h (Xp q b h y) := by
  refine (sum_const_mul (cB a) m _ _).eqSymm.eqTrans ?_
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_cmB]
  simp only [shift_pairT]
  obtain ⟨hq', hb', hc'⟩ := hyps_shift hq hb hc
  let Δ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have hD : Δ ⊢[PRAAx] pw (succ (var 0)) (Syn.shift h) ≐ succ (pred (pw (succ (var 0)) (Syn.shift h))) :=
    pos_of_one_le (one_le_pw' (by ipra_le 𝔞 (var 0)) _)
  have l : Δ ⊢[PRAAx] fstT (pairT (Syn.shift (eqb (rem m q) b)) (pairT (pairT (Syn.shift m) (Syn.shift h)) (Syn.shift y))) *
      inst2 (cB a) (var 0) (sndT (pairT (Syn.shift (eqb (rem m q) b))
        (pairT (pairT (Syn.shift m) (Syn.shift h)) (Syn.shift y)))) ≐
      eqb (rem (Syn.shift m) (Syn.shift q)) (Syn.shift b) *
        (eqb (rem (Syn.shift m) (pw (succ (var 0)) (Syn.shift h))) zero *
          inst2 a (quo (Syn.shift m) (pw (succ (var 0)) (Syn.shift h))) (Syn.shift y)) := by
    have s : Syn.shift (eqb (rem m q) b) = eqb (rem (Syn.shift m) (Syn.shift q)) (Syn.shift b) := by simp [Syn.shift]
    rw [s]
    exact congrMul (fst_pair _ _) ((congrInst2 (cB a) (.eqRefl _) (snd_pair _ _)).eqTrans (cB_at a _ _ _ _))
  refine l.eqTrans ((term_core hq'.wk hb'.wk hc'.wk hD).eqTrans ?_)
  refine (congrMul (.eqRefl _) (tw_at a _ _ _ _ _ _).eqSymm).eqTrans ?_
  exact (tcB_at (tw a) _ _ _ _).eqSymm

/-- `B_{h;q,b}(N) = Σ_{j<N} [gcd((j+1)^h, q) = 1] A_{q,b_{(j+1)^h}}(⌊N/(j+1)^h⌋)` (twisted form). -/
theorem masked_B {q b h : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hb : Γ ⊢[PRAAx] lt b q)
    (hc : Γ ⊢[PRAAx] gcd b q ≐ one) (hh : Γ ⊢[PRAAx] le one h) (N y : PTm n) :
    Γ ⊢[PRAAx] MB a N q b h y ≐ tBt (tw a) N h (Xp q b h y) := by
  refine Prf.eqTrans ?_ (twist_prefix (tw a) hh N (Xp q b h y)).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_shiftBody]
  simp only [shift_pairT]
  obtain ⟨hq', hb', hc'⟩ := hyps_shift hq hb hc
  refine (mask_at (bvB a) _ _ _ _).eqTrans ?_
  refine (congrMul (.eqRefl _) (bvB_at a _ _ _)).eqTrans ?_
  refine (bval_eq a hq'.wk hb'.wk hc'.wk _ _).eqTrans ?_
  exact (tbpB_at (tw a) _ _ _).eqSymm

end LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueRows
