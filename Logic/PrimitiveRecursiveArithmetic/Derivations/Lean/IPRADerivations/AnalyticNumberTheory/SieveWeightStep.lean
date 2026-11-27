import IPRADerivations.AnalyticNumberTheory.SieveWeightPrime

/-!
# One prime step of the weight bound

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:weight-bound`:
"`G ≥ Σ_{e ∣ d} (1/φ(e)) G_{dq}(z/d) = (d/φ(d)) G_{dq}(z/d)`. Together with `eq:weight-formula`, this gives
`|λ_d| ≤ 1`".

In the cleared normalization, with `|Y_r| = Y⁺_r + Y⁻_r` (`hv`) and `W_D = Σ_{r ≤ z} [r ≥ 1] [D ∣ r] |Y_r|`
(the sum of `SieveDiagonal.Ab habs`), `|λ_D| ≤ 1` is `D · W_D ≤ W_1`. The paper proves it by an injection
`(e, s) ↦ es` over all divisors `e` of `d` at once. Here it is split into steps of one prime:

  `p · W_{Dp} ≤ W_D`   for a prime `p`, `D ≥ 1` and `q ≥ 1`                             (`prime_step`).

The multiples `r = kp` of `Dp` are multiples of `D`, and so are their quotients `k`; `|Y_{kp}| = 0` when `p ∣ k`
and `(p − 1) |Y_{kp}| ≤ |Y_k|` when `p ∤ k` (`SieveWeightPrime`). So

  `p Σ_r [Dp ∣ r] |Y_r| ≤ Σ_r [p ∣ r] [D ∣ r] |Y_r| + Σ_r [p ∣ r] ([p ∤ k] [D ∣ k] |Y_k|)_{k = r/p}`      (`main_pt`),

the second sum is at most `Σ_k [p ∤ k] [D ∣ k] |Y_k|` by the reindexing of the multiples of `p`
(`SumReindex.reindex_le`), and the two sums together are `W_D`.

* `Ab_h`: the summand of `W_D`;
* `core_alg`, `good_alg`, `chain`, `split_alg`: the certificates over opaque terms;
* `pt_le`, `split_pt`: the summand inequality and the split by `[p ∣ r]`, for the bodies.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightStep

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg zero_mul_l congrEqb' inst2_mulB eqb_split shift_mul')
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (riB inst2_riB reindex_le)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveDiagonal (Ab Ab_at)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightValues (YP YN)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightPrime (Y_kill abs_step)
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The summand -/

/-- `|Y_r| = Y⁺_r + Y⁻_r` as a body. -/
abbrev habs : PTm 2 := addBody YP YN

/-- `|Y_r|`. -/
abbrev hv (r P : PTm n) : PTm n := inst2 YP r P + inst2 YN r P

/-- The summand of `W_D`: `[r ≥ 1] [D ∣ r] |Y_r|`. -/
theorem Ab_h (r D P : PTm n) :
    Γ ⊢[PRAAx] inst2 (Ab habs) r (pairT D P) ≐ (sg r * eqb (rem r D) zero) * hv r P := by
  have h := Ab_at (Γ := Γ) habs r D P
  rw [inst2_addBody] at h
  exact h

/-! ## Certificates over opaque terms -/

alias zero_le_of := Common.le_of_eq_zero

theorem core_alg {p pm hr hk : PTm n} (xp : Γ ⊢[PRAAx] p ≐ one + pm) (S : Γ ⊢[PRAAx] le (pm * hr) hk) :
    Γ ⊢[PRAAx] le (p * ((one * one) * hr)) (one * ((one * one) * hr) + one * (one * ((one * one) * hk))) := by
  have x := natEq xp
  ipra_le sl S with 𝔞 hr * x

/-- The summand inequality when every indicator is `1`. -/
theorem good_alg {p pm sr eDp hr ep eD cp sk eDk hk : PTm n} (h1 : Γ ⊢[PRAAx] ep ≐ one)
    (h2 : Γ ⊢[PRAAx] sr ≐ one) (h3 : Γ ⊢[PRAAx] eD ≐ one) (h4 : Γ ⊢[PRAAx] cp ≐ one)
    (h5 : Γ ⊢[PRAAx] sk ≐ one) (h6 : Γ ⊢[PRAAx] eDk ≐ one) (h7 : Γ ⊢[PRAAx] eDp ≐ one)
    (xp : Γ ⊢[PRAAx] p ≐ one + pm) (S : Γ ⊢[PRAAx] le (pm * hr) hk) :
    Γ ⊢[PRAAx] le (p * ((sr * eDp) * hr)) (ep * ((sr * eD) * hr) + ep * (cp * ((sk * eDk) * hk))) :=
  le_congr (congrMul (.eqRefl _) (congrMul (congrMul h2 h7) (.eqRefl _))).eqSymm
    (congrAdd (congrMul h1 (congrMul (congrMul h2 h3) (.eqRefl _)))
      (congrMul h1 (congrMul h4 (congrMul (congrMul h5 h6) (.eqRefl _))))).eqSymm (core_alg xp S)

theorem chain {L F M G R H T : PTm n} (e1 : Γ ⊢[PRAAx] L ≐ F) (l2 : Γ ⊢[PRAAx] le F M)
    (e3 : Γ ⊢[PRAAx] M ≐ G + R) (l4 : Γ ⊢[PRAAx] le R H) (e5 : Γ ⊢[PRAAx] G + H ≐ T) : Γ ⊢[PRAAx] le L T := by
  have x1 := natEq e1; have x3 := natEq e3; have x5 := natEq e5
  ipra_le sl l2 + sl l4 with -x5 - x3 - x1

theorem split_alg {e ne T : PTm n} (h : Γ ⊢[PRAAx] ne + e ≐ one) : Γ ⊢[PRAAx] e * T + ne * T ≐ T := by
  ipra_lc 𝔞 T * natEq h

/-! ## The summand inequality -/

/-- `p [r ≥ 1] [Dp ∣ r] |Y_r| ≤ [p ∣ r] [r ≥ 1] [D ∣ r] |Y_r| + [p ∣ r] [p ∤ k] [k ≥ 1] [D ∣ k] |Y_k|` with
`k = r / p`, for `r ≤ z`. -/
theorem main_pt {p D r P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) (hp : Γ ⊢[PRAAx] prime p)
    (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) (hr : Γ ⊢[PRAAx] lt r (succ (sndT (sndT P)))) :
    Γ ⊢[PRAAx] le (p * ((sg r * eqb (rem r (D * p)) zero) * hv r P))
      (eqb (rem r p) zero * ((sg r * eqb (rem r D) zero) * hv r P) +
        eqb (rem r p) zero * (monus one (eqb (rem (quo r p) p) zero) *
          ((sg (quo r p) * eqb (rem (quo r p) D) zero) * hv (quo r p) P))) := by
  have hp2 := prime_two hp
  have hp1 := p_pos hp2
  have hDp : Γ ⊢[PRAAx] D * p ≐ succ (pred (D * p)) := Combinatorics.LegendreDigits.pos_mul' hD hp1
  have hrz : Γ ⊢[PRAAx] le r (sndT (sndT P)) := (succ_monus_succ _ _).eqSymm.eqTrans hr
  refine .orE (zero_or_succ r) ?_ ?_
  · have s0 : ((r ≐ zero) :: Γ) ⊢[PRAAx] sg r ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact zero_le_of ((congrMul (.eqRefl _) (zero_mul_l (zero_mul_l s0 _) _)).eqTrans (mul_zero _))
  · refine .orE (eq_or_ne (rem r (D * p)) zero) ?_ ?_
    · let C : List (Fm PTm n) := (rem r (D * p) ≐ zero) :: (r ≐ succ (pred r)) :: Γ
      have hr1 : C ⊢[PRAAx] r ≐ succ (pred r) := Prf.hyp1
      have hdv : C ⊢[PRAAx] rem r (D * p) ≐ zero := Prf.hyp0
      have hp1' : C ⊢[PRAAx] p ≐ succ (pred p) := hp1.wk.wk
      have hD' : C ⊢[PRAAx] D ≐ succ (pred D) := hD.wk.wk
      have e0 : C ⊢[PRAAx] r ≐ (D * p) * quo r (D * p) := eq_of_dvd' hDp.wk.wk hdv
      have eK : C ⊢[PRAAx] r ≐ p * (D * quo r (D * p)) + zero := by
        ipra_lc natEq e0
      have eDr : C ⊢[PRAAx] r ≐ D * (p * quo r (D * p)) + zero := by
        ipra_lc natEq e0
      have hrp : C ⊢[PRAAx] rem r p ≐ zero := rem_eq' hp1' eK (zero_lt' hp1')
      have hK : C ⊢[PRAAx] quo r p ≐ D * quo r (D * p) := quo_eq hp1' eK (zero_lt' hp1')
      have hrD : C ⊢[PRAAx] rem r D ≐ zero := rem_eq' hD' eDr (zero_lt' hD')
      have hKD : C ⊢[PRAAx] rem (quo r p) D ≐ zero :=
        (congrAp2 remF hK (.eqRefl _)).eqTrans
          (rem_eq' hD' (q := quo r (D * p)) (r := zero) (add_zero _).eqSymm (zero_lt' hD'))
      have eRK : C ⊢[PRAAx] r ≐ quo r p * p := by
        ipra_lc natEq e0 - 𝔞 p * natEq hK
      have hKpos : C ⊢[PRAAx] quo r p ≐ succ (pred (quo r p)) := by
        refine .orE (zero_or_succ (quo r p)) ?_ Prf.hyp0
        have z : ((quo r p ≐ zero) :: C) ⊢[PRAAx] r ≐ zero :=
          eRK.wk.eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))
        exact succ_ne_zero' _ (hr1.wk.eqSymm.eqTrans z)
      have hz' : C ⊢[PRAAx] le (quo r p * p) (sndT (sndT P)) := le_congr eRK (.eqRefl _) hrz.wk.wk
      have ehv : C ⊢[PRAAx] hv r P ≐ hv (quo r p * p) P :=
        congrAdd (congrInst2 YP eRK (.eqRefl _)) (congrInst2 YN eRK (.eqRefl _))
      refine .orE (eq_or_ne (rem (quo r p) p) zero) ?_ ?_
      · have kl := Y_kill (Γ := (rem (quo r p) p ≐ zero) :: C) P hp.wk.wk.wk hKpos.wk Prf.hyp0
        have hz0 : ((rem (quo r p) p ≐ zero) :: C) ⊢[PRAAx] hv r P ≐ zero :=
          ehv.wk.eqTrans ((congrAdd (Prf.andE₁ kl) (Prf.andE₂ kl)).eqTrans (add_zero _))
        exact zero_le_of ((congrMul (.eqRefl _) ((congrMul (.eqRefl _) hz0).eqTrans (mul_zero _))).eqTrans
          (mul_zero _))
      · let E : List (Fm PTm n) := neg (rem (quo r p) p ≐ zero) :: C
        have hne : E ⊢[PRAAx] neg (rem (quo r p) p ≐ zero) := Prf.hyp0
        have cp1 := Common.eqb_compl_one_of_ne hne
        have xp : E ⊢[PRAAx] p ≐ one + monus p one := eq_add_of_le (le_trans (le_succ_self _) hp2.wk.wk.wk)
        have S0 := abs_step (Γ := E) hq.wk.wk.wk hp.wk.wk.wk hKpos.wk hne hz'.wk
        have S : E ⊢[PRAAx] le (monus p one * hv r P) (hv (quo r p) P) :=
          le_congr (congrMul (.eqRefl _) ehv.wk.eqSymm) (.eqRefl _) S0
        exact good_alg (eqb_of_eq hrp.wk) (sg_pos hr1.wk) (eqb_of_eq hrD.wk) cp1 (sg_pos hKpos.wk)
          (eqb_of_eq hKD.wk) (eqb_of_eq hdv.wk) xp S
    · have e0 : (neg (rem r (D * p) ≐ zero) :: (r ≐ succ (pred r)) :: Γ) ⊢[PRAAx]
          eqb (rem r (D * p)) zero ≐ zero := eqb_of_ne Prf.hyp0
      exact zero_le_of ((congrMul (.eqRefl _)
        (zero_mul_l ((congrMul (.eqRefl _) e0).eqTrans (mul_zero _)) _)).eqTrans (mul_zero _))

/-! ## The bodies -/

/-- `[fst x ∣ r]` over `0 = r`, `1 = x`. -/
abbrev eB : PTm 2 := eqb (rem (var 0) (fstT (var 1))) zero
/-- `[fst x ∤ r]`. -/
abbrev neB : PTm 2 := monus one eB

theorem inst2_eB (r x : PTm n) : inst2 eB r x = eqb (rem r (fstT x)) zero := by simp [inst2]
theorem inst2_neB (r x : PTm n) : inst2 neB r x = monus one (eqb (rem r (fstT x)) zero) := by simp [inst2]

/-- `[p ∣ r]` times the summand of `W_D`, over `0 = r`, `1 = ⟨p, ⟨D, P⟩⟩`. -/
def g1B : PTm 2 := eB * sndB (Ab habs)
/-- `[p ∤ r]` times the summand of `W_D`. -/
def hB : PTm 2 := neB * sndB (Ab habs)

theorem g1_at (r p D P : PTm n) :
    Γ ⊢[PRAAx] inst2 g1B r (pairT p (pairT D P)) ≐
      eqb (rem r p) zero * ((sg r * eqb (rem r D) zero) * hv r P) := by
  rw [g1B, inst2_mulB, inst2_eB, inst2_sndB]
  exact congrMul (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _))
    ((congrInst2 _ (.eqRefl _) (snd_pair _ _)).eqTrans (Ab_h r D P))

theorem h_at (r p D P : PTm n) :
    Γ ⊢[PRAAx] inst2 hB r (pairT p (pairT D P)) ≐
      monus one (eqb (rem r p) zero) * ((sg r * eqb (rem r D) zero) * hv r P) := by
  rw [hB, inst2_mulB, inst2_neB, inst2_sndB]
  exact congrMul (congrMonus (.eqRefl _) (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _)))
    ((congrInst2 _ (.eqRefl _) (snd_pair _ _)).eqTrans (Ab_h r D P))

theorem cm_at (r p D P : PTm n) :
    Γ ⊢[PRAAx] inst2 (cmB (Ab habs)) r (pairT p (pairT D P)) ≐ p * ((sg r * eqb (rem r D) zero) * hv r P) := by
  rw [inst2_cmB]
  exact congrMul (fst_pair _ _) ((congrInst2 _ (.eqRefl _) (snd_pair _ _)).eqTrans (Ab_h r D P))

theorem ri_at (r p x : PTm n) :
    Γ ⊢[PRAAx] inst2 (riB hB) r (pairT p x) ≐ eqb (rem r p) zero * inst2 hB (quo r p) x := by
  rw [inst2_riB]
  exact congrMul (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _))
    (congrInst2 hB (congrAp2 quoF (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))

/-- The summand inequality for the bodies. -/
theorem pt_le {p D r P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) (hp : Γ ⊢[PRAAx] prime p)
    (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) (hr : Γ ⊢[PRAAx] lt r (succ (sndT (sndT P)))) :
    Γ ⊢[PRAAx] le (inst2 (cmB (Ab habs)) r (pairT p (pairT (D * p) P)))
      (inst2 (mixB g1B (riB hB)) r (pairT (pairT p (pairT D P)) (pairT p (pairT p (pairT D P))))) :=
  le_congr (cm_at r p (D * p) P).eqSymm
    ((mix_at g1B (riB hB) r _ _).eqTrans (congrAdd (g1_at r p D P)
      ((ri_at r p _).eqTrans (congrMul (.eqRefl _) (h_at (quo r p) p D P))))).eqSymm (main_pt hq hp hD hr)

/-- The split by `[p ∣ r]`. -/
theorem split_pt (r p D P : PTm n) :
    Γ ⊢[PRAAx] inst2 (addBody g1B hB) r (pairT p (pairT D P)) ≐ inst2 (Ab habs) r (pairT D P) := by
  rw [inst2_addBody, g1B, hB, inst2_mulB, inst2_mulB, inst2_eB, inst2_neB, inst2_sndB]
  exact (split_alg (eqb_split _ _)).eqTrans (congrInst2 _ (.eqRefl _) (snd_pair _ _))

/-! ## The prime step -/

/-- `p · W_{Dp} ≤ W_D` for a prime `p`, `D ≥ 1` and `q ≥ 1`. -/
theorem prime_step {p D P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) (hp : Γ ⊢[PRAAx] prime p)
    (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) :
    Γ ⊢[PRAAx] le (p * ap2 (sumF (Ab habs)) (succ (sndT (sndT P))) (pairT (D * p) P))
      (ap2 (sumF (Ab habs)) (succ (sndT (sndT P))) (pairT D P)) := by
  have hp1 := p_pos (prime_two hp)
  have hq' : (Γ.map Fm.shift) ⊢[PRAAx] le one (fstT (Syn.shift P)) := by
    simpa [Fm.shift, Syn.shift] using hq.shift
  have hp' : (Γ.map Fm.shift) ⊢[PRAAx] prime (Syn.shift p) := by simpa [Fm.shift, Syn.shift] using hp.shift
  have hD' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift D ≐ succ (pred (Syn.shift D)) := by
    simpa [Fm.shift, Syn.shift] using hD.shift
  have sN : Syn.shift (succ (sndT (sndT P))) = succ (sndT (sndT (Syn.shift P))) := by simp [Syn.shift]
  have e1 := (sum_const_mul (Γ := Γ) (Ab habs) (succ (sndT (sndT P))) p (pairT (D * p) P)).eqSymm
  have l2 : Γ ⊢[PRAAx] le (ap2 (sumF (cmB (Ab habs))) (succ (sndT (sndT P))) (pairT p (pairT (D * p) P)))
      (ap2 (sumF (mixB g1B (riB hB))) (succ (sndT (sndT P)))
        (pairT (pairT p (pairT D P)) (pairT p (pairT p (pairT D P))))) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT, shift_mul']
    rw [sN]
    exact pt_le hq'.wk hp'.wk hD'.wk Prf.hyp0
  have e3 := sum_mix (Γ := Γ) g1B (riB hB) (succ (sndT (sndT P))) (pairT p (pairT D P))
    (pairT p (pairT p (pairT D P)))
  have l4 := reindex_le (Γ := Γ) hB (x := pairT p (pairT D P)) (succ (sndT (sndT P))) hp1
  have e5 : Γ ⊢[PRAAx] ap2 (sumF g1B) (succ (sndT (sndT P))) (pairT p (pairT D P)) +
      ap2 (sumF hB) (succ (sndT (sndT P))) (pairT p (pairT D P)) ≐
      ap2 (sumF (Ab habs)) (succ (sndT (sndT P))) (pairT D P) := by
    refine (sum_add g1B hB _ _).eqSymm.eqTrans (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
    simp only [shift_pairT]
    exact split_pt _ _ _ _
  exact chain e1 l2 e3 l4 e5

end LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightStep
