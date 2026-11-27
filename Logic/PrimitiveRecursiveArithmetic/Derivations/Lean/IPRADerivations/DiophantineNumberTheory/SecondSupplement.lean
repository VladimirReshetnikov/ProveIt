import IPRADerivations.DiophantineNumberTheory.QuadraticReciprocity

/-!
# The second supplementary law

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex`, `eq:two`:

  "For `a = 2`, `2 ≤ 2i ≤ p − 1` when `1 ≤ i ≤ h`, so `r_i = 2i`. A remainder is large just when `i > ⌊h/2⌋`.
  Consequently `N_p(2) = h − ⌊h/2⌋`. To compare parities, note that `(p² − 1)/8 = h(h + 1)/2`. […]
  `(2/p) = (−1)^{(p² − 1)/8}`."

For an odd prime `p = 2h + 1`:

  `signBit p 2 = par ⌊h (h + 1) / 2⌋`                                                     (`two_law`),

where `h (h + 1)/2 = (p² − 1)/8`. The steps:

* `e_two`: `e_i = [2 (i + 1) > h]` for `i < h` (no reduction modulo `p` occurs);
* `count_two`: `N_p(2) + ⌊h/2⌋ = h` (`DivisorHyperbola.row_count` for the row `2 (i + 1) ≤ h`);
* `par_two`: `N + ⌊h/2⌋ = h` gives `par N = par ⌊h (h + 1)/2⌋`, by the two cases of `h mod 2`;
* Gauss's lemma with `a = 2` (`GaussLemma.gauss_lemma`, `QuadraticReciprocity.sign_eq`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.SecondSupplement

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg one_inst)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (sg_pos rem_small)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola (leI IB IB_at row_count quo_le_self)
open LeanProofs.IPRA.DiophantineNumberTheory.EisensteinParity (eV eB inst2_eB)
open LeanProofs.IPRA.DiophantineNumberTheory.GaussLemma (gauss_lemma pred_ne_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The large remainders for `a = 2` -/

/-- `eV` over `0 = i`, `1 = p`, `2 = a`. -/
abbrev eV3 : PTm 3 := eV (var 0) (var 1) (var 2)

theorem inst3_eV3 (i p a : PTm n) : inst3 eV3 i p a = eV i p a := by simp [inst3, subst_ap1]

theorem congrE {i i' p p' a a' : PTm n} (h₁ : Γ ⊢[PRAAx] i ≐ i') (h₂ : Γ ⊢[PRAAx] p ≐ p')
    (h₃ : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx] eV i p a ≐ eV i' p' a' := by
  have e := congrInst3 eV3 h₁ h₂ h₃
  rw [inst3_eV3 i p a, inst3_eV3 i' p' a'] at e
  exact e

/-- `2 (i + 1) < p` for `i < h`, `p = 2h + 1`. -/
theorem two_lt {p h i : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * h + one) (hi : Γ ⊢[PRAAx] lt i h) :
    Γ ⊢[PRAAx] lt (succ i * two) p := by
  have x := natEq ep
  ipra_le 2 * sl hi with x

/-- `e_i = [2 (i + 1) > h]` for `i < h`. -/
theorem e_two {p i : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * half p + one) (hi : Γ ⊢[PRAAx] lt i (half p)) :
    Γ ⊢[PRAAx] eV i p two ≐ sg (monus (succ i * two) (half p)) :=
  congrSg (congrMonus (rem_small (two_lt ep hi)) (.eqRefl _))

theorem v01 : Γ ⊢[PRAAx] (zero : PTm n) + one ≐ one := zero_add _
theorem v10 : Γ ⊢[PRAAx] (one : PTm n) + zero ≐ one := add_zero _

/-- `[x ≥ 1] + (1 − x) = 1`. -/
theorem sg_compl (x : PTm n) : Γ ⊢[PRAAx] sg x + monus one x ≐ one := by
  refine .orE (zero_or_succ x) ?_ ?_
  · have h0 : ((x ≐ zero) :: Γ) ⊢[PRAAx] x ≐ zero := Prf.hyp0
    exact (congrAdd ((congrSg h0).eqTrans sg_zero) ((congrMonus (.eqRefl _) h0).eqTrans (monus_zero _))).eqTrans v01
  · have h1 : ((x ≐ succ (pred x)) :: Γ) ⊢[PRAAx] x ≐ succ (pred x) := Prf.hyp0
    exact (congrAdd (sg_pos h1) ((congrMonus (.eqRefl _) h1).eqTrans
      ((succ_monus_succ _ _).eqTrans (zero_monus _)))).eqTrans v10

/-- `e_i + [2 (i + 1) ≤ h] = 1` for `i < h`. -/
theorem pt {p i : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * half p + one) (hi : Γ ⊢[PRAAx] lt i (half p)) :
    Γ ⊢[PRAAx] eV i p two + leI (succ one * succ i) (half p) ≐ one :=
  (congrAdd ((e_two ep hi).eqTrans (congrSg (congrMonus (mul_comm _ _) (.eqRefl _)))) (.eqRefl _)).eqTrans
    (sg_compl _)

/-- `N_p(2) + ⌊h/2⌋ = h` for `p = 2h + 1`. -/
theorem count_two {p : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * half p + one) :
    Γ ⊢[PRAAx] ap2 (sumF eB) (half p) (pairT p two) + quo (half p) two ≐ half p := by
  have ep' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ two * half (Syn.shift p) + one := by
    simpa [Fm.shift, Syn.shift, subst_ap1] using ep.shift
  have sH : Syn.shift (half p) = half (Syn.shift p) := by simp [Syn.shift, subst_ap1]
  have s1 : Syn.shift (pairT (pairT p two) (pairT one (half p))) =
      pairT (pairT (Syn.shift p) two) (pairT one (half (Syn.shift p))) := by simp [Syn.shift, subst_ap1]
  have c1 : Γ ⊢[PRAAx] ap2 (sumF (mixB eB IB)) (half p) (pairT (pairT p two) (pairT one (half p))) ≐ half p := by
    refine (sum_congr_bounded _ (one : PTm 2) _ (pairT (pairT p two) (pairT one (half p))) _
      (.allI (.impI ?_))).eqTrans (sum_ones _ _)
    rw [s1, sH, one_inst]
    refine (mix_at eB IB _ _ _).eqTrans ?_
    rw [inst2_eB]
    exact (congrAdd (congrE (.eqRefl _) (fst_pair _ _) (snd_pair _ _)) (IB_at _ _ _)).eqTrans
      (pt ep'.wk Prf.hyp0)
  have c2 := sum_mix (Γ := Γ) eB IB (half p) (pairT p two) (pairT one (half p))
  have c3 : Γ ⊢[PRAAx] ap2 (sumF IB) (half p) (pairT one (half p)) ≐ quo (half p) two :=
    row_count (quo_le_self one (half p))
  exact (congrAdd (.eqRefl _) c3.eqSymm).eqTrans (c2.eqSymm.eqTrans c1)

/-! ## The parity of `h − ⌊h/2⌋` -/

theorem even_alg {h t : PTm n} (e : Γ ⊢[PRAAx] h ≐ two * t) :
    Γ ⊢[PRAAx] h * succ h ≐ two * (t * succ (two * t)) + zero := by
  ipra_lc (𝔞 h + 2 * 𝔞 t + 1) * natEq e

theorem odd_alg {h t : PTm n} (e : Γ ⊢[PRAAx] h ≐ two * t + one) :
    Γ ⊢[PRAAx] h * succ h ≐ two * (succ (two * t) * succ t) + zero := by
  ipra_lc (𝔞 h + 2 * 𝔞 t + 2) * natEq e

theorem q_even (t : PTm n) : Γ ⊢[PRAAx] t * succ (two * t) ≐ t + two * (t * t) := by
  ipra_ring

theorem q_odd (t : PTm n) : Γ ⊢[PRAAx] succ (two * t) * succ t ≐ succ t + two * (t * succ t) := by
  ipra_ring

theorem n_alg {N t ρ h : PTm n} (hN : Γ ⊢[PRAAx] N + t ≐ h) (d : Γ ⊢[PRAAx] h ≐ two * t + ρ) :
    Γ ⊢[PRAAx] N ≐ t + ρ := by
  ipra_lc natEq hN + natEq d

theorem succ_alg (t : PTm n) : Γ ⊢[PRAAx] t + one ≐ succ t := by ipra_ring

/-- `N + ⌊h/2⌋ = h` gives `par N = par ⌊h (h + 1)/2⌋`. -/
theorem par_two {h N : PTm n} (hN : Γ ⊢[PRAAx] N + quo h two ≐ h) :
    Γ ⊢[PRAAx] par N ≐ par (quo (h * succ h) two) := by
  have d := div_eq (Γ := Γ) (j := h) two_pos'
  have rl := rem_lt' (Γ := Γ) two_pos' h
  have eN := n_alg hN d
  refine .orE (zero_or_succ (rem h two)) ?_ ?_
  · let C : List (Fm PTm n) := (rem h two ≐ zero) :: Γ
    have r0 : C ⊢[PRAAx] rem h two ≐ zero := Prf.hyp0
    have eh : C ⊢[PRAAx] h ≐ two * quo h two := d.wk.eqTrans ((congrAdd (.eqRefl _) r0).eqTrans (add_zero _))
    have q : C ⊢[PRAAx] quo (h * succ h) two ≐ quo h two * succ (two * quo h two) :=
      quo_eq two_pos' (even_alg eh) (zero_lt_succ _)
    have pq : C ⊢[PRAAx] par (quo (h * succ h) two) ≐ par (quo h two) :=
      (congrAp1 parF (q.eqTrans (q_even _))).eqTrans (par_add_two _ _)
    have pn : C ⊢[PRAAx] par N ≐ par (quo h two) :=
      congrAp1 parF (eN.wk.eqTrans ((congrAdd (.eqRefl _) r0).eqTrans (add_zero _)))
    exact pn.eqTrans pq.eqSymm
  · let C : List (Fm PTm n) := (rem h two ≐ succ (pred (rem h two))) :: Γ
    have hs : C ⊢[PRAAx] rem h two ≐ succ (pred (rem h two)) := Prf.hyp0
    have r1 : C ⊢[PRAAx] rem h two ≐ one := by
      have l : C ⊢[PRAAx] le (pred (rem h two)) zero :=
        (succ_monus_succ _ _).eqSymm.eqTrans ((congrMonus hs.eqSymm (.eqRefl _)).eqTrans
          ((succ_monus_succ _ _).eqSymm.eqTrans rl.wk))
      exact hs.eqTrans (congrSucc (le_antisymm l (zero_le _)))
    have eh : C ⊢[PRAAx] h ≐ two * quo h two + one := d.wk.eqTrans (congrAdd (.eqRefl _) r1)
    have q : C ⊢[PRAAx] quo (h * succ h) two ≐ succ (two * quo h two) * succ (quo h two) :=
      quo_eq two_pos' (odd_alg eh) (zero_lt_succ _)
    have pq : C ⊢[PRAAx] par (quo (h * succ h) two) ≐ par (succ (quo h two)) :=
      (congrAp1 parF (q.eqTrans (q_odd _))).eqTrans (par_add_two _ _)
    have pn : C ⊢[PRAAx] par N ≐ par (succ (quo h two)) :=
      congrAp1 parF (eN.wk.eqTrans ((congrAdd (.eqRefl _) r1).eqTrans (succ_alg _)))
    exact pn.eqTrans pq.eqSymm

/-! ## The law -/

/-- `eq:two`: `signBit p 2 = par ⌊h (h + 1)/2⌋` for an odd prime `p = 2h + 1`, where `h (h + 1)/2 = (p² − 1)/8`. -/
theorem two_law {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one) :
    Γ ⊢[PRAAx] signBit p two ≐ par (quo (half p * succ (half p)) two) := by
  have hq := prime_two hp
  have hp1 := p_pos hq
  have nd : Γ ⊢[PRAAx] neg (dvd p two) := by
    refine .impI ?_
    have l := dvd_le' (Γ := dvd p two :: Γ) hp1.wk Prf.hyp0 two_pos'
    have e : (dvd p two :: Γ) ⊢[PRAAx] p ≐ two := le_antisymm l hq.wk
    exact pred_ne_one hp1.wk hodd.wk _ ((congrPred e).eqTrans (pred_succ _))
  have hc : Γ ⊢[PRAAx] gcd p two ≐ one := gcd_prime hp nd
  exact (sign_eq p two).eqTrans ((gauss_lemma hp hodd two_pos' hc).eqSymm.eqTrans
    (par_two (count_two (odd_of hodd))))

end LeanProofs.IPRA.DiophantineNumberTheory.SecondSupplement
