import IPRADerivations.DiophantineNumberTheory.AperyLcmTerms
import IPRADerivations.DiophantineNumberTheory.AperyLcmVal

/-!
# The per-prime count of the Apéry divisibility step

Packet: `diophantine-number-theory/apery_ipra`, Lemma `lem:lcm-div` (`d_{42m} ∣ d_m M_m`), the per-index
comparison: with `q = p^{j+1}`, `E = v_p(d_{42m})` and `E' = v_p(d_m)`,

  `[j < E] + ⌊21m/q⌋ + ⌊14m/q⌋ + ⌊6m/q⌋ + ⌊m/q⌋ ≤ [j < E'] + ⌊42m/q⌋`.

If `j < E` then `q ≤ 42m`, so `⌊42m/q⌋ ≥ 1`; if moreover `q > m` the floors fall short of `⌊42m/q⌋`
(`AperyLcmTerms.terms_lt`), and if `q ≤ m` then `j < E'`. If `j ≥ E`, `AperyLcmTerms.terms_le` suffices.

* `terms_le'`, `terms_lt'`: the termwise bounds at an arbitrary positive `q`;
* `quo_pos`: `q ≤ N` gives `⌊N/q⌋ ≥ 1`;
* `point_bound`: the comparison above, from `p ≥ 2`, `sg(E) p^E ≤ 42m` and `m < p^{E'+1}` (the two halves of
  `LcmUpto.Inv`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperyLcmCount

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.AperyLcmTerms (terms_le terms_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val lt_pw)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (lcmu Inv lcm_valuation)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (qB' qB'_at)
open LeanProofs.IPRA.Combinatorics.LegendreFact (ltB inst2_ltB count_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext)
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialLcm (qz)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyLcmVal (L val_Mm binom_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultinomial (Mm)
open LeanProofs.IPRA.Combinatorics.LegendreFact (shift_le_two)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- The four floors at `q`. -/
abbrev fl (m q : PTm k) : PTm k := quo (num 21 * m) q + quo (num 14 * m) q + quo (num 6 * m) q + quo m q

theorem fl_congr {m q q' : PTm k} (h : Γ ⊢[PRAAx] q ≐ q') : Γ ⊢[PRAAx] fl m q ≐ fl m q' :=
  congrAdd (congrAdd (congrAdd (congrAp2 quoF (.eqRefl _) h) (congrAp2 quoF (.eqRefl _) h))
    (congrAp2 quoF (.eqRefl _) h)) (congrAp2 quoF (.eqRefl _) h)

theorem terms_le' {m q : PTm k} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) :
    Γ ⊢[PRAAx] le (fl m q) (quo (num 42 * m) q) :=
  le_congr (fl_congr hq.eqSymm) (congrAp2 quoF (.eqRefl _) hq.eqSymm) (terms_le m (pred q))

theorem terms_lt' {m q : PTm k} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hm : Γ ⊢[PRAAx] lt m q)
    (hJ : Γ ⊢[PRAAx] le one (quo (num 42 * m) q)) : Γ ⊢[PRAAx] lt (fl m q) (quo (num 42 * m) q) :=
  lt_congr (fl_congr hq.eqSymm) (congrAp2 quoF (.eqRefl _) hq.eqSymm)
    (terms_lt (lt_congr (.eqRefl _) hq hm) (le_congr (.eqRefl _) (congrAp2 quoF (.eqRefl _) hq) hJ))

/-- `q ≤ N` gives `⌊N/q⌋ ≥ 1`. -/
theorem quo_pos {N q : PTm k} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (h : Γ ⊢[PRAAx] le q N) :
    Γ ⊢[PRAAx] le one (quo N q) := by
  have d := div_mod (Γ := Γ) N (pred q)
  refine .orE (zero_or_succ (quo N q)) ?_ ?_
  · have h0 : ((quo N q ≐ zero) :: Γ) ⊢[PRAAx] quo N q ≐ zero := Prf.hyp0
    have e := natEq ((Prf.andE₁ d).wk (ψ := quo N q ≐ zero))
    have eq := natEq (hq.wk (ψ := quo N q ≐ zero))
    have e0 := natEq ((congrAp2 quoF (.eqRefl N) (hq.wk (ψ := quo N q ≐ zero))).eqSymm.eqTrans h0)
    have hr : ((quo N q ≐ zero) :: Γ) ⊢[PRAAx] le (succ (rem N (succ (pred q)))) (succ (pred q)) := (Prf.andE₂ d).wk
    have hN : ((quo N q ≐ zero) :: Γ) ⊢[PRAAx] le q N := h.wk
    have c : ((quo N q ≐ zero) :: Γ) ⊢[PRAAx] le (succ zero) zero := by
      ipra_le sl hr + sl hN using
        linear_combination -e - (𝔞 (pred q) + 1) * e0 + eq
    exact not_succ_le_self zero _ c
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (by ipra_le 𝔞 (pred (quo N q)))

theorem pos_of_lt {a b : PTm k} (h : Γ ⊢[PRAAx] lt a b) : Γ ⊢[PRAAx] b ≐ succ (pred b) := by
  refine .orE (zero_or_succ b) ?_ Prf.hyp0
  have h0 : ((b ≐ zero) :: Γ) ⊢[PRAAx] b ≐ zero := Prf.hyp0
  have c : ((b ≐ zero) :: Γ) ⊢[PRAAx] le (succ a) zero := le_congr (.eqRefl _) h0 h.wk
  exact not_succ_le_self zero _ (by ipra_le sl c + 𝔞 a)

/-- The per-index comparison `[j < E] + floors ≤ [j < E'] + ⌊42m/q⌋`, `q = p^{j+1}`. -/
theorem point_bound {p m j E E' : PTm k} (hp2 : Γ ⊢[PRAAx] le two p)
    (hI1 : Γ ⊢[PRAAx] le (sg E * pw p E) (num 42 * m)) (hI2 : Γ ⊢[PRAAx] lt m (pw p (succ E'))) :
    Γ ⊢[PRAAx] le (sg (monus E j) + fl m (pw p (succ j))) (sg (monus E' j) + quo (num 42 * m) (pw p (succ j))) := by
  have hpp := p_pos hp2
  have hq := pw_pos' hpp (succ j)
  have tle := terms_le' (m := m) hq
  refine .orE (lt_or_le j E) ?_ ?_
  · have hj : (lt j E :: Γ) ⊢[PRAAx] lt j E := Prf.hyp0
    have hE := pos_of_lt hj
    have sgE : (lt j E :: Γ) ⊢[PRAAx] sg E ≐ one := (congrSg hE).eqTrans (sg_succ _)
    have pE : (lt j E :: Γ) ⊢[PRAAx] le (pw p E) (num 42 * m) :=
      le_congr ((congrMul sgE (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _) hI1.wk
    have qle : (lt j E :: Γ) ⊢[PRAAx] le (pw p (succ j)) (num 42 * m) := le_trans (pw_le_exp hpp.wk hj) pE
    have hJ := quo_pos hq.wk qle
    refine .orE (lt_or_le m (pw p (succ j))) ?_ ?_
    · let Δ := lt m (pw p (succ j)) :: lt j E :: Γ
      have tlt := terms_lt' (hq.wk.wk : Δ ⊢[PRAAx] _) Prf.hyp0 hJ.wk
      have tlt' : Δ ⊢[PRAAx] le (succ (fl m (pw p (succ j)))) (quo (num 42 * m) (pw p (succ j))) := tlt
      have s1 := natEq ((sg_lt hj).wk : Δ ⊢[PRAAx] _)
      ipra_le sl tlt' + 𝔞 (sg (monus E' j)) using linear_combination -s1
    · let Δ := le (pw p (succ j)) m :: lt j E :: Γ
      have hle : Δ ⊢[PRAAx] le (pw p (succ j)) m := Prf.hyp0
      have hjE' : Δ ⊢[PRAAx] lt j E' := by
        refine .orE (lt_or_le j E') Prf.hyp0 ?_
        have hE' : (le E' j :: Δ) ⊢[PRAAx] le E' j := Prf.hyp0
        have hs : (le E' j :: Δ) ⊢[PRAAx] le (succ E') (succ j) := by ipra_le sl hE'
        have pw1 := pw_le_exp (hpp.wk.wk.wk : (le E' j :: Δ) ⊢[PRAAx] _) hs
        have hI2' : (le E' j :: Δ) ⊢[PRAAx] le (succ m) (pw p (succ E')) := hI2.wk.wk.wk
        have hle' : (le E' j :: Δ) ⊢[PRAAx] le (pw p (succ j)) m := hle.wk
        exact not_succ_le_self zero _ (by ipra_le sl pw1 + sl hI2' + sl hle')
      have s1 := natEq ((sg_lt hj).wk : Δ ⊢[PRAAx] _)
      have s2 := natEq (sg_lt hjE')
      have tle' : Δ ⊢[PRAAx] le (fl m (pw p (succ j))) (quo (num 42 * m) (pw p (succ j))) := tle.wk.wk
      ipra_le sl tle' using linear_combination s2 - s1
  · have s0 := natEq (sg_le (Prf.hyp0 : (le E j :: Γ) ⊢[PRAAx] le E j))
    have tle' : (le E j :: Γ) ⊢[PRAAx] le (fl m (pw p (succ j))) (quo (num 42 * m) (pw p (succ j))) := tle.wk
    ipra_le sl tle' + 𝔞 (sg (monus E' j)) using linear_combination -s0

/-! ## Summing the comparison -/

/-- `v_p(d_N) ≤ N`. -/
theorem e_le_N {p N : PTm k} (hp2 : Γ ⊢[PRAAx] le two p)
    (hI1 : Γ ⊢[PRAAx] le (sg (val p (lcmu N)) * pw p (val p (lcmu N))) N) : Γ ⊢[PRAAx] le (val p (lcmu N)) N := by
  refine .orE (zero_or_succ (val p (lcmu N))) (le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le _)) ?_
  have s : ((val p (lcmu N) ≐ succ (pred (val p (lcmu N)))) :: Γ) ⊢[PRAAx] sg (val p (lcmu N)) ≐ one :=
    (congrSg Prf.hyp0).eqTrans (sg_succ _)
  have pe := le_congr ((congrMul s (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _) hI1.wk
  exact le_trans (le_of_lt (lt_pw hp2.wk _)) pe

theorem fl_congr2 {m m' q q' : PTm k} (hm : Γ ⊢[PRAAx] m ≐ m') (hq : Γ ⊢[PRAAx] q ≐ q') :
    Γ ⊢[PRAAx] fl m q ≐ fl m' q' :=
  congrAdd (congrAdd (congrAdd (congrAp2 quoF (congrMul (.eqRefl _) hm) hq)
    (congrAp2 quoF (congrMul (.eqRefl _) hm) hq)) (congrAp2 quoF (congrMul (.eqRefl _) hm) hq)) (congrAp2 quoF hm hq)

/-- The left body `[j < E] + floors`, over `1 = ⟨⟨p, m⟩, ⟨E, E'⟩⟩`. -/
abbrev aB : PTm 2 := sg (monus (fstT (sndT (var 1))) (var 0)) +
  fl (sndT (fstT (var 1))) (pw (fstT (fstT (var 1))) (succ (var 0)))
/-- The right body `[j < E'] + ⌊42m/q⌋`. -/
abbrev bB : PTm 2 := sg (monus (sndT (sndT (var 1))) (var 0)) +
  quo (num 42 * sndT (fstT (var 1))) (pw (fstT (fstT (var 1))) (succ (var 0)))
/-- The floors alone, over `1 = ⟨p, m⟩`. -/
abbrev fB : PTm 2 := fl (sndT (var 1)) (pw (fstT (var 1)) (succ (var 0)))

section Proj
variable {p m E E' : PTm k}
theorem pp : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT p m) (pairT E E'))) ≐ p := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
theorem pm : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT p m) (pairT E E'))) ≐ m := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
theorem pE : Γ ⊢[PRAAx] fstT (sndT (pairT (pairT p m) (pairT E E'))) ≐ E := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
theorem pE' : Γ ⊢[PRAAx] sndT (sndT (pairT (pairT p m) (pairT E E'))) ≐ E' := (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
end Proj

theorem aB_at (j p m E E' : PTm k) :
    Γ ⊢[PRAAx] inst2 aB j (pairT (pairT p m) (pairT E E')) ≐ sg (monus E j) + fl m (pw p (succ j)) := by
  have h : inst2 aB j (pairT (pairT p m) (pairT E E')) =
      sg (monus (fstT (sndT (pairT (pairT p m) (pairT E E')))) j) +
        fl (sndT (fstT (pairT (pairT p m) (pairT E E')))) (pw (fstT (fstT (pairT (pairT p m) (pairT E E')))) (succ j)) := by
    simp [inst2]
  rw [h]
  exact congrAdd (congrSg (congrMonus pE (.eqRefl _)))
    (fl_congr2 pm (LeanProofs.IPRA.Combinatorics.BinomialTheorem.congrPw pp (.eqRefl _)))

theorem bB_at (j p m E E' : PTm k) :
    Γ ⊢[PRAAx] inst2 bB j (pairT (pairT p m) (pairT E E')) ≐ sg (monus E' j) + quo (num 42 * m) (pw p (succ j)) := by
  have h : inst2 bB j (pairT (pairT p m) (pairT E E')) =
      sg (monus (sndT (sndT (pairT (pairT p m) (pairT E E')))) j) +
        quo (num 42 * sndT (fstT (pairT (pairT p m) (pairT E E')))) (pw (fstT (fstT (pairT (pairT p m) (pairT E E')))) (succ j)) := by
    simp [inst2]
  rw [h]
  exact congrAdd (congrSg (congrMonus pE' (.eqRefl _)))
    (congrAp2 quoF (congrMul (.eqRefl _) pm) (LeanProofs.IPRA.Combinatorics.BinomialTheorem.congrPw pp (.eqRefl _)))

/-- `⌊cm/p^{j+1}⌋`, over `0 = j`, `1 = ⟨p, m⟩`. -/
abbrev fc (c : ℕ) : PTm 2 := quo (num c * sndT (var 1)) (pw (fstT (var 1)) (succ (var 0)))
/-- The four floors as a sum of bodies. -/
abbrev fB' : PTm 2 := ((fc 21 + fc 14) + fc 6) + qB'

theorem inst2_add (f g : PTm 2) (i y : PTm k) : inst2 (f + g) i y = inst2 f i y + inst2 g i y := by
  simp [inst2]

theorem fc_at (c : ℕ) (j p m : PTm k) :
    Γ ⊢[PRAAx] inst2 (fc c) j (pairT p m) ≐ quo (num c * m) (pw p (succ j)) := by
  have h : inst2 (fc c) j (pairT p m) = quo (num c * sndT (pairT p m)) (pw (fstT (pairT p m)) (succ j)) := by
    simp [inst2]
  rw [h]
  exact congrAp2 quoF (congrMul (.eqRefl _) (snd_pair _ _))
    (LeanProofs.IPRA.Combinatorics.BinomialTheorem.congrPw (fst_pair _ _) (.eqRefl _))

theorem fB'_at (j p m : PTm k) : Γ ⊢[PRAAx] inst2 fB' j (pairT p m) ≐ fl m (pw p (succ j)) := by
  rw [inst2_add, inst2_add, inst2_add]
  exact congrAdd (congrAdd (congrAdd (fc_at 21 j p m) (fc_at 14 j p m)) (fc_at 6 j p m)) (qB'_at j p m)

/-- Truncating `∑_{j<N+1} ⌊M/p^{j+1}⌋` to `L(M)` when `M ≤ N`. -/
theorem trunc {p M N : PTm k} (hp2 : Γ ⊢[PRAAx] le two p) (hMN : Γ ⊢[PRAAx] le M N) :
    Γ ⊢[PRAAx] ap2 (sumF qB') (succ N) (pairT p M) ≐ L p M := by
  have s2 := sum_ext (Γ := Γ) qB' (B := M) (N := succ N) (x := pairT p M) (fun Δ a hs hl => by
    rw [shift_pairT]
    exact (qB'_at _ _ _).eqTrans (qz ((shift_le_two hp2).weaken hs) (le_of_lt hl)))
    ((succ_monus_succ _ _).eqTrans hMN)
  have s3 := sum_succ' (Γ := Γ) qB' M (pairT p M)
  have z3 := (qB'_at (Γ := Γ) M p M).eqTrans (qz hp2 (le_refl M))
  exact s2.eqTrans (s3.eqTrans ((congrAdd (.eqRefl _) z3).eqTrans (add_zero _)))

theorem fc_sum (c : ℕ) {p m N : PTm k} (hp2 : Γ ⊢[PRAAx] le two p) (hc : Γ ⊢[PRAAx] le (num c * m) N) :
    Γ ⊢[PRAAx] ap2 (sumF (fc c)) (succ N) (pairT p m) ≐ L p (num c * m) := by
  refine (sum_congr_bounded (fc c) qB' (pairT p m) (pairT p (num c * m)) (succ N) (.allI (.impI ?_))).eqTrans
    (trunc hp2 hc)
  have e : Syn.shift (num c * m) = num c * Syn.shift m := by simp [Syn.shift]
  simp only [shift_pairT]; rw [e]
  exact (fc_at _ _ _ _).eqTrans (qB'_at _ _ _).eqSymm

/-- The per-prime inequality `v_p(d_{42m}) ≤ v_p(d_m) + v_p(M_m)`. -/
theorem val_lcm_le {p : PTm k} (hp : Γ ⊢[PRAAx] prime p) (m : PTm k) :
    Γ ⊢[PRAAx] le (val p (lcmu (num 42 * m))) (val p (lcmu m) + val p (Mm m)) := by
  have hp2 := prime_two hp
  have I := lcm_valuation hp (num 42 * m)
  have I1 := Prf.andE₁ I
  have J := lcm_valuation hp m
  have J1 := Prf.andE₁ J; have J2 := Prf.andE₂ J
  have hp2' := shift_le_two hp2
  have I1s : Γ.map Fm.shift ⊢[PRAAx] le (sg (Syn.shift (val p (lcmu (num 42 * m)))) *
      pw (Syn.shift p) (Syn.shift (val p (lcmu (num 42 * m))))) (num 42 * Syn.shift m) := by
    have e := I1.shift
    simpa [Fm.shift, Syn.shift] using e
  have J2s : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift m) (pw (Syn.shift p) (succ (Syn.shift (val p (lcmu m))))) := by
    have e := J2.shift
    simpa [Fm.shift, Syn.shift] using e
  -- the summed comparison, over `j < 42m + 1`
  have sl := Analysis.PowerSums.sum_le (Γ := Γ) aB bB
    (pairT (pairT p m) (pairT (val p (lcmu (num 42 * m))) (val p (lcmu m)))) (succ (num 42 * m))
    (.allI (.impI (by
      simp only [shift_pairT]
      exact le_congr (aB_at _ _ _ _ _).eqSymm (bB_at _ _ _ _ _).eqSymm (point_bound hp2'.wk I1s.wk J2s.wk))))
  have ca : Γ ⊢[PRAAx] ap2 (sumF aB) (succ (num 42 * m)) (pairT (pairT p m) (pairT (val p (lcmu (num 42 * m))) (val p (lcmu m)))) ≐
      ap2 (sumF ltB) (succ (num 42 * m)) (val p (lcmu (num 42 * m))) + ap2 (sumF fB') (succ (num 42 * m)) (pairT p m) := by
    refine sum_add2 _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]; rw [inst2_ltB]
    exact (aB_at _ _ _ _ _).eqTrans (congrAdd (.eqRefl _) (fB'_at _ _ _).eqSymm)
  have cb : Γ ⊢[PRAAx] ap2 (sumF bB) (succ (num 42 * m)) (pairT (pairT p m) (pairT (val p (lcmu (num 42 * m))) (val p (lcmu m)))) ≐
      ap2 (sumF ltB) (succ (num 42 * m)) (val p (lcmu m)) + ap2 (sumF qB') (succ (num 42 * m)) (pairT p (num 42 * m)) := by
    refine sum_add2 _ _ _ (.allI (.impI ?_))
    have e : Syn.shift (num 42 * m) = num 42 * Syn.shift m := by simp [Syn.shift]
    simp only [shift_pairT]; rw [inst2_ltB, e]
    exact (bB_at _ _ _ _ _).eqTrans (congrAdd (.eqRefl _) (qB'_at _ _ _).eqSymm)
  have c1 := sum_add2 (Γ := Γ) ((fc 21 + fc 14) + fc 6) qB' fB' (K := succ (num 42 * m)) (x := pairT p m)
    (x' := pairT p m) (z := pairT p m) (.allI (.impI (by rw [inst2_add]; exact .eqRefl _)))
  have c2 := sum_add2 (Γ := Γ) (fc 21 + fc 14) (fc 6) ((fc 21 + fc 14) + fc 6) (K := succ (num 42 * m))
    (x := pairT p m) (x' := pairT p m) (z := pairT p m) (.allI (.impI (by rw [inst2_add]; exact .eqRefl _)))
  have c3 := sum_add2 (Γ := Γ) (fc 21) (fc 14) (fc 21 + fc 14) (K := succ (num 42 * m))
    (x := pairT p m) (x' := pairT p m) (z := pairT p m) (.allI (.impI (by rw [inst2_add]; exact .eqRefl _)))
  have t21 := fc_sum 21 hp2 (m := m) (N := num 42 * m) (by ipra_le 21 * 𝔞 m)
  have t14 := fc_sum 14 hp2 (m := m) (N := num 42 * m) (by ipra_le 28 * 𝔞 m)
  have t6 := fc_sum 6 hp2 (m := m) (N := num 42 * m) (by ipra_le 36 * 𝔞 m)
  have tm := trunc hp2 (M := m) (N := num 42 * m) (by ipra_le 41 * 𝔞 m)
  have tN := trunc hp2 (M := num 42 * m) (N := num 42 * m) (le_refl _)
  have cE := count_lt (Γ := Γ) (le_trans (e_le_N hp2 I1) (le_succ_self _))
  have cE' := count_lt (Γ := Γ) (K := succ (num 42 * m))
    (le_trans (e_le_N hp2 J1) (by ipra_le 41 * 𝔞 m + 1 : Γ ⊢[PRAAx] le m (succ (num 42 * m))))
  have u1 := natEq ca; have u2 := natEq cb; have u3 := natEq c1; have u4 := natEq c2; have u5 := natEq c3
  have w1 := natEq t21; have w2 := natEq t14; have w3 := natEq t6; have w4 := natEq tm; have w5 := natEq tN
  have x1 := natEq cE; have x2 := natEq cE'
  refine le_of_add_le_add_right (c := L p (num 21 * m) + L p (num 14 * m) + L p (num 6 * m) + L p m) ?_
  refine le_congr ?_ ?_ sl
  · ipra_lc u1 + u3 + u4 + u5 + w1 + w2 + w3 + w4 + x1
  · ipra_lc u2 + w5 + x2 - natEq (val_Mm hp m)

theorem Mm_pos (m : PTm k) : Γ ⊢[PRAAx] Mm m ≐ succ (pred (Mm m)) := by
  have l1 : Γ ⊢[PRAAx] le (num 21 * m) (num 42 * m) := by ipra_le 21 * 𝔞 m
  have l2 : Γ ⊢[PRAAx] le (num 14 * m) (num 21 * m) := by ipra_le 7 * 𝔞 m
  have l3 : Γ ⊢[PRAAx] le (num 6 * m) (num 7 * m) := by ipra_le 𝔞 m
  exact pos_mul (pos_mul (binom_pos l1) (binom_pos l2)) (binom_pos l3)

/-- `lem:lcm-div`: `d_{42m} ∣ d_m M_m`. -/
theorem lcm_div (m : PTm k) : Γ ⊢[PRAAx] dvd (lcmu (num 42 * m)) (lcmu m * Mm m) := by
  have apos := lcmu_pos (Γ := Γ) (num 42 * m)
  have bpos := pos_mul (lcmu_pos (Γ := Γ) m) (Mm_pos m)
  have hs1 : Syn.shift (lcmu (num 42 * m)) = lcmu (num 42 * Syn.shift m) := by simp [Syn.shift]
  have hs2 : Syn.shift (lcmu m * Mm m) = lcmu (Syn.shift m) * Mm (Syn.shift m) := by simp [Syn.shift]
  refine dvd_of_val_le (N := succ (lcmu (num 42 * m) + lcmu m * Mm m)) apos bpos
    ((succ_monus_succ _ _).eqTrans (le_add_right _ _)) ((succ_monus_succ _ _).eqTrans (le_add_left _ _))
    (.allI (.impI (.impI ?_)))
  rw [hs1, hs2]
  exact le_congr (.eqRefl _) (val_mul (prime_of_isP Prf.hyp0) (lcmu_pos _) (Mm_pos _)).eqSymm
    (val_lcm_le (prime_of_isP Prf.hyp0) _)

end LeanProofs.IPRA.DiophantineNumberTheory.AperyLcmCount
