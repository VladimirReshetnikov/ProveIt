import IPRADerivations.AnalyticNumberTheory.PowerDivisorPrefix

/-!
# One row of the inversion along perfect powers (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, proof of Theorem
`thm:powerdivisor`: "For the second identity, substitute the first into the right side, use
`⌊⌊N/d^h⌋/e^h⌋ = ⌊N/(de)^h⌋`, and group pairs by `s = de`."

For a coefficient body `a`, `h ≥ 1`, `d ≥ 1` and `G(m) = A(⌊N/m^h⌋)` (`GB`):

* `sum_cut`: a sum whose terms vanish from `M` on may be cut from `N ≥ M` to `M`;
* `row_bt`: `B_h(⌊N/d^h⌋) = Σ_{e<N} A(⌊⌊N/d^h⌋/(e+1)^h⌋)` (`PowerDivisorPrefix.prefix_identity`, then the terms with
  `e ≥ ⌊N/d^h⌋` vanish);
* `row_G`: each such term is `G(d(e+1))` (`ConvolutionAssoc.quo_quo` and `(d(e+1))^h = d^h (e+1)^h`);
* `row_identity`: `B_h(⌊N/d^h⌋) = Σ_{m<N+1} [d ∣ m] sg(m) G(m)`: the multiples `m = dk ≤ Nd` of `d` are reindexed by
  `k ≤ N` (`SumReindex.reindex_eq`, `ConvolutionAssoc.multiples_upto`), the term `k = 0` vanishes, and the terms
  `m > N` vanish (`m^h ≥ m > N`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorRow

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorPrefix
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (riB inst2_riB reindex_eq cM)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (quo_small)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb' congrSg)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Cutting a sum -/

/-- Terms vanishing from `M` on: `Σ_{i<N} g = Σ_{i<M} g` for `M ≤ N`. -/
theorem sum_cut (g : PTm 2) {M N x : PTm n} (hMN : Γ ⊢[PRAAx] le M N)
    (hz : Γ ⊢[PRAAx] Fm.all (inst2 g (Syn.shift M + var 0) (Syn.shift x) ≐ zero)) :
    Γ ⊢[PRAAx] ap2 (sumF g) N x ≐ ap2 (sumF g) M x := by
  refine (congrAp2 (sumF g) (eq_add_of_le hMN) (.eqRefl x)).eqTrans ?_
  refine (sum_split g M (monus N M) x).eqTrans ((congrAdd (.eqRefl _) ?_).eqTrans (add_zero _))
  refine sum_zero_of_all _ _ (.allI ?_) _
  rw [show Syn.shift (pairT M x) = pairT (Syn.shift M) (Syn.shift x) by simp [Syn.shift], inst2_offB]
  exact (congrInst2 g (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans hz.allOpen

/-- `x < (x+1)^h` for `h ≥ 1`. -/
theorem lt_succ_pw {h : PTm n} (hp : Γ ⊢[PRAAx] h ≐ succ (pred h)) (x : PTm n) :
    Γ ⊢[PRAAx] lt x (pw (succ x) h) :=
  le_congr (.eqRefl _) (congrAp2 powF hp.eqSymm (.eqRefl _)) (le_self_pw x (pred h))

theorem pw_pos1 {h : PTm n} (x : PTm n) : Γ ⊢[PRAAx] pw (succ x) h ≐ succ (pred (pw (succ x) h)) :=
  Common.pos_pw (Common.succ_pos x) h

variable (a : PTm 2)

/-! ## The terms `G(m) = A(⌊N/m^h⌋)` -/

/-- `G(m) = A(⌊N/m^h⌋)` over `0 = m`, `1 = ⟨⟨N, h⟩, y⟩`. -/
def GB : PTm 2 :=
  ap2 (sumF (shiftBody a)) (quo (fstT (fstT (var 1))) (pw (var 0) (sndT (fstT (var 1))))) (sndT (var 1))

theorem inst2_GB (m P : PTm n) :
    inst2 (GB a) m P = Apre a (quo (fstT (fstT P)) (pw m (sndT (fstT P)))) (sndT P) := by
  simp [inst2, GB]

theorem GB_at (m N h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (GB a) m (pairT (pairT N h) y) ≐ Apre a (quo N (pw m h)) y := by
  rw [inst2_GB]
  have e1 : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT N h) y)) ≐ N := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have e2 : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT N h) y)) ≐ h := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  exact congrAp2 _ (congrAp2 quoF e1 (congrAp2 powF e2 (.eqRefl _))) (snd_pair _ _)

/-! ## The row as a sum over `e` -/

/-- `B_h(⌊N/d^h⌋) = Σ_{e<N} A(⌊⌊N/d^h⌋/(e+1)^h⌋)`. -/
theorem row_bt {h : PTm n} (hh : Γ ⊢[PRAAx] le one h) (N d y : PTm n) (hdN : Γ ⊢[PRAAx] le (quo N (pw d h)) N) :
    Γ ⊢[PRAAx] Bpre a (quo N (pw d h)) h y ≐
      ap2 (sumF (btB a)) N (pairT (pairT (quo N (pw d h)) h) y) := by
  refine (prefix_identity a hh _ y).eqSymm.eqTrans (sum_cut (btB a) hdN (.allI ?_)).eqSymm
  rw [show Syn.shift (pairT (pairT (quo N (pw d h)) h) y) =
    pairT (pairT (quo (Syn.shift N) (pw (Syn.shift d) (Syn.shift h))) (Syn.shift h)) (Syn.shift y) by simp [Syn.shift],
    show Syn.shift (quo N (pw d h)) = quo (Syn.shift N) (pw (Syn.shift d) (Syn.shift h)) by simp [Syn.shift]]
  have hp : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift h ≐ succ (pred (Syn.shift h)) := by
    have b := (pos_of_one_le hh).shift
    simpa [Fm.shift, Syn.shift] using b
  have hl : (Γ.map Fm.shift) ⊢[PRAAx] lt (quo (Syn.shift N) (pw (Syn.shift d) (Syn.shift h)))
      (pw (succ (quo (Syn.shift N) (pw (Syn.shift d) (Syn.shift h)) + var 0)) (Syn.shift h)) :=
    le_trans (by ipra_le 𝔞 (var 0)) (lt_succ_pw hp _)
  refine (btB_at a _ _ _ _).eqTrans ((congrAp2 _ (quo_small (pw_pos1 _) hl) (.eqRefl _)).eqTrans (sum_zero _ _))

/-- Each term of the row is `G(d(e+1))`. -/
theorem row_G {d h : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (N e y : PTm n) :
    Γ ⊢[PRAAx] Apre a (quo (quo N (pw d h)) (pw (succ e) h)) y ≐ Apre a (quo N (pw (d * succ e) h)) y := by
  have hdp : Γ ⊢[PRAAx] pw d h ≐ succ (pred (pw d h)) :=
    pos_of_one_le (one_le_pw' (le_congr (.eqRefl _) hd.eqSymm (by ipra_le 𝔞 (pred d))) _)
  have q := quo_quo (m := N) hdp (pw_pos1 (h := h) e)
  exact congrAp2 _ (q.eqTrans (congrAp2 quoF (.eqRefl _) (pw_mul_base d (succ e) h).eqSymm)) (.eqRefl _)

/-! ## The row as a sum over the multiples of `d` -/

/-- `sg(dq) = sg(q)` for `d ≥ 1`. -/
theorem sg_mul_pos {d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (q : PTm n) :
    Γ ⊢[PRAAx] sg (d * q) ≐ sg q := by
  refine .orE (lt_or_le zero q) ?_ ?_
  · let C : List (Fm PTm n) := lt zero q :: Γ
    have hq : C ⊢[PRAAx] q ≐ succ (pred q) := pos_of_one_le Prf.hyp0
    have e : C ⊢[PRAAx] d * q ≐ succ (pred (d * q) ) := by
      refine pos_of_one_le ?_
      have p : C ⊢[PRAAx] d * q ≐ succ (pred d * q + pred q) := by
        ipra_lc 𝔞 q * natEq (hd.wk : C ⊢[PRAAx] _) + natEq hq
      exact le_congr (.eqRefl _) p.eqSymm (by ipra_le 𝔞 (pred d * q + pred q))
    exact ((congrSg e).eqTrans (sg_succ _)).eqTrans ((congrSg hq).eqTrans (sg_succ _)).eqSymm
  · let C : List (Fm PTm n) := le q zero :: Γ
    have hq : C ⊢[PRAAx] q ≐ zero := (monus_zero q).eqSymm.eqTrans Prf.hyp0
    exact (congrSg ((congrMul (.eqRefl d) hq).eqTrans (mul_zero d))).eqTrans (congrSg hq).eqSymm

/-- Under the divisibility gate, the quotient reindexes a positive-weight summand. -/
theorem guarded_quotient (G : PTm 2) (i d P : PTm n) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] eqb (rem i d) zero * (sg (quo i d) * inst2 G (d * quo i d) P) ≐
      eqb (rem i d) zero * sg i * inst2 G i P := by
  refine .orE (eqb_cases (rem i d) zero) ?_ ?_
  · have z : (eqb (rem i d) zero ≐ zero) :: Γ ⊢[PRAAx] eqb (rem i d) zero ≐ zero := Prf.hyp0
    exact ((congrMul z (.eqRefl _)).eqTrans (zero_mul _)).eqTrans
      ((congrMul (congrMul z (.eqRefl _)) (.eqRefl _)).eqTrans
        ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))).eqSymm
  · have o : (eqb (rem i d) zero ≐ one) :: Γ ⊢[PRAAx] eqb (rem i d) zero ≐ one := Prf.hyp0
    have r₀ := LeanProofs.IPRA.Foundations.BoundedReflection.eq_of_eqb o
    have dv := ((div_eq hd.wk).eqTrans
      ((congrAdd (.eqRefl _) r₀).eqTrans (add_zero _))).eqSymm
    have s := (sg_mul_pos hd.wk _).eqSymm.eqTrans (congrSg dv)
    exact (congrMul (.eqRefl _) (congrMul s (congrInst2 G dv (.eqRefl _)))).eqTrans (mul_assoc _ _ _).eqSymm

/-- Reindexing by a positive divisor extends the upper bound. -/
theorem reindex_bound (N : PTm n) {d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] le (succ N) (succ (N * d)) :=
  Order.succ_le_succ
    (le_congr (Common.mul_one_right N) (.eqRefl _) (mul_le_mul_left N (Common.one_le_of_pos hd)))

/-- The reindexed summand `sg(k) G(dk)` over `0 = k`, `1 = ⟨d, ⟨⟨N, h⟩, y⟩⟩`. -/
def hB : PTm 2 := sg (var 0) * Syn.subst ![fstT (var 1) * var 0, sndT (var 1)] (GB a)

theorem inst2_hB (k W : PTm n) : inst2 (hB a) k W = sg k * inst2 (GB a) (fstT W * k) (sndT W) := by
  have hg : Syn.subst ![k, W] (Syn.subst ![fstT (var 1) * var 0, sndT (var 1)] (GB a)) =
      inst2 (GB a) (fstT W * k) (sndT W) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext j; fin_cases j <;> simp
  simp only [inst2, hB, PTm.subst_mul, hg]
  simp

/-- The multiple summand `[d ∣ m] sg(m) G(m)` over `0 = m`, `1 = ⟨d, ⟨⟨N, h⟩, y⟩⟩`. -/
def dmB : PTm 2 :=
  eqb (rem (var 0) (fstT (var 1))) zero * sg (var 0) * Syn.subst ![var 0, sndT (var 1)] (GB a)

theorem inst2_dmB (m W : PTm n) :
    inst2 (dmB a) m W = eqb (rem m (fstT W)) zero * sg m * inst2 (GB a) m (sndT W) := by
  have hg : Syn.subst ![m, W] (Syn.subst ![var 0, sndT (var 1)] (GB a)) = inst2 (GB a) m (sndT W) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext j; fin_cases j <;> simp
  simp only [inst2, dmB, PTm.subst_mul, hg]
  simp

theorem hB_at (k d N h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (hB a) k (pairT d (pairT (pairT N h) y)) ≐ sg k * Apre a (quo N (pw (d * k) h)) y := by
  rw [inst2_hB]
  exact congrMul (.eqRefl _) ((congrInst2 (GB a) (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans
    (GB_at a _ _ _ _))

theorem dmB_at (m d N h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (dmB a) m (pairT d (pairT (pairT N h) y)) ≐
      eqb (rem m d) zero * sg m * Apre a (quo N (pw m h)) y := by
  rw [inst2_dmB]
  exact congrMul (congrMul (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _)) (.eqRefl _))
    ((congrInst2 (GB a) (.eqRefl _) (snd_pair _ _)).eqTrans (GB_at a _ _ _ _))

/-- `B_h(⌊N/d^h⌋) = Σ_{m<N+1} [d ∣ m] sg(m) G(m)` for `d ≥ 1`, `h ≥ 1`. -/
theorem row_identity {d h : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hh : Γ ⊢[PRAAx] le one h) (N y : PTm n) :
    Γ ⊢[PRAAx] Bpre a (quo N (pw d h)) h y ≐ ap2 (sumF (dmB a)) (succ N) (pairT d (pairT (pairT N h) y)) := by
  let Z : PTm n := pairT (pairT N h) y
  have hp : Γ ⊢[PRAAx] h ≐ succ (pred h) := pos_of_one_le hh
  have hdp : Γ ⊢[PRAAx] pw d h ≐ succ (pred (pw d h)) :=
    pos_of_one_le (one_le_pw' (le_congr (.eqRefl _) hd.eqSymm (by ipra_le 𝔞 (pred d))) _)
  have hdN : Γ ⊢[PRAAx] le (quo N (pw d h)) N := by
    have q := LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwap.quo_lt' (N := N) hdp
    ipra_le sl q
  -- (1) the row over `e`
  have s1 := row_bt a hh N d y hdN
  -- (2) its terms are `sg(e+1) G(d(e+1))`
  have s2 : Γ ⊢[PRAAx] ap2 (sumF (btB a)) N (pairT (pairT (quo N (pw d h)) h) y) ≐
      ap2 (sumF (shiftBody (hB a))) N (pairT d (pairT (pairT N h) y)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [show Syn.shift (pairT (pairT (quo N (pw d h)) h) y) =
        pairT (pairT (quo (Syn.shift N) (pw (Syn.shift d) (Syn.shift h))) (Syn.shift h)) (Syn.shift y) by
          simp [Syn.shift],
      show Syn.shift (pairT d (pairT (pairT N h) y)) =
        pairT (Syn.shift d) (pairT (pairT (Syn.shift N) (Syn.shift h)) (Syn.shift y)) by simp [Syn.shift],
      inst2_shiftBody]
    let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    have hd' : Λ ⊢[PRAAx] Syn.shift d ≐ succ (pred (Syn.shift d)) := by
      have b : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift d ≐ succ (pred (Syn.shift d)) := by
        simpa [Fm.shift, Syn.shift] using hd.shift
      exact b.wk
    refine (btB_at a _ _ _ _).eqTrans ((row_G a hd' (Syn.shift N) (var 0) (Syn.shift y)).eqTrans ?_)
    exact ((one_mul _).eqSymm.eqTrans (congrMul (sg_succ _).eqSymm (.eqRefl _))).eqTrans (hB_at a _ _ _ _ _).eqSymm
  -- (3) add the vanishing term `k = 0`
  have s3 : Γ ⊢[PRAAx] ap2 (sumF (hB a)) (succ N) (pairT d (pairT (pairT N h) y)) ≐
      ap2 (sumF (shiftBody (hB a))) N (pairT d (pairT (pairT N h) y)) := by
    refine (sum_shift _ _ _).eqTrans ((congrAdd ?_ (.eqRefl _)).eqTrans (zero_add _))
    exact (hB_at a _ _ _ _ _).eqTrans ((congrMul sg_zero (.eqRefl _)).eqTrans (zero_mul _))
  -- (4) reindex the multiples of `d` up to `Nd`
  have cm : Γ ⊢[PRAAx] cM (succ (N * d)) d ≐ succ N :=
    (multiples_upto (Q := N * d) hd).eqTrans (congrSucc (quo_mul hd (mul_comm _ _)))
  have s4 : Γ ⊢[PRAAx] ap2 (sumF (riB (hB a))) (succ (N * d)) (pairT d (pairT d (pairT (pairT N h) y))) ≐
      ap2 (sumF (hB a)) (succ N) (pairT d (pairT (pairT N h) y)) :=
    (reindex_eq (hB a) (succ (N * d)) hd).eqTrans (congrAp2 _ cm (.eqRefl _))
  -- (5) the reindexed terms are `[d ∣ m] sg(m) G(m)`
  have s5 : Γ ⊢[PRAAx] ap2 (sumF (riB (hB a))) (succ (N * d)) (pairT d (pairT d (pairT (pairT N h) y))) ≐
      ap2 (sumF (dmB a)) (succ (N * d)) (pairT d (pairT (pairT N h) y)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [show Syn.shift (pairT d (pairT d (pairT (pairT N h) y))) =
        pairT (Syn.shift d) (pairT (Syn.shift d) (pairT (pairT (Syn.shift N) (Syn.shift h)) (Syn.shift y))) by
          simp [Syn.shift],
      show Syn.shift (pairT d (pairT (pairT N h) y)) =
        pairT (Syn.shift d) (pairT (pairT (Syn.shift N) (Syn.shift h)) (Syn.shift y)) by simp [Syn.shift],
      inst2_riB]
    let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ (N * d))) :: Γ.map Fm.shift
    have hd' : Λ ⊢[PRAAx] Syn.shift d ≐ succ (pred (Syn.shift d)) := by
      have b : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift d ≐ succ (pred (Syn.shift d)) := by
        simpa [Fm.shift, Syn.shift] using hd.shift
      exact b.wk
    have e0 : Λ ⊢[PRAAx] eqb (rem (var 0) (fstT (pairT (Syn.shift d)
        (pairT (Syn.shift d) (pairT (pairT (Syn.shift N) (Syn.shift h)) (Syn.shift y)))))) zero ≐
        eqb (rem (var 0) (Syn.shift d)) zero :=
      congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _)
    have eq0 : Λ ⊢[PRAAx] quo (var 0) (fstT (pairT (Syn.shift d)
        (pairT (Syn.shift d) (pairT (pairT (Syn.shift N) (Syn.shift h)) (Syn.shift y))))) ≐ quo (var 0) (Syn.shift d) :=
      congrAp2 quoF (.eqRefl _) (fst_pair _ _)
    refine (congrMul e0 ((congrInst2 (hB a) eq0 (snd_pair _ _)).eqTrans (hB_at a _ _ _ _ _))).eqTrans ?_
    refine Prf.eqTrans ?_ (dmB_at a _ _ _ _ _).eqSymm
    have g₁ := GB_at (Γ := Λ) a (Syn.shift d * quo (var 0) (Syn.shift d))
      (Syn.shift N) (Syn.shift h) (Syn.shift y)
    have g₂ := GB_at (Γ := Λ) a (var 0) (Syn.shift N) (Syn.shift h) (Syn.shift y)
    exact (congrMul (.eqRefl _) (congrMul (.eqRefl _) g₁.eqSymm)).eqTrans
      ((guarded_quotient (GB a) (var 0) (Syn.shift d) _ hd').eqTrans (congrMul (.eqRefl _) g₂))
  -- (6) the terms beyond `N` vanish
  have hNd := reindex_bound N hd
  have s6 : Γ ⊢[PRAAx] ap2 (sumF (dmB a)) (succ (N * d)) (pairT d (pairT (pairT N h) y)) ≐
      ap2 (sumF (dmB a)) (succ N) (pairT d (pairT (pairT N h) y)) := by
    refine sum_cut (dmB a) hNd (.allI ?_)
    rw [show Syn.shift (pairT d (pairT (pairT N h) y)) =
        pairT (Syn.shift d) (pairT (pairT (Syn.shift N) (Syn.shift h)) (Syn.shift y)) by simp [Syn.shift],
      show Syn.shift (succ N) = succ (Syn.shift N) by simp [Syn.shift]]
    have hp' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift h ≐ succ (pred (Syn.shift h)) := by
      simpa [Fm.shift, Syn.shift] using hp.shift
    have hl : (Γ.map Fm.shift) ⊢[PRAAx] lt (Syn.shift N) (pw (succ (Syn.shift N) + var 0) (Syn.shift h)) := by
      have l := lt_succ_pw hp' (Syn.shift N + var 0)
      have e : (Γ.map Fm.shift) ⊢[PRAAx] succ (Syn.shift N + var 0) ≐ succ (Syn.shift N) + var 0 := by
        ipra_ring
      exact le_trans (by ipra_le 𝔞 (var 0)) (le_congr (.eqRefl _) (congrAp2 powF (.eqRefl _) e) l)
    have hq : (Γ.map Fm.shift) ⊢[PRAAx] pw (succ (Syn.shift N) + var 0) (Syn.shift h) ≐
        succ (pred (pw (succ (Syn.shift N) + var 0) (Syn.shift h))) := by
      have e : (Γ.map Fm.shift) ⊢[PRAAx] succ (Syn.shift N) + var 0 ≐ succ (Syn.shift N + var 0) := by
        ipra_ring
      exact (congrAp2 powF (.eqRefl _) e).eqTrans ((pw_pos1 _).eqTrans
        (congrSucc (congrPred (congrAp2 powF (.eqRefl _) e.eqSymm))))
    refine (dmB_at a _ _ _ _ _).eqTrans ?_
    refine (congrMul (.eqRefl _) ((congrAp2 _ (quo_small hq hl) (.eqRefl _)).eqTrans (sum_zero _ _))).eqTrans ?_
    exact mul_zero _
  exact s1.eqTrans (s2.eqTrans (s3.eqSymm.eqTrans (s4.eqSymm.eqTrans (s5.eqTrans s6))))

end LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorRow
