import IPRADerivations.AnalyticNumberTheory.DivisorSplit
import IPRADerivations.AnalyticNumberTheory.PowerDivisorInversion

/-!
# Divisor sums over a coprime product (`robin_ipra_research_2026-11-19`, multiplicativity of `σ`)

For `m, N ≥ 1` with `gcd(m, N) = 1` and any body `g(d, y)`:

  `Σ_{d ≤ mN, d ∣ mN} g(d) = Σ_{a ≤ m, a ∣ m} Σ_{b ≤ N, b ∣ N} g(ab)`                       (`divisor_factor`)

The right side is rewritten as the triple sum `Σ_a Σ_b Σ_{d ≤ mN} [a ∣ m][b ∣ N][ab = d] g(d)` (the delta sum
`Core/Fubini.sum_delta`, since `ab ≤ mN`), exchanged twice by `Core/Fubini.fubini` to `Σ_d Σ_a Σ_b`, and each column is
`g(d) Σ_a Σ_b [d ∣ mN][a = gcd(d,m)][b = d/gcd(d,m)] = [d ∣ mN] g(d)` by `DivisorSplit.cnt_pt` (the term `d = 0`
vanishes on both sides).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.DivisorFactor

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorSplit
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_le' one_le_of_pos coprime_dvd_left gcd_comm_one)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable (g : PTm 2)

/-! ## The bodies, at the parameter `X = ⟨⟨m, N⟩, y⟩` -/

abbrev Xp (m N y : PTm n) : PTm n := pairT (pairT m N) y

/-- `[a ∣ m][b ∣ N][ab = d] g(d)` over `0 = a`, `1 = b`, `2 = d`, `3 = m`, `4 = N`, `5 = y`. -/
def cC : PTm 6 := eqb (rem (var 3) (var 0)) zero * eqb (rem (var 4) (var 1)) zero * eqb (var 0 * var 1) (var 2) *
  Syn.subst ![var 2, var 5] g

abbrev cval (a b d m N y : PTm n) : PTm n :=
  eqb (rem m a) zero * eqb (rem N b) zero * eqb (a * b) d * inst2 g d y

theorem cC_eval (a b d m N y : PTm n) : Syn.subst ![a, b, d, m, N, y] (cC g) = cval g a b d m N y := by
  simp only [cC, PTm.subst_mul, subst_eqb, subst_ap2, Syn.subst_var, inst2, Syn.subst_subst,
    ConciseIPRA.PTm.subst_zero]
  refine congrArg _ ?_
  congr 1; funext k; fin_cases k <;> rfl

/-- The inner body over `0 = b`, `1 = d`, `2 = ⟨a, X⟩`. -/
def aIn : PTm 3 := Syn.subst ![fstT (var 2), var 0, var 1, fstT (fstT (sndT (var 2))), sndT (fstT (sndT (var 2))),
  sndT (sndT (var 2))] (cC g)

theorem aIn_at (a b d m N y : PTm n) :
    Γ ⊢[PRAAx] inst3 (aIn g) b d (pairT a (Xp m N y)) ≐ cval g a b d m N y := by
  have e : inst3 (aIn g) b d (pairT a (Xp m N y)) = Syn.subst ![fstT (pairT a (Xp m N y)), b, d,
      fstT (fstT (sndT (pairT a (Xp m N y)))), sndT (fstT (sndT (pairT a (Xp m N y)))),
      sndT (sndT (pairT a (Xp m N y)))] (cC g) := by
    simp only [inst3, aIn, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  rw [e, ← cC_eval]
  have e1 : Γ ⊢[PRAAx] fstT (pairT a (Xp m N y)) ≐ a := fst_pair _ _
  have e2 : Γ ⊢[PRAAx] fstT (fstT (sndT (pairT a (Xp m N y)))) ≐ m :=
    (congrFst ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))).eqTrans (fst_pair _ _)
  have e3 : Γ ⊢[PRAAx] sndT (fstT (sndT (pairT a (Xp m N y)))) ≐ N :=
    (congrSnd ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))).eqTrans (snd_pair _ _)
  have e4 : Γ ⊢[PRAAx] sndT (sndT (pairT a (Xp m N y))) ≐ y := (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  exact Prf.eqCongr (cC g) fun k => by
    fin_cases k
    · exact e1
    · exact .eqRefl _
    · exact .eqRefl _
    · exact e2
    · exact e3
    · exact e4

/-- `Σ_{b<N+1} aIn(b, d, ⟨a, X⟩)` over `0 = a`, `1 = d`, `2 = X`. -/
def aOut : PTm 3 := ap2 (sumF (colB (aIn g))) (succ (sndT (fstT (var 2)))) (pairT (var 1) (pairT (var 0) (var 2)))

theorem inst3_aOut (a d X : PTm n) :
    inst3 (aOut g) a d X = ap2 (sumF (colB (aIn g))) (succ (sndT (fstT X))) (pairT d (pairT a X)) := by
  simp [inst3, aOut]

/-- The left body `[d ∣ mN] g(d)` over `0 = d`, `1 = X`. -/
def lB : PTm 2 := eqb (rem (fstT (fstT (var 1)) * sndT (fstT (var 1))) (var 0)) zero * Syn.subst ![var 0, sndT (var 1)] g

/-- The inner right body `[b ∣ N] g(ab)` over `0 = b`, `1 = ⟨a, X⟩`. -/
def riB : PTm 2 := eqb (rem (sndT (fstT (sndT (var 1)))) (var 0)) zero *
  Syn.subst ![fstT (var 1) * var 0, sndT (sndT (var 1))] g

/-- The outer right body `[a ∣ m] Σ_{b<N+1} [b ∣ N] g(ab)` over `0 = a`, `1 = X`. -/
def rB : PTm 2 := eqb (rem (fstT (fstT (var 1))) (var 0)) zero *
  ap2 (sumF (riB g)) (succ (sndT (fstT (var 1)))) (pairT (var 0) (var 1))

theorem lB_at (d m N y : PTm n) :
    Γ ⊢[PRAAx] inst2 (lB g) d (Xp m N y) ≐ eqb (rem (m * N) d) zero * inst2 g d y := by
  have e : inst2 (lB g) d (Xp m N y) = eqb (rem (fstT (fstT (Xp m N y)) * sndT (fstT (Xp m N y))) d) zero *
      inst2 g d (sndT (Xp m N y)) := by
    simp only [inst2, lB, PTm.subst_mul, subst_reindex2]; simp
  rw [e]
  have e1 : Γ ⊢[PRAAx] fstT (fstT (Xp m N y)) ≐ m := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have e2 : Γ ⊢[PRAAx] sndT (fstT (Xp m N y)) ≐ N := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  exact congrMul (congrEqb' (congrAp2 remF (congrMul e1 e2) (.eqRefl _)) (.eqRefl _))
    (congrInst2 g (.eqRefl _) (snd_pair _ _))

theorem riB_at (b a m N y : PTm n) :
    Γ ⊢[PRAAx] inst2 (riB g) b (pairT a (Xp m N y)) ≐ eqb (rem N b) zero * inst2 g (a * b) y := by
  have e : inst2 (riB g) b (pairT a (Xp m N y)) = eqb (rem (sndT (fstT (sndT (pairT a (Xp m N y))))) b) zero *
      inst2 g (fstT (pairT a (Xp m N y)) * b) (sndT (sndT (pairT a (Xp m N y)))) := by
    simp only [inst2, riB, PTm.subst_mul, subst_reindex2]; simp
  rw [e]
  have e3 : Γ ⊢[PRAAx] sndT (fstT (sndT (pairT a (Xp m N y)))) ≐ N :=
    (congrSnd ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))).eqTrans (snd_pair _ _)
  exact congrMul (congrEqb' (congrAp2 remF e3 (.eqRefl _)) (.eqRefl _))
    (congrInst2 g (congrMul (fst_pair _ _) (.eqRefl _)) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))

theorem rB_at (a m N y : PTm n) :
    Γ ⊢[PRAAx] inst2 (rB g) a (Xp m N y) ≐
      eqb (rem m a) zero * ap2 (sumF (riB g)) (succ N) (pairT a (Xp m N y)) := by
  have e : inst2 (rB g) a (Xp m N y) = eqb (rem (fstT (fstT (Xp m N y))) a) zero *
      ap2 (sumF (riB g)) (succ (sndT (fstT (Xp m N y)))) (pairT a (Xp m N y)) := by simp [inst2, rB]
  rw [e]
  have e1 : Γ ⊢[PRAAx] fstT (fstT (Xp m N y)) ≐ m := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have e2 : Γ ⊢[PRAAx] sndT (fstT (Xp m N y)) ≐ N := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  exact congrMul (congrEqb' (congrAp2 remF e1 (.eqRefl _)) (.eqRefl _)) (congrAp2 _ (congrSucc e2) (.eqRefl _))

/-! ## Step A: the delta sum, for fixed `a, b` -/

/-- `[a ∣ m] ([b ∣ N] g(ab)) = Σ_{d<mN+1} [a ∣ m][b ∣ N][ab = d] g(d)` for `a ≤ m`, `b ≤ N`. -/
theorem step_a {a b m N y : PTm n} (ha : Γ ⊢[PRAAx] lt a (succ m)) (hb : Γ ⊢[PRAAx] lt b (succ N)) :
    Γ ⊢[PRAAx] eqb (rem m a) zero * (eqb (rem N b) zero * inst2 g (a * b) y) ≐
      ap2 (sumF (rowB (aIn g))) (succ (m * N)) (pairT b (pairT a (Xp m N y))) := by
  have hab : Γ ⊢[PRAAx] lt (a * b) (succ (m * N)) := by
    have l := le_mul_mono (by ipra_le sl ha : Γ ⊢[PRAAx] le a m) (by ipra_le sl hb : Γ ⊢[PRAAx] le b N)
    ipra_le sl l
  have dl := sum_delta (Γ := Γ) g (x := y) hab
  have cm := sum_const_mul (Γ := Γ) (dB g) (succ (m * N)) (eqb (rem m a) zero * eqb (rem N b) zero) (pairT (a * b) y)
  refine Prf.eqTrans ?_ (Prf.eqTrans cm.eqSymm ?_)
  · refine (by ipra_ring :
      Γ ⊢[PRAAx] eqb (rem m a) zero * (eqb (rem N b) zero * inst2 g (a * b) y) ≐
        eqb (rem m a) zero * eqb (rem N b) zero * inst2 g (a * b) y).eqTrans ?_
    exact congrMul (.eqRefl _) dl.eqSymm
  · refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [inst2_cmB, inst2_rowB, inst2_dB, shift_pairT]
    let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ (m * N))) :: Γ.map Fm.shift
    have f1 : Λ ⊢[PRAAx] fstT (pairT (Syn.shift (eqb (rem m a) zero * eqb (rem N b) zero))
        (pairT (Syn.shift (a * b)) (Syn.shift y))) ≐ Syn.shift (eqb (rem m a) zero * eqb (rem N b) zero) := fst_pair _ _
    have f2 : Λ ⊢[PRAAx] sndT (pairT (Syn.shift (eqb (rem m a) zero * eqb (rem N b) zero))
        (pairT (Syn.shift (a * b)) (Syn.shift y))) ≐ pairT (Syn.shift (a * b)) (Syn.shift y) := snd_pair _ _
    have l : Λ ⊢[PRAAx] fstT (pairT (Syn.shift (eqb (rem m a) zero * eqb (rem N b) zero))
        (pairT (Syn.shift (a * b)) (Syn.shift y))) *
        (eqb (fstT (sndT (pairT (Syn.shift (eqb (rem m a) zero * eqb (rem N b) zero))
          (pairT (Syn.shift (a * b)) (Syn.shift y))))) (var 0) *
          inst2 g (var 0) (sndT (sndT (pairT (Syn.shift (eqb (rem m a) zero * eqb (rem N b) zero))
            (pairT (Syn.shift (a * b)) (Syn.shift y)))))) ≐
        Syn.shift (eqb (rem m a) zero * eqb (rem N b) zero) * (eqb (Syn.shift (a * b)) (var 0) *
          inst2 g (var 0) (Syn.shift y)) :=
      congrMul f1 (congrMul (congrEqb' ((congrFst f2).eqTrans (fst_pair _ _)) (.eqRefl _))
        (congrInst2 g (.eqRefl _) ((congrSnd f2).eqTrans (snd_pair _ _))))
    refine l.eqTrans (Prf.eqTrans ?_ ((congrInst3 (aIn g) (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans
      (aIn_at g (Γ := Λ) _ _ _ _ _ _)).eqSymm)
    have s1 : Syn.shift (eqb (rem m a) zero * eqb (rem N b) zero) =
        eqb (rem (Syn.shift m) (Syn.shift a)) zero * eqb (rem (Syn.shift N) (Syn.shift b)) zero := by simp [Syn.shift]
    have s2 : Syn.shift (a * b) = Syn.shift a * Syn.shift b := by simp [Syn.shift]
    rw [s1, s2]
    ipra_ring

/-! ## Shifting the hypotheses under a binder -/

theorem pos_sh {x : PTm n} (h : Γ ⊢[PRAAx] x ≐ succ (pred x)) :
    Γ.map Fm.shift ⊢[PRAAx] Syn.shift x ≐ succ (pred (Syn.shift x)) := by
  simpa [Fm.shift, Syn.shift] using h.shift

theorem gcd_sh {m N : PTm n} (h : Γ ⊢[PRAAx] gcd m N ≐ one) :
    Γ.map Fm.shift ⊢[PRAAx] gcd (Syn.shift m) (Syn.shift N) ≐ one := by
  have e := h.shift
  simp only [Fm.shift, Fm.subst_eq, subst_ex2, subst_ap2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e
  exact e

/-- To prove a law on divisors of positive coprime inputs, use positivity and coprimality of each pair. -/
theorem on_coprime_divisor_pairs {m N : PTm n} {P : Fm PTm (n + 2)}
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hc : Γ ⊢[PRAAx] gcd m N ≐ one)
    (atPair : let a : PTm (n + 2) := var 1; let b : PTm (n + 2) := var 0
      let Δ := dvd b (Syn.shift (Syn.shift N)) :: dvd a (Syn.shift (Syn.shift m)) :: (Γ.map Fm.shift).map Fm.shift
      (Δ ⊢[PRAAx] le one a) → (Δ ⊢[PRAAx] le one b) → (Δ ⊢[PRAAx] gcd a b ≐ one) → (Δ ⊢[PRAAx] P)) :
    Γ ⊢[PRAAx] Fm.all (Fm.all (dvd (var 1) (Syn.shift (Syn.shift m)) ⟶
      dvd (var 0) (Syn.shift (Syn.shift N)) ⟶ P)) := by
  refine .allI (.allI (.impI (.impI ?_)))
  let m' := Syn.shift (Syn.shift m)
  let N' := Syn.shift (Syn.shift N)
  let Δ := dvd (var 0) N' :: dvd (var 1) m' :: (Γ.map Fm.shift).map Fm.shift
  have hN' : Δ ⊢[PRAAx] N' ≐ succ (pred N') := (pos_sh (pos_sh hN)).wk.wk
  have hc' : Δ ⊢[PRAAx] gcd m' N' ≐ one := (gcd_sh (gcd_sh hc)).wk.wk
  have pa : Δ ⊢[PRAAx] var 1 ≐ succ (pred (var 1)) := pos_of_dvd (pos_sh (pos_sh hm)).wk.wk Prf.hyp1
  have pb : Δ ⊢[PRAAx] var 0 ≐ succ (pred (var 0)) := pos_of_dvd hN' Prf.hyp0
  have hba := coprime_dvd_left pb Prf.hyp0 (gcd_comm_one hN' (coprime_dvd_left pa Prf.hyp1 hc'))
  exact atPair (one_le_of_pos pa) (one_le_of_pos pb) (gcd_comm_one pa hba)

theorem lt_sh {a b : PTm n} (h : Γ ⊢[PRAAx] lt a b) : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift b) := by
  have e := h.shift
  simp only [Fm.shift, lt, subst_le, ConciseIPRA.PTm.subst_succ] at e
  exact e

theorem shift_succ_mul (m N : PTm n) : Syn.shift (succ (m * N)) = succ (Syn.shift m * Syn.shift N) := by
  simp [Syn.shift]

theorem shift_K (m a : PTm n) : Syn.shift (eqb (rem m a) zero) = eqb (rem (Syn.shift m) (Syn.shift a)) zero := by
  simp [Syn.shift]

/-! ## Step B: one row `a` -/

/-- `[a ∣ m] Σ_{b<N+1} [b ∣ N] g(ab) = Σ_{d<mN+1} Σ_{b<N+1} [a ∣ m][b ∣ N][ab = d] g(d)` for `a ≤ m`. -/
theorem step_b {a m N y : PTm n} (ha : Γ ⊢[PRAAx] lt a (succ m)) :
    Γ ⊢[PRAAx] inst2 (rB g) a (Xp m N y) ≐ ap2 (sumF (rowB (aOut g))) (succ (m * N)) (pairT a (Xp m N y)) := by
  refine (rB_at g _ _ _ _).eqTrans ?_
  refine (sum_const_mul (riB g) (succ N) (eqb (rem m a) zero) (pairT a (Xp m N y))).eqSymm.eqTrans ?_
  -- each term is a delta sum over `d`
  have r1 : Γ ⊢[PRAAx] ap2 (sumF (cmB (riB g))) (succ N) (pairT (eqb (rem m a) zero) (pairT a (Xp m N y))) ≐
      ap2 (sumF (oB (aIn g))) (succ N) (pairT (succ (m * N)) (pairT a (Xp m N y))) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [inst2_cmB, shift_pairT, shift_K, shift_succ_mul]
    let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift
    have hb : Λ ⊢[PRAAx] lt (var 0) (succ (Syn.shift N)) := by
      have b : Λ ⊢[PRAAx] lt (var 0) (Syn.shift (succ N)) := Prf.hyp0
      rw [show Syn.shift (succ N) = succ (Syn.shift N) by simp [Syn.shift]] at b
      exact b
    have ha' : Λ ⊢[PRAAx] lt (Syn.shift a) (succ (Syn.shift m)) := by
      have b := lt_sh ha; simp only [Syn.shift, ConciseIPRA.PTm.subst_succ] at b; exact b.wk
    have e1 : Λ ⊢[PRAAx] fstT (pairT (eqb (rem (Syn.shift m) (Syn.shift a)) zero)
        (pairT (Syn.shift a) (Xp (Syn.shift m) (Syn.shift N) (Syn.shift y)))) ≐
        eqb (rem (Syn.shift m) (Syn.shift a)) zero := fst_pair _ _
    refine (congrMul e1 ((congrInst2 (riB g) (.eqRefl _) (snd_pair _ _)).eqTrans (riB_at g _ _ _ _ _))).eqTrans ?_
    exact (step_a g ha' hb).eqTrans (oB_at (aIn g) _ _ _).eqSymm
  refine r1.eqTrans ((fubini (aIn g) (succ N) (succ (m * N)) (pairT a (Xp m N y))).eqTrans ?_)
  -- the columns are the outer body `aOut`
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [inst2_pB, inst2_rowB, inst3_aOut, shift_pairT]
  have b1 : (lt (var 0) (Syn.shift (succ (m * N))) :: Γ.map Fm.shift) ⊢[PRAAx]
      fstT (pairT (Syn.shift (succ N)) (pairT (Syn.shift a) (Xp (Syn.shift m) (Syn.shift N) (Syn.shift y)))) ≐
      succ (sndT (fstT (sndT (pairT (Syn.shift a) (Xp (Syn.shift m) (Syn.shift N) (Syn.shift y)))))) := by
    refine (fst_pair _ _).eqTrans ?_
    have e : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
    rw [e]
    exact congrSucc ((congrSnd ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))).eqTrans (snd_pair _ _)).eqSymm
  refine congrAp2 _ b1 (congrPairT (.eqRefl _) ((snd_pair _ _).eqTrans ?_))
  exact (congrPairT (fst_pair _ _) (snd_pair _ _)).eqSymm

/-! ## Step D: one column `d` -/

theorem inst2_v1 {k : ℕ} (i z : PTm k) : inst2 (var 1 : PTm 2) i z = z := by simp [inst2]

/-- The column sum `Σ_{a<m+1} Σ_{b<N+1} c(a, b, d)` collapses once `c(a, b, d) = [b = B₀][a = A₀] L`. -/
theorem col_collapse {d m N y A0 B0 L : PTm n} (hA : Γ ⊢[PRAAx] lt A0 (succ m)) (hB : Γ ⊢[PRAAx] lt B0 (succ N))
    (pt : (Δ : List (Fm PTm (n + 2))) → ((Γ.map Fm.shift).map Fm.shift ⊆ Δ) →
      (Δ ⊢[PRAAx] cval g (var 1) (var 0) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift m))
        (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift y)) ≐
      eqb (Syn.shift (Syn.shift B0)) (var 0) * (eqb (Syn.shift (Syn.shift A0)) (var 1) * Syn.shift (Syn.shift L)))) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (aOut g))) (succ m) (pairT d (Xp m N y)) ≐ L := by
  -- the inner sums
  have inner : Γ ⊢[PRAAx] ap2 (sumF (colB (aOut g))) (succ m) (pairT d (Xp m N y)) ≐
      ap2 (sumF (dB (var 1))) (succ m) (pairT A0 L) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [inst2_colB, inst3_aOut, inst2_dB, inst2_v1, shift_pairT]
    let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift
    have hB' : Λ ⊢[PRAAx] lt (Syn.shift B0) (succ (Syn.shift N)) := by
      have b := lt_sh hB; simp only [Syn.shift, ConciseIPRA.PTm.subst_succ] at b; exact b.wk
    have e1 : Λ ⊢[PRAAx] ap2 (sumF (colB (aIn g))) (succ (sndT (fstT (sndT (pairT (Syn.shift d)
        (Xp (Syn.shift m) (Syn.shift N) (Syn.shift y)))))))
        (pairT (fstT (pairT (Syn.shift d) (Xp (Syn.shift m) (Syn.shift N) (Syn.shift y))))
          (pairT (var 0) (sndT (pairT (Syn.shift d) (Xp (Syn.shift m) (Syn.shift N) (Syn.shift y)))))) ≐
        ap2 (sumF (dB (var 1))) (succ (Syn.shift N))
          (pairT (Syn.shift B0) (eqb (Syn.shift A0) (var 0) * Syn.shift L)) := by
      refine (congrAp2 _ (congrSucc ((congrSnd ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))).eqTrans
        (snd_pair _ _))) (congrPairT (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _)))).eqTrans ?_
      refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
      simp only [inst2_colB, inst2_dB, inst2_v1, shift_pairT, Syn.shift_var, Fin.succ_zero_eq_one]
      let Λ' : List (Fm PTm (n + 2)) := lt (var 0) (Syn.shift (succ (Syn.shift N))) :: Λ.map Fm.shift
      have p := pt Λ' (fun _ hx => List.mem_cons_of_mem _ (by
        simp only [Λ, List.map_cons]; exact List.mem_cons_of_mem _ hx))
      refine (congrInst3 (aIn g) (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans
        ((aIn_at g _ _ _ _ _ _).eqTrans (p.eqTrans ?_))
      have s1 : Syn.shift (eqb (Syn.shift A0) (var 0) * Syn.shift L) =
          eqb (Syn.shift (Syn.shift A0)) (var 1) * Syn.shift (Syn.shift L) := by simp [Syn.shift]
      rw [s1]
      exact congrMul (congrEqb' (fst_pair _ _).eqSymm (.eqRefl _)) (snd_pair _ _).eqSymm
    refine e1.eqTrans ((sum_delta (var 1) hB').eqTrans ?_)
    rw [inst2_v1]
    exact congrMul (congrEqb' (fst_pair _ _).eqSymm (.eqRefl _)) (snd_pair _ _).eqSymm
  refine inner.eqTrans ((sum_delta (var 1) hA).eqTrans ?_)
  rw [inst2_v1]
  exact .eqRefl _

/-! ## The three kinds of column -/

theorem shift_gcd (a b : PTm n) : Syn.shift (gcd a b) = gcd (Syn.shift a) (Syn.shift b) := by
  simp only [Syn.shift, subst_ex2, ConciseIPRA.PTm.subst_succ]

theorem ind_sh0 {d m N : PTm n} (h : Γ ⊢[PRAAx] eqb (rem (m * N) d) zero ≐ zero) :
    Γ.map Fm.shift ⊢[PRAAx] eqb (rem (Syn.shift m * Syn.shift N) (Syn.shift d)) zero ≐ zero := by
  have e := h.shift
  simp only [Fm.shift, Fm.subst_eq, subst_eqb, subst_ap2, PTm.subst_mul, ConciseIPRA.PTm.subst_zero] at e
  exact e

theorem eq_sh0 {d : PTm n} (h : Γ ⊢[PRAAx] d ≐ zero) : Γ.map Fm.shift ⊢[PRAAx] Syn.shift d ≐ zero := by
  have e := h.shift
  simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_zero] at e
  exact e

theorem shift2_zero : Syn.shift (Syn.shift (zero : PTm n)) = zero := by simp [Syn.shift]

/-- A column `d ≥ 1` with `d ∤ mN` vanishes. -/
theorem col_none {d m N y : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hc : Γ ⊢[PRAAx] gcd m N ≐ one)
    (h0 : Γ ⊢[PRAAx] eqb (rem (m * N) d) zero ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (aOut g))) (succ m) (pairT d (Xp m N y)) ≐ inst2 (lB g) d (Xp m N y) := by
  refine (col_collapse g (A0 := zero) (B0 := zero) (L := zero) (by ipra_le 𝔞 m) (by ipra_le 𝔞 N) ?_).eqTrans ?_
  · intro Δ s
    rw [shift2_zero]
    have hd2 := (pos_sh (pos_sh hd)).weaken s
    have hm2 := (pos_sh (pos_sh hm)).weaken s
    have hN2 := (pos_sh (pos_sh hN)).weaken s
    have hc2 := (gcd_sh (gcd_sh hc)).weaken s
    have h02 := (ind_sh0 (ind_sh0 h0)).weaken s
    have cn := cnt_pt hd2 hm2 hN2 hc2 (var 1) (var 0)
    have z : Δ ⊢[PRAAx] cval g (var 1) (var 0) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift m))
        (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift y)) ≐ zero :=
      (congrMul (cn.eqTrans ((congrMul h02 (.eqRefl _)).eqTrans (zero_mul _))) (.eqRefl _)).eqTrans (zero_mul _)
    exact z.eqTrans (by ipra_ring)
  · exact ((lB_at g _ _ _ _).eqTrans ((congrMul h0 (.eqRefl _)).eqTrans (zero_mul _))).eqSymm

/-- A column `d ≥ 1` with `d ∣ mN` is `g(d)`. -/
theorem col_some {d m N y : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hc : Γ ⊢[PRAAx] gcd m N ≐ one)
    (h1 : Γ ⊢[PRAAx] eqb (rem (m * N) d) zero ≐ one) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (aOut g))) (succ m) (pairT d (Xp m N y)) ≐ inst2 (lB g) d (Xp m N y) := by
  obtain ⟨h0a, h0b, -⟩ := split_exists hd hc (eq_of_eqb h1)
  have hA : Γ ⊢[PRAAx] lt (gcd d m) (succ m) := by
    have l := dvd_le' (pos_of_dvd hm h0a) h0a hm
    ipra_le sl l
  have hB : Γ ⊢[PRAAx] lt (quo d (gcd d m)) (succ N) := by
    have l := dvd_le' (pos_of_dvd hN h0b) h0b hN
    ipra_le sl l
  refine (col_collapse g (A0 := gcd d m) (B0 := quo d (gcd d m)) (L := eqb (rem (m * N) d) zero * inst2 g d y)
    hA hB ?_).eqTrans (lB_at g _ _ _ _).eqSymm
  intro Δ s
  have eA : Syn.shift (Syn.shift (gcd d m)) = gcd (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift m)) := by
    rw [shift_gcd, shift_gcd]
  have eB : Syn.shift (Syn.shift (quo d (gcd d m))) =
      quo (Syn.shift (Syn.shift d)) (gcd (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift m))) := by
    rw [← eA]; simp [Syn.shift]
  have eL : Syn.shift (Syn.shift (eqb (rem (m * N) d) zero * inst2 g d y)) =
      eqb (rem (Syn.shift (Syn.shift m) * Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift d))) zero *
        inst2 g (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift y)) := by simp [Syn.shift]
  rw [eA, eB, eL]
  have hd2 := (pos_sh (pos_sh hd)).weaken s
  have hm2 := (pos_sh (pos_sh hm)).weaken s
  have hN2 := (pos_sh (pos_sh hN)).weaken s
  have hc2 := (gcd_sh (gcd_sh hc)).weaken s
  have cn := cnt_pt hd2 hm2 hN2 hc2 (var 1) (var 0)
  refine (congrMul (cn.eqTrans (congrMul (.eqRefl _) (congrMul (eqb_comm' _ _) (eqb_comm' _ _)))) (.eqRefl _)).eqTrans ?_
  ipra_ring

/-- The column `d = 0` vanishes. -/
theorem col_zero {d m N y : PTm n} (hz : Γ ⊢[PRAAx] d ≐ zero) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (aOut g))) (succ m) (pairT d (Xp m N y)) ≐ inst2 (lB g) d (Xp m N y) := by
  refine (col_collapse g (A0 := zero) (B0 := zero) (L := zero) (by ipra_le 𝔞 m) (by ipra_le 𝔞 N) ?_).eqTrans ?_
  · intro Δ s
    rw [shift2_zero]
    have hz2 := (eq_sh0 (eq_sh0 hz)).weaken s
    have hm2 := (pos_sh (pos_sh hm)).weaken s
    have hN2 := (pos_sh (pos_sh hN)).weaken s
    have z : Δ ⊢[PRAAx] cval g (var 1) (var 0) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift m))
        (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift y)) ≐ zero := by
      refine .orE (tri (eqb_cases (rem (Syn.shift (Syn.shift m)) (var 1)) zero)
        (eqb_cases (rem (Syn.shift (Syn.shift N)) (var 0)) zero)
        (eqb_cases (var 1 * var 0) (Syn.shift (Syn.shift d)))) ?_ ?_
      · exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
      · let P : Fm PTm (n + 2) := (eqb (rem (Syn.shift (Syn.shift m)) (var 1)) zero ≐ one) ⋏
          ((eqb (rem (Syn.shift (Syn.shift N)) (var 0)) zero ≐ one) ⋏ (eqb (var 1 * var 0) (Syn.shift (Syn.shift d)) ≐ one))
        have hp : (P :: Δ) ⊢[PRAAx] P := Prf.hyp0
        have fa : (P :: Δ) ⊢[PRAAx] dvd (var 1) (Syn.shift (Syn.shift m)) := eq_of_eqb (Prf.andE₁ hp)
        have fb : (P :: Δ) ⊢[PRAAx] dvd (var 0) (Syn.shift (Syn.shift N)) := eq_of_eqb (Prf.andE₁ (Prf.andE₂ hp))
        have fab : (P :: Δ) ⊢[PRAAx] var 1 * var 0 ≐ Syn.shift (Syn.shift d) := eq_of_eqb (Prf.andE₂ (Prf.andE₂ hp))
        have pab := pos_mul (pos_of_dvd hm2.wk fa) (pos_of_dvd hN2.wk fb)
        exact succ_ne_zero' _ (pab.eqSymm.eqTrans (fab.eqTrans hz2.wk))
    exact z.eqTrans (by ipra_ring)
  · refine ((lB_at g _ _ _ _).eqTrans ?_).eqSymm
    have pmN := pos_mul hm hN
    have r : Γ ⊢[PRAAx] rem (m * N) d ≐ m * N := (congrAp2 remF (.eqRefl _) hz).eqTrans (rem_by_zero _)
    have e0 : Γ ⊢[PRAAx] eqb (rem (m * N) d) zero ≐ zero :=
      (congrEqb' r (.eqRefl _)).eqTrans (eqb_zero_of_gt (one_le_of_pos pmN))
    exact (congrMul e0 (.eqRefl _)).eqTrans (zero_mul _)

theorem col_d {d m N y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hc : Γ ⊢[PRAAx] gcd m N ≐ one) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (aOut g))) (succ m) (pairT d (Xp m N y)) ≐ inst2 (lB g) d (Xp m N y) := by
  refine .orE (lt_or_le zero d) ?_ ?_
  · have hd : (lt zero d :: Γ) ⊢[PRAAx] d ≐ succ (pred d) := pos_of_one_le Prf.hyp0
    refine .orE (eqb_cases (Γ := lt zero d :: Γ) (rem (m * N) d) zero) ?_ ?_
    · exact col_none g hd.wk hm.wk.wk hN.wk.wk hc.wk.wk Prf.hyp0
    · exact col_some g hd.wk hm.wk.wk hN.wk.wk hc.wk.wk Prf.hyp0
  · exact col_zero g ((monus_zero d).eqSymm.eqTrans Prf.hyp0) hm.wk hN.wk

/-! ## The factorization -/

/-- `Σ_{d ≤ mN, d ∣ mN} g(d) = Σ_{a ≤ m, a ∣ m} Σ_{b ≤ N, b ∣ N} g(ab)` for coprime `m, N ≥ 1`. -/
theorem divisor_factor {m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hc : Γ ⊢[PRAAx] gcd m N ≐ one) (y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (lB g)) (succ (m * N)) (Xp m N y) ≐ ap2 (sumF (rB g)) (succ m) (Xp m N y) := by
  have hm1 := pos_sh hm
  have hN1 := pos_sh hN
  have hc1 := gcd_sh hc
  have r1 : Γ ⊢[PRAAx] ap2 (sumF (rB g)) (succ m) (Xp m N y) ≐
      ap2 (sumF (oB (aOut g))) (succ m) (pairT (succ (m * N)) (Xp m N y)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT, shift_succ_mul]
    have ha : (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift m)) := by
      have b : (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift (succ m)) := Prf.hyp0
      rw [show Syn.shift (succ m) = succ (Syn.shift m) by simp [Syn.shift]] at b
      exact b
    exact (step_b g ha).eqTrans (oB_at (aOut g) _ _ _).eqSymm
  have r2 := fubini (Γ := Γ) (aOut g) (succ m) (succ (m * N)) (Xp m N y)
  have r3 : Γ ⊢[PRAAx] ap2 (sumF (pB (aOut g))) (succ (m * N)) (pairT (succ m) (Xp m N y)) ≐
      ap2 (sumF (lB g)) (succ (m * N)) (Xp m N y) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [inst2_pB, shift_pairT]
    have e : Syn.shift (succ m) = succ (Syn.shift m) := by simp [Syn.shift]
    rw [e]
    refine (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
    exact col_d g hm1.wk hN1.wk hc1.wk
  exact (r1.eqTrans (r2.eqTrans r3)).eqSymm

end LeanProofs.IPRA.AnalyticNumberTheory.DivisorFactor
