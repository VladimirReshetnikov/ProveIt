import IPRADerivations.DiophantineNumberTheory.KhinchinBad

/-!
# The bad pairs up to `Q` (`hurwitz_khinchin_ipra`, (K3))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, the proof of (K3):
"Every noncoprime pair counted by `A(Q)` is divisible by some integer `d ∈ {2, …, Q}`. Dividing both
coordinates by `d` and applying (K5) bounds the number of bad pairs by `Σ_{d=2}^Q A(⌊Q/d⌋)`."

With `J* = (α/β, γ/β)`, numerators `p < M` and the parameters `y = ⟨M, ⟨α, ⟨γ, β⟩⟩⟩`:

  `Σ_{q ≤ Q} #{p < M : p/q ∈ J*, gcd(p, q) ≠ 1} ≤ Σ_{d ≤ Q} [2 ≤ d] · A(⌊Q/d⌋)`      (`bad_total`)

where `A(X) = KhinchinLattice.latticeA X M α γ β` is the (K5) count of all pairs with denominators
`1 ≤ q ≤ X`. The proof sums `KhinchinBad.bad_le` over `q` (the denominator `q = 0` counts nothing),
exchanges the double sum over `(q, d)` (`Core/Fubini`), and for each `d ≥ 1` reindexes the
denominators `q = d q'` (`SumReindex.reindex_eq`); the number of multiples of `d` up to `Q` is
`⌊Q/d⌋ + 1` (`Totient.count_multiples`), and the term `q' = 0` vanishes again.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBadSum

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (riB inst2_riB reindex_eq sum_le_bound)
open LeanProofs.IPRA.Topology.StaggeredGrids (congrEqb')
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Foundations.LatticeCount (sg_congr dcB)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBad (xq xα xγ xβ inJT cntB badB eB xdiv inst2_cntB
  inst2_badB inst2_eB inJT_congr bad_le)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinLattice (aK)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Bodies -/

/-- `bad(q) = #{p < M : p/q ∈ J*, gcd(p, q) ≠ 1}` in `(q, ⟨M, t⟩)`. -/
abbrev bqB : PTm 2 := ap2 (sumF badB) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

/-- `C(k) = #{p < M : p/k ∈ J*}` in `(k, ⟨M, t⟩)`. -/
abbrev cB : PTm 2 := ap2 (sumF cntB) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

/-- `[2 ≤ d][d ∣ q] C(q/d)` in `(q, d, ⟨M, t⟩)`. -/
abbrev gB : PTm 3 :=
  monus one (monus two (var 1)) * eqb (rem (var 0) (var 1)) zero *
    ap2 (sumF cntB) (fstT (var 2)) (pairT (quo (var 0) (var 1)) (sndT (var 2)))

/-- `[2 ≤ d] A(⌊Q/d⌋)` in `(d, ⟨Q, ⟨M, t⟩⟩)`. -/
abbrev LB : PTm 2 :=
  monus one (monus two (var 0)) * ap2 (sumF aK) (quo (fstT (var 1)) (var 0)) (sndT (var 1))

theorem inst2_bqB (q y : PTm n) : inst2 bqB q y = ap2 (sumF badB) (fstT y) (pairT q (sndT y)) := by
  simp [inst2, subst_ap2]

theorem inst2_cB (k y : PTm n) : inst2 cB k y = ap2 (sumF cntB) (fstT y) (pairT k (sndT y)) := by
  simp [inst2, subst_ap2]

theorem inst3_gB (q d y : PTm n) :
    inst3 gB q d y = monus one (monus two d) * eqb (rem q d) zero *
      ap2 (sumF cntB) (fstT y) (pairT (quo q d) (sndT y)) := by
  simp [inst3, subst_ap2]

theorem inst2_LB (d z : PTm n) :
    inst2 LB d z = monus one (monus two d) * ap2 (sumF aK) (quo (fstT z) d) (sndT z) := by
  simp [inst2, subst_ap2]

theorem inst2_aK (i y : PTm n) :
    inst2 aK i y = Foundations.LatticeCount.dS (fstT y) (succ i * fstT (sndT y))
      (succ i * fstT (sndT (sndT y))) (sndT (sndT (sndT y))) := by
  simp [inst2, subst_ap2]

theorem inst2_dcB (p w : PTm n) :
    inst2 dcB p w = sg (monus (p * sndT (sndT w)) (fstT w)) * sg (monus (fstT (sndT w)) (p * sndT (sndT w))) := by
  simp [inst2, Signum.sg]

/-! ## The denominator `0` counts nothing -/

/-- `[2 ≤ 0] = 0`. -/
theorem gate_zero : Γ ⊢[PRAAx] monus one (monus two (zero : PTm n)) ≐ zero :=
  (congrMonus (.eqRefl _) (monus_zero _)).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))

theorem inJT_zero (p q α γ β : PTm n) (h : Γ ⊢[PRAAx] q ≐ zero) : Γ ⊢[PRAAx] inJT p q α γ β ≐ zero := by
  have e : Γ ⊢[PRAAx] monus (q * γ) (p * β) ≐ zero :=
    (congrMonus ((congrMul h (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans (zero_monus _)
  exact (congrMul (.eqRefl _) ((sg_congr e).eqTrans sg_zero)).eqTrans (mul_zero _)

theorem shift_zero_hyp {q M : PTm n} (h : Γ ⊢[PRAAx] q ≐ zero) :
    (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] Syn.shift q ≐ zero := by
  have a := h.shift
  simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_zero] at a
  exact a.wk

theorem cnt_zero {q : PTm n} (M s : PTm n) (h : Γ ⊢[PRAAx] q ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF cntB) M (pairT q s) ≐ zero := by
  refine (sum_congr_bounded cntB zero (pairT q s) (pairT q s) M (.allI (.impI ?_))).eqTrans (sum_zeroB M _)
  rw [show inst2 (zero : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift (pairT q s)) = zero by simp [inst2],
    show Syn.shift (pairT q s) = pairT (Syn.shift q) (Syn.shift s) by simp [Syn.shift], inst2_cntB]
  exact (inJT_congr (.eqRefl _) (fst_pair _ _) (.eqRefl _) (.eqRefl _) (.eqRefl _)).eqTrans
    (inJT_zero _ _ _ _ _ (shift_zero_hyp (M := M) h))

theorem bad_zero {q : PTm n} (M s : PTm n) (h : Γ ⊢[PRAAx] q ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF badB) M (pairT q s) ≐ zero := by
  refine (sum_congr_bounded badB zero (pairT q s) (pairT q s) M (.allI (.impI ?_))).eqTrans (sum_zeroB M _)
  rw [show inst2 (zero : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift (pairT q s)) = zero by simp [inst2],
    show Syn.shift (pairT q s) = pairT (Syn.shift q) (Syn.shift s) by simp [Syn.shift], inst2_badB]
  exact (congrMul ((inJT_congr (.eqRefl _) (fst_pair _ _) (.eqRefl _) (.eqRefl _) (.eqRefl _)).eqTrans
    (inJT_zero _ _ _ _ _ (shift_zero_hyp (M := M) h))) (.eqRefl _)).eqTrans (zero_mul _)

/-! ## Rows: one denominator -/

/-- The `KhinchinBad` column body is the row of `gB`. -/
theorem eB_row (d q y : PTm n) :
    Γ ⊢[PRAAx] inst2 eB d (pairT (fstT y) (pairT q (sndT y))) ≐ inst2 (rowB gB) d (pairT q y) := by
  rw [inst2_eB, inst2_rowB, inst3_gB]
  have h2 : Γ ⊢[PRAAx] sndT (pairT (fstT y) (pairT q (sndT y))) ≐ pairT q (sndT y) := snd_pair _ _
  have hq1 : Γ ⊢[PRAAx] xq (sndT (pairT (fstT y) (pairT q (sndT y)))) ≐ q := h2.fstE
  have hq2 : Γ ⊢[PRAAx] fstT (pairT q y) ≐ q := fst_pair _ _
  have hy : Γ ⊢[PRAAx] sndT (pairT q y) ≐ y := snd_pair _ _
  have hs : Γ ⊢[PRAAx] sndT (sndT (pairT (fstT y) (pairT q (sndT y)))) ≐ sndT y :=
    h2.sndE
  refine (congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF hq1 (.eqRefl _)) (.eqRefl _)))
    (congrAp2 (sumF cntB) (fst_pair _ _) (congrPairT (congrAp2 quoF hq1 (.eqRefl _)) hs))).eqTrans ?_
  exact (congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF hq2 (.eqRefl _)) (.eqRefl _)))
    (congrAp2 (sumF cntB) (congrFst hy) (congrPairT (congrAp2 quoF hq2 (.eqRefl _)) (congrSnd hy)))).eqSymm

/-- `bad(q) ≤ Σ_{d < Q+1} [2 ≤ d][d ∣ q] C(q/d)` for `q < Q + 1`. -/
theorem row_le {q Q y : PTm n} (h : Γ ⊢[PRAAx] lt q (succ Q)) :
    Γ ⊢[PRAAx] le (inst2 bqB q y) (inst2 (oB gB) q (pairT (succ Q) y)) := by
  rw [inst2_bqB]
  refine le_congr (.eqRefl _) (oB_at gB q (succ Q) y).eqSymm ?_
  refine .orE (zero_or_succ q) ?_ ?_
  · exact le_congr (bad_zero _ _ Prf.hyp0).eqSymm (.eqRefl _) (zero_le _)
  · let Δ : List (Fm PTm n) := (q ≐ succ (pred q)) :: Γ
    have hq : Δ ⊢[PRAAx] q ≐ succ (pred q) := Prf.hyp0
    have hx : Δ ⊢[PRAAx] xq (pairT q (sndT y)) ≐ q := fst_pair _ _
    have hq' : Δ ⊢[PRAAx] xq (pairT q (sndT y)) ≐ succ (pred (xq (pairT q (sndT y)))) :=
      hx.eqTrans (hq.eqTrans (congrSucc (congrPred hx.eqSymm)))
    have b := bad_le (M := fstT y) hq'
    have hb : Δ ⊢[PRAAx] le (succ (xq (pairT q (sndT y)))) (succ Q) :=
      le_congr (congrSucc hx).eqSymm (.eqRefl _) (h.wk : Δ ⊢[PRAAx] le (succ q) (succ Q))
    have E : Δ ⊢[PRAAx] ap2 (sumF eB) (succ Q) (pairT (fstT y) (pairT q (sndT y))) ≐
        ap2 (sumF (rowB gB)) (succ Q) (pairT q y) := by
      refine sum_congr_bounded eB (rowB gB) _ _ (succ Q) (.allI (.impI ?_))
      rw [show Syn.shift (pairT (fstT y) (pairT q (sndT y))) =
          pairT (fstT (Syn.shift y)) (pairT (Syn.shift q) (sndT (Syn.shift y))) by simp [Syn.shift],
        show Syn.shift (pairT q y) = pairT (Syn.shift q) (Syn.shift y) by simp [Syn.shift]]
      exact eB_row _ _ _
    exact le_trans b (le_congr (.eqRefl _) E (sum_le_bound eB hb))

/-! ## Columns: one divisor -/

/-- `C(k) = dS(M, kα, kγ, β)`: the `KhinchinBad` count is the `LatticeCount` count. -/
theorem cnt_dS (k M s : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF cntB) M (pairT k s) ≐
      Foundations.LatticeCount.dS M (k * fstT s) (k * fstT (sndT s)) (sndT (sndT s)) := by
  refine sum_congr_bounded cntB dcB _ _ M (.allI (.impI ?_))
  rw [show Syn.shift (pairT k s) = pairT (Syn.shift k) (Syn.shift s) by simp [Syn.shift],
    show Syn.shift (pairT (k * fstT s) (pairT (k * fstT (sndT s)) (sndT (sndT s)))) =
      pairT (Syn.shift k * fstT (Syn.shift s)) (pairT (Syn.shift k * fstT (sndT (Syn.shift s)))
        (sndT (sndT (Syn.shift s)))) by simp [Syn.shift],
    inst2_cntB, inst2_dcB]
  let Δ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift
  have hX : Δ ⊢[PRAAx] sndT (pairT (Syn.shift k) (Syn.shift s)) ≐ Syn.shift s := snd_pair _ _
  have hW : Δ ⊢[PRAAx] sndT (pairT (Syn.shift k * fstT (Syn.shift s)) (pairT (Syn.shift k * fstT (sndT (Syn.shift s)))
      (sndT (sndT (Syn.shift s))))) ≐ pairT (Syn.shift k * fstT (sndT (Syn.shift s))) (sndT (sndT (Syn.shift s))) :=
    snd_pair _ _
  have hβ := hW.sndE
  have hu := (fst_pair (Γ := Δ) (Syn.shift k * fstT (Syn.shift s))
    (pairT (Syn.shift k * fstT (sndT (Syn.shift s))) (sndT (sndT (Syn.shift s)))))
  have hv := hW.fstE
  refine (inJT_congr (.eqRefl _) (fst_pair _ _) (congrFst hX) (congrFst (congrSnd hX))
    (congrSnd (congrSnd hX))).eqTrans ?_
  exact congrMul (sg_congr (congrMonus (congrMul (.eqRefl _) hβ.eqSymm) hu.eqSymm))
    (sg_congr (congrMonus hv.eqSymm (congrMul (.eqRefl _) hβ.eqSymm)))

/-- `Q + 1 + (d − 1) = d (⌊Q/d⌋ + 1) + (Q mod d)`, with atoms. -/
theorem quo_add_aux {Q d u r e : PTm n} (h1 : Γ ⊢[PRAAx] Q ≐ d * u + r) (h2 : Γ ⊢[PRAAx] d ≐ succ e) :
    Γ ⊢[PRAAx] succ Q + e ≐ d * succ u + r := by
  refine (congrAdd (congrSucc (h1.eqTrans (congrAdd (congrMul h2 (.eqRefl _)) (.eqRefl _)))) (.eqRefl _)).eqTrans ?_
  refine .eqTrans ?_ (congrAdd (congrMul h2.eqSymm (.eqRefl _)) (.eqRefl _))
  ipra_ring

/-- `#{q < Q + 1 : d ∣ q} = ⌊Q/d⌋ + 1` for `d ≥ 1`. -/
theorem multiples_upto {Q d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] ap2 (sumF mulBody) (succ Q) d ≐ succ (quo Q d) := by
  have dm := div_mod_at (Γ := Γ) (x := Q) hd
  exact (count_multiples hd).eqTrans (quo_eq hd (quo_add_aux (Prf.andE₁ dm) hd) (Prf.andE₂ dm))

/-- The column `d` of the double sum is `[2 ≤ d] A(⌊Q/d⌋)`. -/
theorem col_eq (d Q y : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB gB) d (pairT (succ Q) y) ≐ inst2 LB d (pairT Q y) := by
  rw [inst2_pB, inst2_LB]
  refine (congrAp2 (sumF (colB gB)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  refine .eqTrans ?_ (congrMul (.eqRefl _)
    (congrAp2 (sumF aK) (congrAp2 quoF (fst_pair _ _).eqSymm (.eqRefl _)) (snd_pair _ _).eqSymm))
  -- the column is `[2 ≤ d] · Σ_{q < Q+1} [d ∣ q] C(q/d)`
  have eS : Γ ⊢[PRAAx] ap2 (sumF (colB gB)) (succ Q) (pairT d y) ≐
      monus one (monus two d) * ap2 (sumF (riB cB)) (succ Q) (pairT d y) := by
    refine sum_scale (colB gB) (riB cB) (succ Q) (monus one (monus two d)) (pairT d y) (pairT d y)
      (.allI (.impI ?_))
    rw [show Syn.shift (pairT d y) = pairT (Syn.shift d) (Syn.shift y) by simp [Syn.shift], inst2_colB,
      inst2_riB, inst2_cB,
      show Syn.shift (monus one (monus two d)) = monus one (monus two (Syn.shift d)) by simp [Syn.shift]]
    refine (congrInst3 gB (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_gB]
    refine .eqTrans ?_ (congrMul (.eqRefl _) (congrMul
      (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _))
      (congrAp2 (sumF cntB) (congrFst (snd_pair _ _))
        (congrPairT (congrAp2 quoF (.eqRefl _) (fst_pair _ _)) (congrSnd (snd_pair _ _)))))).eqSymm
    ipra_ring
  refine .orE (zero_or_succ d) ?_ ?_
  · -- `d = 0`: the gate is closed on both sides
    let Δ : List (Fm PTm n) := (d ≐ zero) :: Γ
    have g0 : Δ ⊢[PRAAx] monus one (monus two d) ≐ zero :=
      (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans gate_zero
    exact (eS.wk.eqTrans ((congrMul g0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans
      ((congrMul g0 (.eqRefl _)).eqTrans (zero_mul _)).eqSymm
  · let Δ : List (Fm PTm n) := (d ≐ succ (pred d)) :: Γ
    have hd : Δ ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    refine eS.wk.eqTrans (congrMul (.eqRefl _) ?_)
    -- reindex `q = d q'`: `q' < ⌊Q/d⌋ + 1`
    refine (reindex_eq cB (succ Q) hd).eqTrans ?_
    refine (congrAp2 (sumF cB) (multiples_upto hd) (.eqRefl _)).eqTrans ?_
    refine (sum_shift cB (quo Q d) y).eqTrans ?_
    rw [inst2_cB]
    refine (congrAdd (cnt_zero _ _ (.eqRefl _)) (.eqRefl _)).eqTrans ((zero_add _).eqTrans ?_)
    refine sum_congr_bounded (shiftBody cB) aK y y (quo Q d) (.allI (.impI ?_))
    rw [inst2_shiftBody, inst2_cB, inst2_aK]
    exact cnt_dS _ _ _

/-! ## The total -/

/-- `Σ_{q ≤ Q} bad(q) ≤ Σ_{d ≤ Q} [2 ≤ d] A(⌊Q/d⌋)`. -/
theorem bad_total (Q y : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF bqB) (succ Q) y) (ap2 (sumF LB) (succ Q) (pairT Q y)) := by
  have s1 : Γ ⊢[PRAAx] le (ap2 (sumF bqB) (succ Q) y) (ap2 (sumF (oB gB)) (succ Q) (pairT (succ Q) y)) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    rw [show Syn.shift (pairT (succ Q) y) = pairT (succ (Syn.shift Q)) (Syn.shift y) by simp [Syn.shift]]
    have h : (lt (var 0) (Syn.shift (succ Q)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift Q)) := by
      rw [show succ (Syn.shift Q) = Syn.shift (succ Q) by simp [Syn.shift]]
      exact Prf.hyp0
    exact row_le h
  have s2 := fubini (Γ := Γ) gB (succ Q) (succ Q) y
  have s3 : Γ ⊢[PRAAx] ap2 (sumF (pB gB)) (succ Q) (pairT (succ Q) y) ≐ ap2 (sumF LB) (succ Q) (pairT Q y) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [show Syn.shift (pairT (succ Q) y) = pairT (succ (Syn.shift Q)) (Syn.shift y) by simp [Syn.shift],
      show Syn.shift (pairT Q y) = pairT (Syn.shift Q) (Syn.shift y) by simp [Syn.shift]]
    exact col_eq _ _ _
  exact le_congr (.eqRefl _) (s2.eqTrans s3) s1

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBadSum
