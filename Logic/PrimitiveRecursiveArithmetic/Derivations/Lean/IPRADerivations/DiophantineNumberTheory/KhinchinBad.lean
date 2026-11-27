import IPRADerivations.DiophantineNumberTheory.KhinchinSieve
import IPRADerivations.AnalyticNumberTheory.SumReindex
import IPRADerivations.Probability.Independence
import IPRADerivations.DiophantineNumberTheory.HurwitzMargin

/-!
# The bad pairs of one denominator (`hurwitz_khinchin_ipra`, (K3))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, the proof of (K3).
For one denominator `q ≥ 1`, with `J* = (α/β, γ/β)` and numerators `p < M`:

  `bad(q) = #{p < M : p/q ∈ J*, gcd(p, q) ≠ 1} ≤ Σ_{d ≤ q} [2 ≤ d][d ∣ q] · #{p' < M : p'/(q/d) ∈ J*}`

(`bad_le`): each noncoprime numerator is counted by `d = gcd(p, q)` (`KhinchinSieve.sieve_point`), the
double sum over `(p, d)` is exchanged (`Core/Fubini`), and for each `d ∣ q` the multiples `p = dp'`
are reindexed (`SumReindex.reindex_le`) to numerators `p'` of `q/d` (`KhinchinSieve.inJ_scale`).

The parameters are packed as `x = ⟨q, ⟨α, ⟨γ, β⟩⟩⟩`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBad

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (riB inst2_riB reindex_le)
open LeanProofs.IPRA.Topology.StaggeredGrids (eqb01' eq_of_eqb congrEqb')
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Foundations.LatticeCount (sg_congr)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinSieve (inJ_scale)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Bodies -/

abbrev xq (x : PTm n) : PTm n := fstT x
abbrev xα (x : PTm n) : PTm n := fstT (sndT x)
abbrev xγ (x : PTm n) : PTm n := fstT (sndT (sndT x))
abbrev xβ (x : PTm n) : PTm n := sndT (sndT (sndT x))

/-- `[qα < pβ][pβ < qγ]`. -/
abbrev inJT (p q α γ β : PTm n) : PTm n := sg (monus (p * β) (q * α)) * sg (monus (q * γ) (p * β))

/-- `[p/q ∈ J*]` in `(p, x)`. -/
abbrev cntB : PTm 2 := inJT (var 0) (xq (var 1)) (xα (var 1)) (xγ (var 1)) (xβ (var 1))

/-- `[p/q ∈ J*] [gcd(p, q) ≠ 1]` in `(p, x)`. -/
abbrev badB : PTm 2 := cntB * monus one (eqb (gcd (var 0) (xq (var 1))) one)

/-- `[2 ≤ d][d ∣ q][d ∣ p][p/q ∈ J*]` in `(p, d, x)`. -/
abbrev aB : PTm 3 :=
  monus one (monus two (var 1)) * eqb (rem (xq (var 2)) (var 1)) zero * eqb (rem (var 0) (var 1)) zero *
    inJT (var 0) (xq (var 2)) (xα (var 2)) (xγ (var 2)) (xβ (var 2))

/-- The parameters for the denominator `q/d`. -/
abbrev xdiv (x d : PTm n) : PTm n := pairT (quo (xq x) d) (sndT x)

/-- `[2 ≤ d][d ∣ q] · #{p' < M : p'/(q/d) ∈ J*}` in `(d, ⟨M, x⟩)`. -/
abbrev eB : PTm 2 :=
  monus one (monus two (var 0)) * eqb (rem (xq (sndT (var 1))) (var 0)) zero *
    ap2 (sumF cntB) (fstT (var 1)) (xdiv (sndT (var 1)) (var 0))

theorem inst2_cntB (p x : PTm n) : inst2 cntB p x = inJT p (xq x) (xα x) (xγ x) (xβ x) := by simp [inst2]

theorem inst2_badB (p x : PTm n) :
    inst2 badB p x = inJT p (xq x) (xα x) (xγ x) (xβ x) * monus one (eqb (gcd p (xq x)) one) := by
  simp only [inst2, badB, cntB, inJT, Signum.sg, PTm.subst_mul, PTm.subst_monus, subst_ex2,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, subst_eqb, subst_fstT, subst_sndT]

theorem inst3_aB (p d x : PTm n) :
    inst3 aB p d x = monus one (monus two d) * eqb (rem (xq x) d) zero * eqb (rem p d) zero *
      inJT p (xq x) (xα x) (xγ x) (xβ x) := by simp [inst3]

theorem inst2_eB (d z : PTm n) :
    inst2 eB d z = monus one (monus two d) * eqb (rem (xq (sndT z)) d) zero *
      ap2 (sumF cntB) (fstT z) (xdiv (sndT z) d) := by simp [inst2, subst_ap2]

/-! ## The sieve in row form -/

/-- `[p/q ∈ J*][gcd(p, q) ≠ 1] ≤ Σ_{d < q+1} a(p, d, x)`. -/
theorem sieve_row {p x : PTm n} (hq : Γ ⊢[PRAAx] xq x ≐ succ (pred (xq x))) :
    Γ ⊢[PRAAx] le (inst2 badB p x) (ap2 (sumF (rowB aB)) (succ (xq x)) (pairT p x)) := by
  rw [inst2_badB]
  have hrow : ∀ (d : PTm n), Γ ⊢[PRAAx] inst2 (rowB aB) d (pairT p x) ≐ inst3 aB p d x := fun d => by
    rw [inst2_rowB]; exact congrInst3 aB (fst_pair _ _) (.eqRefl _) (snd_pair _ _)
  refine .orE (eqb01' (Γ := Γ) (gcd p (xq x)) one) ?_ ?_
  · let Δ : List (Fm PTm n) := (eqb (gcd p (xq x)) one ≐ zero) :: Γ
    have hL : Δ ⊢[PRAAx] inJT p (xq x) (xα x) (xγ x) (xβ x) * monus one (eqb (gcd p (xq x)) one) ≐
        inJT p (xq x) (xα x) (xγ x) (xβ x) :=
      (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _))).eqTrans
        ((mul_comm _ _).eqTrans (one_mul _))
    have hg : Δ ⊢[PRAAx] gcd p (xq x) ≐ succ (pred (gcd p (xq x))) := gcd_pos_right hq.wk
    have hd := gcd_dvd_at hg
    have hgq : Δ ⊢[PRAAx] le (gcd p (xq x)) (xq x) := dvd_le' hg (Prf.andE₂ hd) hq.wk
    have h2 : Δ ⊢[PRAAx] monus one (monus two (gcd p (xq x))) ≐ one := by
      refine .orE (zero_or_succ (pred (gcd p (xq x)))) ?_ ?_
      · refine .botE _ (succ_ne_zero (a := zero) ?_)
        have e1 : ((pred (gcd p (xq x)) ≐ zero) :: Δ) ⊢[PRAAx] gcd p (xq x) ≐ one :=
          hg.wk.eqTrans (congrSucc Prf.hyp0)
        exact (eqb_of_eq e1).eqSymm.eqTrans (Prf.hyp1 : ((pred (gcd p (xq x)) ≐ zero) :: Δ) ⊢[PRAAx] _)
      · have e2 : ((pred (gcd p (xq x)) ≐ succ (pred (pred (gcd p (xq x))))) :: Δ) ⊢[PRAAx]
            gcd p (xq x) ≐ succ (succ (pred (pred (gcd p (xq x))))) := hg.wk.eqTrans (congrSucc Prf.hyp0)
        refine (congrMonus (.eqRefl _) ?_).eqTrans (monus_zero _)
        exact (congrMonus (.eqRefl _) e2).eqTrans ((succ_monus_succ _ _).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _)))
    have hterm : Δ ⊢[PRAAx] inst3 aB p (gcd p (xq x)) x ≐ inJT p (xq x) (xα x) (xγ x) (xβ x) := by
      rw [inst3_aB]
      refine (congrMul (congrMul (congrMul h2 (eqb_of_eq (Prf.andE₂ hd))) (eqb_of_eq (Prf.andE₁ hd))) (.eqRefl _)).eqTrans ?_
      ipra_ring
    have hlt : Δ ⊢[PRAAx] lt (gcd p (xq x)) (succ (xq x)) := (succ_monus_succ _ _).eqTrans hgq
    exact le_congr ((hrow _).wk.eqTrans (hterm.eqTrans hL.eqSymm)) (.eqRefl _) (term_le_sum (rowB aB) hlt)
  · have h0 : ((eqb (gcd p (xq x)) one ≐ one) :: Γ) ⊢[PRAAx]
        inJT p (xq x) (xα x) (xγ x) (xβ x) * monus one (eqb (gcd p (xq x)) one) ≐ zero :=
      (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self _))).eqTrans (mul_zero _)
    exact le_congr h0.eqSymm (.eqRefl _) (zero_le _)

/-! ## One divisor -/

/-- `[d ∣ p][p/q ∈ J*] = [d ∣ p][(p/d)/(q/d) ∈ J*]` when `d ∣ q`, `d ≥ 1`. -/
theorem div_point {p d x : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hdq : Γ ⊢[PRAAx] dvd d (xq x)) :
    Γ ⊢[PRAAx] eqb (rem p d) zero * inJT p (xq x) (xα x) (xγ x) (xβ x) ≐
      eqb (rem p d) zero * inJT (quo p d) (quo (xq x) d) (xα x) (xγ x) (xβ x) := by
  have dq := Prf.andE₁ (div_mod_at (Γ := Γ) (x := xq x) hd)
  have hq : Γ ⊢[PRAAx] xq x ≐ d * quo (xq x) d := dq.eqTrans ((congrAdd (.eqRefl _) hdq).eqTrans (add_zero _))
  refine .orE (eqb01' (Γ := Γ) (rem p d) zero) ?_ ?_
  · have h0 : ((eqb (rem p d) zero ≐ zero) :: Γ) ⊢[PRAAx] eqb (rem p d) zero ≐ zero := Prf.hyp0
    exact ((congrMul h0 (.eqRefl _)).eqTrans (zero_mul _)).eqTrans ((congrMul h0 (.eqRefl _)).eqTrans (zero_mul _)).eqSymm
  · let Δ : List (Fm PTm n) := (eqb (rem p d) zero ≐ one) :: Γ
    have hr : Δ ⊢[PRAAx] rem p d ≐ zero := eq_of_eqb Prf.hyp0
    have hp : Δ ⊢[PRAAx] p ≐ d * quo p d :=
      (Prf.andE₁ (div_mod_at (Γ := Δ) (x := p) hd.wk)).eqTrans ((congrAdd (.eqRefl _) hr).eqTrans (add_zero _))
    have e1 : Δ ⊢[PRAAx] p * xβ x ≐ d * quo p d * xβ x := congrMul hp (.eqRefl _)
    have e2 : Δ ⊢[PRAAx] xq x * xα x ≐ d * quo (xq x) d * xα x := congrMul hq.wk (.eqRefl _)
    have e3 : Δ ⊢[PRAAx] xq x * xγ x ≐ d * quo (xq x) d * xγ x := congrMul hq.wk (.eqRefl _)
    exact congrMul (.eqRefl _) ((congrMul (sg_congr (congrMonus e1 e2)) (sg_congr (congrMonus e3 e1))).eqTrans
      (inJ_scale hd.wk))

/-- `[d ∣ p][p/q ∈ J*]` in `(p, ⟨d, x⟩)`. -/
abbrev fB : PTm 2 :=
  eqb (rem (var 0) (fstT (var 1))) zero *
    inJT (var 0) (xq (sndT (var 1))) (xα (sndT (var 1))) (xγ (sndT (var 1))) (xβ (sndT (var 1)))

theorem inst2_fB (p y : PTm n) :
    inst2 fB p y = eqb (rem p (fstT y)) zero *
      inJT p (xq (sndT y)) (xα (sndT y)) (xγ (sndT y)) (xβ (sndT y)) := by simp [inst2]

/-- `inJT` is a congruence in all its arguments. -/
theorem inJT_congr {p p' q q' α α' γ γ' β β' : PTm n} (h1 : Γ ⊢[PRAAx] p ≐ p') (h2 : Γ ⊢[PRAAx] q ≐ q')
    (h3 : Γ ⊢[PRAAx] α ≐ α') (h4 : Γ ⊢[PRAAx] γ ≐ γ') (h5 : Γ ⊢[PRAAx] β ≐ β') :
    Γ ⊢[PRAAx] inJT p q α γ β ≐ inJT p' q' α' γ' β' :=
  congrMul (sg_congr (congrMonus (congrMul h1 h5) (congrMul h2 h3)))
    (sg_congr (congrMonus (congrMul h2 h4) (congrMul h1 h5)))

/-- The projections of a pair `⟨d, x⟩`. -/
theorem fB_at (p d x : PTm n) :
    Γ ⊢[PRAAx] inst2 fB p (pairT d x) ≐ eqb (rem p d) zero * inJT p (xq x) (xα x) (xγ x) (xβ x) := by
  rw [inst2_fB]
  have hs : Γ ⊢[PRAAx] sndT (pairT d x) ≐ x := snd_pair _ _
  exact congrMul (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _))
    (inJT_congr (.eqRefl _) (congrFst hs) (congrFst (congrSnd hs)) (congrFst (congrSnd (congrSnd hs)))
      (congrSnd (congrSnd (congrSnd hs))))

/-- The reindexed body read through the pairs. -/
theorem riB_at (p d x : PTm n) :
    Γ ⊢[PRAAx] inst2 (riB cntB) p (pairT d (xdiv x d)) ≐
      eqb (rem p d) zero * inJT (quo p d) (quo (xq x) d) (xα x) (xγ x) (xβ x) := by
  rw [inst2_riB, inst2_cntB]
  have hs : Γ ⊢[PRAAx] sndT (pairT d (xdiv x d)) ≐ xdiv x d := snd_pair _ _
  have hf : Γ ⊢[PRAAx] fstT (pairT d (xdiv x d)) ≐ d := fst_pair _ _
  have hq : Γ ⊢[PRAAx] xq (sndT (pairT d (xdiv x d))) ≐ quo (xq x) d := (congrFst hs).eqTrans (fst_pair _ _)
  have hx : Γ ⊢[PRAAx] sndT (sndT (pairT d (xdiv x d))) ≐ sndT x := (congrSnd hs).eqTrans (snd_pair _ _)
  exact congrMul (congrEqb' (congrAp2 remF (.eqRefl _) hf) (.eqRefl _))
    (inJT_congr (congrAp2 quoF (.eqRefl _) hf) hq (congrFst hx) (congrFst (congrSnd hx)) (congrSnd (congrSnd hx)))

/-- `K S ≤ K S'` for the gate `K = [2 ≤ d][d ∣ q]`. -/
theorem col_bound (M d x : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF (colB aB)) M (pairT d x)) (inst2 eB d (pairT M x)) := by
  let K : PTm n := monus one (monus two d) * eqb (rem (xq x) d) zero
  -- the column is `K · Σ_p [d ∣ p][p/q ∈ J*]`
  have eS : Γ ⊢[PRAAx] ap2 (sumF (colB aB)) M (pairT d x) ≐ K * ap2 (sumF fB) M (pairT d x) := by
    refine sum_scale (colB aB) fB M K (pairT d x) (pairT d x) (.allI (.impI ?_))
    rw [show Syn.shift (pairT d x) = pairT (Syn.shift d) (Syn.shift x) by simp [Syn.shift]]
    rw [inst2_colB]
    refine (congrInst3 aB (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aB]
    refine (?_ : _ ⊢[PRAAx] _ ≐ Syn.shift K * (eqb (rem (var 0) (Syn.shift d)) zero *
      inJT (var 0) (xq (Syn.shift x)) (xα (Syn.shift x)) (xγ (Syn.shift x)) (xβ (Syn.shift x)))).eqTrans
      (congrMul (.eqRefl _) (fB_at _ _ _).eqSymm)
    rw [show Syn.shift K = monus one (monus two (Syn.shift d)) * eqb (rem (xq (Syn.shift x)) (Syn.shift d)) zero by
      simp [K, Syn.shift, subst_ap2]]
    ipra_ring
  -- the right side is `K · #{p' < M : p'/(q/d) ∈ J*}`
  have eR : Γ ⊢[PRAAx] inst2 eB d (pairT M x) ≐ K * ap2 (sumF cntB) M (xdiv x d) := by
    rw [inst2_eB]
    have hz2 : Γ ⊢[PRAAx] sndT (pairT M x) ≐ x := snd_pair _ _
    exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (congrFst hz2) (.eqRefl _)) (.eqRefl _)))
      (congrAp2 (sumF cntB) (fst_pair _ _) (congrPairT (congrAp2 quoF (congrFst hz2) (.eqRefl _)) (congrSnd hz2)))
  refine le_congr eS.eqSymm eR.eqSymm ?_
  have kz : ∀ {Δ : List (Fm PTm n)}, (Δ ⊢[PRAAx] K ≐ zero) →
      (Δ ⊢[PRAAx] le (K * ap2 (sumF fB) M (pairT d x)) (K * ap2 (sumF cntB) M (xdiv x d))) := fun h =>
    le_congr ((congrMul h (.eqRefl _)).eqTrans (zero_mul _)).eqSymm (.eqRefl _) (zero_le _)
  refine .orE (zero_or_succ d) ?_ ?_
  · -- `d = 0`: the gate is closed
    refine kz ?_
    have g0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] monus one (monus two d) ≐ zero :=
      (congrMonus (.eqRefl _) ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _))).eqTrans
        ((succ_monus_succ _ _).eqTrans (zero_monus _))
    exact (congrMul g0 (.eqRefl _)).eqTrans (zero_mul _)
  · let Δ : List (Fm PTm n) := (d ≐ succ (pred d)) :: Γ
    have hd : Δ ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    refine .orE (eqb01' (Γ := Δ) (rem (xq x) d) zero) ?_ ?_
    · refine kz ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))
    · -- `d ∣ q`: reindex the multiples of `d`
      let Δ' : List (Fm PTm n) := (eqb (rem (xq x) d) zero ≐ one) :: Δ
      have hdq : Δ' ⊢[PRAAx] dvd d (xq x) := eq_of_eqb Prf.hyp0
      have hS : Δ' ⊢[PRAAx] ap2 (sumF fB) M (pairT d x) ≐ ap2 (sumF (riB cntB)) M (pairT d (xdiv x d)) := by
        refine sum_congr_bounded fB (riB cntB) _ _ M (.allI (.impI ?_))
        have hd' : (lt (var 0) (Syn.shift M) :: Δ'.map Fm.shift) ⊢[PRAAx] Syn.shift d ≐ succ (pred (Syn.shift d)) := by
          have a := (show Δ' ⊢[PRAAx] d ≐ succ (pred d) from hd.wk).shift
          simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_succ, PTm.subst_pred] at a
          exact a.wk
        have hdq' : (lt (var 0) (Syn.shift M) :: Δ'.map Fm.shift) ⊢[PRAAx] dvd (Syn.shift d) (xq (Syn.shift x)) := by
          have a := hdq.shift
          simp only [Fm.shift, Fm.subst_eq, subst_ap2, ConciseIPRA.PTm.subst_zero, subst_fstT] at a
          exact a.wk
        rw [show Syn.shift (pairT d x) = pairT (Syn.shift d) (Syn.shift x) by simp [Syn.shift],
          show Syn.shift (pairT d (xdiv x d)) = pairT (Syn.shift d) (xdiv (Syn.shift x) (Syn.shift d)) by
            simp [Syn.shift, subst_ap2]]
        exact (fB_at _ _ _).eqTrans ((div_point hd' hdq').eqTrans (riB_at _ _ _).eqSymm)
      have hle := reindex_le cntB (x := xdiv x d) M (show Δ' ⊢[PRAAx] d ≐ succ (pred d) from hd.wk)
      exact HurwitzMargin.le_mul_mono K (le_congr hS.eqSymm (.eqRefl _) hle)

/-- The bad numerators of one denominator `q ≥ 1`:
`#{p < M : p/q ∈ J*, gcd(p, q) ≠ 1} ≤ Σ_{d < q+1} [2 ≤ d][d ∣ q] #{p' < M : p'/(q/d) ∈ J*}`. -/
theorem bad_le {M x : PTm n} (hq : Γ ⊢[PRAAx] xq x ≐ succ (pred (xq x))) :
    Γ ⊢[PRAAx] le (ap2 (sumF badB) M x) (ap2 (sumF eB) (succ (xq x)) (pairT M x)) := by
  have s1 : Γ ⊢[PRAAx] le (ap2 (sumF badB) M x) (ap2 (sumF (oB aB)) M (pairT (succ (xq x)) x)) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    have hq' : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx]
        xq (Syn.shift x) ≐ succ (pred (xq (Syn.shift x))) := by
      have a := hq.shift
      simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_succ, PTm.subst_pred, subst_fstT] at a
      exact a.wk
    rw [show Syn.shift (pairT (succ (xq x)) x) = pairT (succ (xq (Syn.shift x))) (Syn.shift x) by simp [Syn.shift]]
    exact le_congr (.eqRefl _) (oB_at aB _ _ _).eqSymm (sieve_row hq')
  have s2 := fubini (Γ := Γ) aB M (succ (xq x)) x
  have s3 : Γ ⊢[PRAAx] le (ap2 (sumF (pB aB)) (succ (xq x)) (pairT M x)) (ap2 (sumF eB) (succ (xq x)) (pairT M x)) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    rw [show Syn.shift (pairT M x) = pairT (Syn.shift M) (Syn.shift x) by simp [Syn.shift], inst2_pB]
    refine le_congr (congrAp2 (sumF (colB aB)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
      (.eqRefl _) (col_bound _ _ _)
  exact le_trans s1 (le_congr s2.eqSymm (.eqRefl _) s3)

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBad

export_ipra DiophantineNumberTheory.KhinchinBad (inJT)
