import IPRADerivations.Core.OrderCertificates
import IPRADerivations.AnalyticNumberTheory.Mobius
import IPRADerivations.Topology.StaggeredGrids
import IPRADerivations.Core.Reindex

/-!
# Counting through an injection

A bounded set `{i < N : c(i) ≠ 0}` mapped injectively by `g` into `[0, R)` has at most `R` elements:

  `Σ_{i<N} [c(i)] ≤ R`                                                         (`injection_count`)

where `[c] = sg c`. The two hypotheses are closed equations, so that they can be discharged by sum
arguments:

* no collisions: `Σ_{M<N} Σ_{i<M} [c(i)][c(M)][g(i) = g(M)] = 0` (`coll`);
* no escape: `Σ_{i<N} [c(i)][R ≤ g(i)] = 0` (`viol`).

The proof is the double count of `e(i, y) = [c(i)][g(i) = y]` on `i < N`, `y < R` (`Core/Fubini`): a row
with `c(i) ≠ 0` contains exactly one `1` (`row_val`, by `sum_delta`), and a column contains at most one
(`col_le`, by induction: a second index in the same column would be a collision).

Reusable for separation counts such as "distinct reduced fractions with denominators at most `Q` are
separated by `Q⁻²`, so an interval of length `λ` contains at most `λQ² + 1` of them"
(`hurwitz_khinchin_ipra`, `khinchin.tex`, (K3), (K9)).
-/

namespace LeanProofs.IPRA.Foundations.InjectionCount

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (sg_bit shift_inst2')
open LeanProofs.IPRA.Topology.StaggeredGrids (eqb01' eq_of_eqb congrEqb')
open LeanProofs.IPRA.Probability.Independence (sum_scale)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Inj

variable (c g : PTm 2)

/-- `[c(i)] [g(i) = y]` over `0 = i`, `1 = y`, `2 = x`. -/
def eB : PTm 3 := sg (Syn.subst ![var 0, var 2] c) * eqb (Syn.subst ![var 0, var 2] g) (var 1)

theorem inst3_eB (i y x : PTm n) : inst3 (eB c g) i y x = sg (inst2 c i x) * eqb (inst2 g i x) y := by
  simp [inst3, eB, PTm.subst_mul, Signum.sg, PTm.subst_monus, subst_eqb, subst_reindex2]

/-- `[c(i)] [c(M)] [g(i) = g(M)]` over `0 = i`, `1 = ⟨M, x⟩`. -/
def clB : PTm 2 := sg (Syn.subst ![var 0, sndT (var 1)] c) * sg (Syn.subst ![fstT (var 1), sndT (var 1)] c) *
  eqb (Syn.subst ![var 0, sndT (var 1)] g) (Syn.subst ![fstT (var 1), sndT (var 1)] g)

theorem inst2_clB (i z : PTm n) : inst2 (clB c g) i z =
    sg (inst2 c i (sndT z)) * sg (inst2 c (fstT z) (sndT z)) * eqb (inst2 g i (sndT z)) (inst2 g (fstT z) (sndT z)) := by
  simp [inst2, clB, PTm.subst_mul, Signum.sg, PTm.subst_monus, subst_eqb, subst_reindex2]

/-- The collisions of the index `M`: `Σ_{i<M} clB(i, ⟨M, x⟩)` over `0 = M`, `1 = x`. -/
abbrev rowCB : PTm 2 := ap2 (sumF (clB c g)) (var 0) (pairT (var 0) (var 1))

theorem inst2_rowCB (M x : PTm n) : inst2 (rowCB c g) M x = ap2 (sumF (clB c g)) M (pairT M x) := by
  simp [inst2, subst_ap2]

/-- All collisions below `N`. -/
abbrev coll (N x : PTm n) : PTm n := ap2 (sumF (rowCB c g)) N x

/-- `[c(i)] [R ≤ g(i)]` over `0 = i`, `1 = ⟨R, x⟩`. -/
def vB : PTm 2 := sg (Syn.subst ![var 0, sndT (var 1)] c) *
  monus one (monus (fstT (var 1)) (Syn.subst ![var 0, sndT (var 1)] g))

theorem inst2_vB (i z : PTm n) : inst2 (vB c g) i z =
    sg (inst2 c i (sndT z)) * monus one (monus (fstT z) (inst2 g i (sndT z))) := by
  simp [inst2, vB, PTm.subst_mul, Signum.sg, PTm.subst_monus, subst_reindex2]

/-- All range violations below `N`. -/
abbrev viol (N R x : PTm n) : PTm n := ap2 (sumF (vB c g)) N (pairT R x)

/-- `[c(i)]` as a body. -/
abbrev sgB : PTm 2 := sg c

theorem inst2_sgB (i x : PTm n) : inst2 (sgB c) i x = sg (inst2 c i x) := by simp [inst2, Signum.sg]

/-- A term of a vanishing sum vanishes. -/
theorem term_zero (f : PTm 2) {i N x : PTm n} (hi : Γ ⊢[PRAAx] lt i N) (h : Γ ⊢[PRAAx] ap2 (sumF f) N x ≐ zero) :
    Γ ⊢[PRAAx] inst2 f i x ≐ zero :=
  le_antisymm (le_congr (.eqRefl _) h (term_le_sum f hi)) (zero_le _)

/-! ## Rows -/

/-- `Σ_{y<R} [g = y] = 1` for `g < R`. -/
theorem delta_one {G R : PTm n} (h : Γ ⊢[PRAAx] lt G R) :
    Γ ⊢[PRAAx] ap2 (sumF (eqb (var 1) (var 0) : PTm 2)) R G ≐ one := by
  refine (sum_congr_bounded _ (dB (one : PTm 2)) G (pairT G G) R (.allI (.impI ?_))).eqTrans
    ((sum_delta (x := G) (one : PTm 2) h).eqTrans
      (by rw [show inst2 (one : PTm 2) G G = one by simp [inst2]]; exact .eqRefl _))
  rw [inst2_dB, show Syn.shift (pairT G G) = pairT (Syn.shift G) (Syn.shift G) by simp [Syn.shift],
    show inst2 (eqb (var 1) (var 0) : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift G) = eqb (Syn.shift G) (var 0) by
      simp [inst2],
    show inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (sndT (pairT (Syn.shift G) (Syn.shift G))) = one by simp [inst2]]
  exact (congrEqb' (fst_pair _ _).eqSymm (.eqRefl _)).eqTrans ((mul_comm _ _).eqTrans (one_mul _)).eqSymm

/-- A row: `Σ_{y<R} [c(i)][g(i) = y] = [c(i)]` when `[c(i)][R ≤ g(i)] = 0`. -/
theorem row_val {i R x : PTm n} (hv : Γ ⊢[PRAAx] sg (inst2 c i x) * monus one (monus R (inst2 g i x)) ≐ zero) :
    Γ ⊢[PRAAx] inst2 (oB (eB c g)) i (pairT R x) ≐ sg (inst2 c i x) := by
  refine (oB_at (eB c g) i R x).eqTrans ?_
  have sc : Γ ⊢[PRAAx] ap2 (sumF (rowB (eB c g))) R (pairT i x) ≐
      sg (inst2 c i x) * ap2 (sumF (eqb (var 1) (var 0) : PTm 2)) R (inst2 g i x) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB, show Syn.shift (pairT i x) = pairT (Syn.shift i) (Syn.shift x) by simp [Syn.shift]]
    refine (congrInst3 (eB c g) (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_eB, show inst2 (eqb (var 1) (var 0) : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift (inst2 g i x)) =
        eqb (Syn.shift (inst2 g i x)) (var 0) by simp [inst2],
      show Syn.shift (sg (inst2 c i x)) = sg (inst2 c (Syn.shift i) (Syn.shift x)) by
        rw [← shift_inst2']; simp [Syn.shift, Signum.sg],
      shift_inst2']
    exact .eqRefl _
  refine sc.eqTrans ?_
  refine .orE (sg_bit (Γ := Γ) (inst2 c i x)) ?_ ?_
  · have h0 : ((sg (inst2 c i x) ≐ zero) :: Γ) ⊢[PRAAx] sg (inst2 c i x) ≐ zero := Prf.hyp0
    exact ((congrMul h0 (.eqRefl _)).eqTrans (zero_mul _)).eqTrans h0.eqSymm
  · let Δ : List (Fm PTm n) := (sg (inst2 c i x) ≐ one) :: Γ
    have h1 : Δ ⊢[PRAAx] sg (inst2 c i x) ≐ one := Prf.hyp0
    -- `[R ≤ g(i)] = 0`, so `g(i) < R`
    have hz : Δ ⊢[PRAAx] monus one (monus R (inst2 g i x)) ≐ zero :=
      ((one_mul _).eqSymm.eqTrans (congrMul h1.eqSymm (.eqRefl _))).eqTrans hv.wk
    have hlt : Δ ⊢[PRAAx] lt (inst2 g i x) R := by
      refine .orE (lt_or_le (inst2 g i x) R) Prf.hyp0 ?_
      refine .botE _ (succ_ne_zero (a := zero) ?_)
      have hle : (le R (inst2 g i x) :: Δ) ⊢[PRAAx] monus R (inst2 g i x) ≐ zero := Prf.hyp0
      exact (monus_zero _).eqSymm.eqTrans ((congrMonus (.eqRefl _) hle).eqSymm.eqTrans hz.wk)
    exact (congrMul h1 (delta_one hlt)).eqTrans ((one_mul _).eqTrans h1.eqSymm)

/-! ## Columns -/

/-- The column invariant: `M ≤ N → Σ_{i<M} [c(i)][g(i) = y] ≤ 1`. -/
def colInv (M N y x : PTm n) : Fm PTm n :=
  le M N ⟶ le (ap2 (sumF (colB (eB c g))) M (pairT y x)) one

@[simp] theorem subst_colInv {k : ℕ} (σ : Fin n → PTm k) (M N y x : PTm n) :
    (colInv c g M N y x).subst σ = colInv c g (Syn.subst σ M) (Syn.subst σ N) (Syn.subst σ y) (Syn.subst σ x) := by
  simp [colInv, subst_ap2]

theorem colInv_QF (M N y x : PTm n) : (colInv c g M N y x).QF := by
  unfold colInv; exact ⟨le_QF _ _, le_QF _ _⟩

theorem colB_at (i y x : PTm n) :
    Γ ⊢[PRAAx] inst2 (colB (eB c g)) i (pairT y x) ≐ sg (inst2 c i x) * eqb (inst2 g i x) y := by
  rw [inst2_colB]
  refine (congrInst3 (eB c g) (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans ?_
  rw [inst3_eB]; exact .eqRefl _

/-- The step of the column count. -/
theorem col_step {M N y x : PTm n} (hK : Γ ⊢[PRAAx] coll c g N x ≐ zero) (ih : Γ ⊢[PRAAx] colInv c g M N y x) :
    Γ ⊢[PRAAx] colInv c g (succ M) N y x := by
  refine .impI ?_
  let Δ : List (Fm PTm n) := le (succ M) N :: Γ
  have hM : Δ ⊢[PRAAx] lt M N := Prf.hyp0
  have ih' : Δ ⊢[PRAAx] le (ap2 (sumF (colB (eB c g))) M (pairT y x)) one :=
    Prf.impE ih.wk (le_trans (le_succ_self M) Prf.hyp0)
  have es := (sum_succ' (Γ := Δ) (colB (eB c g)) M (pairT y x)).eqTrans (congrAdd (.eqRefl _) (colB_at c g M y x))
  refine le_congr es.eqSymm (.eqRefl _) ?_
  refine .orE (sg_bit (Γ := Δ) (inst2 c M x)) ?_ ?_
  · have h0 : ((sg (inst2 c M x) ≐ zero) :: Δ) ⊢[PRAAx] sg (inst2 c M x) ≐ zero := Prf.hyp0
    exact le_congr ((add_zero (ap2 (sumF (colB (eB c g))) M (pairT y x))).eqSymm.eqTrans
      (congrAdd (.eqRefl _) ((congrMul h0 (.eqRefl _)).eqTrans (zero_mul _)).eqSymm)) (.eqRefl _) ih'.wk
  · refine .orE (eqb01' (Γ := (sg (inst2 c M x) ≐ one) :: Δ) (inst2 g M x) y) ?_ ?_
    · let Δ' : List (Fm PTm n) := (eqb (inst2 g M x) y ≐ zero) :: (sg (inst2 c M x) ≐ one) :: Δ
      have h0 : Δ' ⊢[PRAAx] eqb (inst2 g M x) y ≐ zero := Prf.hyp0
      exact le_congr ((add_zero (ap2 (sumF (colB (eB c g))) M (pairT y x))).eqSymm.eqTrans
        (congrAdd (.eqRefl _) ((congrMul (.eqRefl _) h0).eqTrans (mul_zero _)).eqSymm)) (.eqRefl _) ih'.wk.wk
    · let Δ' : List (Fm PTm n) := (eqb (inst2 g M x) y ≐ one) :: (sg (inst2 c M x) ≐ one) :: Δ
      have he : Δ' ⊢[PRAAx] eqb (inst2 g M x) y ≐ one := Prf.hyp0
      have hc : Δ' ⊢[PRAAx] sg (inst2 c M x) ≐ one := Prf.hyp1
      have hgy : Δ' ⊢[PRAAx] inst2 g M x ≐ y := eq_of_eqb he
      -- the collisions of `M` vanish
      have hrow : Δ' ⊢[PRAAx] ap2 (sumF (clB c g)) M (pairT M x) ≐ zero := by
        have t := term_zero (rowCB c g) (hM.wk.wk : Δ' ⊢[PRAAx] lt M N) hK.wk.wk.wk
        rw [inst2_rowCB] at t
        exact t
      -- so the earlier part of the column vanishes
      have hz : Δ' ⊢[PRAAx] ap2 (sumF (colB (eB c g))) M (pairT y x) ≐ zero := by
        refine (sum_congr_bounded _ (zero : PTm 2) _ (pairT y x) M (.allI (.impI ?_))).eqTrans (sum_zeroB _ _)
        rw [show inst2 (zero : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift (pairT y x)) = zero by simp [inst2],
          show Syn.shift (pairT y x) = pairT (Syn.shift y) (Syn.shift x) by simp [Syn.shift]]
        refine (colB_at c g _ _ _).eqTrans ?_
        let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift M) :: Δ'.map Fm.shift
        have hrow' : Θ ⊢[PRAAx] ap2 (sumF (clB c g)) (Syn.shift M) (pairT (Syn.shift M) (Syn.shift x)) ≐ zero := by
          have s0 : Δ'.map Fm.shift ⊢[PRAAx] ap2 (sumF (clB c g)) (Syn.shift M) (pairT (Syn.shift M) (Syn.shift x)) ≐ zero := by
            simpa [Fm.shift, Syn.shift, subst_ap2] using hrow.shift
          exact s0.wk
        have tz := term_zero (clB c g) (Prf.hyp0 : Θ ⊢[PRAAx] lt (var 0) (Syn.shift M)) hrow'
        rw [inst2_clB] at tz
        have hc' : Θ ⊢[PRAAx] sg (inst2 c (Syn.shift M) (Syn.shift x)) ≐ one := by
          have s0 : Δ'.map Fm.shift ⊢[PRAAx] sg (inst2 c (Syn.shift M) (Syn.shift x)) ≐ one := by
            rw [← shift_inst2']
            simpa [Fm.shift, Syn.shift, Signum.sg] using hc.shift
          exact s0.wk
        have hgy' : Θ ⊢[PRAAx] inst2 g (Syn.shift M) (Syn.shift x) ≐ Syn.shift y := by
          have s0 : Δ'.map Fm.shift ⊢[PRAAx] inst2 g (Syn.shift M) (Syn.shift x) ≐ Syn.shift y := by
            rw [← shift_inst2']
            simpa [Fm.shift, Syn.shift] using hgy.shift
          exact s0.wk
        have fs : Θ ⊢[PRAAx] fstT (pairT (Syn.shift M) (Syn.shift x)) ≐ Syn.shift M := fst_pair _ _
        have ss : Θ ⊢[PRAAx] sndT (pairT (Syn.shift M) (Syn.shift x)) ≐ Syn.shift x := snd_pair _ _
        refine .eqTrans ?_ tz
        refine .eqTrans ?_ (congrMul (congrMul (congrSg (congrInst2 c (.eqRefl _) ss)).eqSymm
          (congrSg (congrInst2 c fs ss)).eqSymm)
          (congrEqb' (congrInst2 g (.eqRefl _) ss) (congrInst2 g fs ss)).eqSymm)
        refine .eqTrans ?_ (congrMul (congrMul (.eqRefl _) hc'.eqSymm) (congrEqb' (.eqRefl _) hgy'.eqSymm))
        ipra_ring
      have e1 := natEq hz; have e2 := natEq hc; have e3 := natEq he
      ipra_le 0 with e1 + 𝔞 (eqb (inst2 g M x) y) * e2 + e3

/-- A column: `Σ_{i<N} [c(i)][g(i) = y] ≤ 1` when there are no collisions. -/
theorem col_le {N y x : PTm n} (hK : Γ ⊢[PRAAx] coll c g N x ≐ zero) :
    Γ ⊢[PRAAx] le (ap2 (sumF (colB (eB c g))) N (pairT y x)) one := by
  have hall : Γ ⊢[PRAAx] Fm.all (colInv c g (var 0) (Syn.shift N) (Syn.shift y) (Syn.shift x)) := by
    refine PRA.qfInd _ (colInv_QF _ _ _ _ _ _) ?_ ?_
    · rw [subst_colInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact .impI (le_congr (sum_zero _ _).eqSymm (.eqRefl _) (zero_le _))
    · rw [subst_colInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have hK' : (colInv c g (var 0) (Syn.shift N) (Syn.shift y) (Syn.shift x) :: Γ.map Fm.shift) ⊢[PRAAx]
          coll c g (Syn.shift N) (Syn.shift x) ≐ zero := by
        have s0 : Γ.map Fm.shift ⊢[PRAAx] coll c g (Syn.shift N) (Syn.shift x) ≐ zero := by
          simpa [Fm.shift, Syn.shift, subst_ap2] using hK.shift
        exact s0.wk
      exact col_step c g hK' Prf.hyp0
  have a := Prf.allE N hall
  rw [subst_colInv] at a
  simp only [Syn.subst_inst_shift] at a
  exact Prf.impE a (le_refl N)

/-! ## The count -/

/-- `Σ_{i<N} [c(i)] ≤ R` for an injective `g` into `[0, R)` on `{c ≠ 0}`. -/
theorem injection_count {N R x : PTm n} (hK : Γ ⊢[PRAAx] coll c g N x ≐ zero)
    (hV : Γ ⊢[PRAAx] viol c g N R x ≐ zero) : Γ ⊢[PRAAx] le (ap2 (sumF (sgB c)) N x) R := by
  have rows : Γ ⊢[PRAAx] ap2 (sumF (sgB c)) N x ≐ ap2 (sumF (oB (eB c g))) N (pairT R x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_sgB, show Syn.shift (pairT R x) = pairT (Syn.shift R) (Syn.shift x) by simp [Syn.shift]]
    let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    have hV' : Θ ⊢[PRAAx] viol c g (Syn.shift N) (Syn.shift R) (Syn.shift x) ≐ zero := by
      have s0 : Γ.map Fm.shift ⊢[PRAAx] viol c g (Syn.shift N) (Syn.shift R) (Syn.shift x) ≐ zero := by
        simpa [Fm.shift, Syn.shift, subst_ap2] using hV.shift
      exact s0.wk
    have tz := term_zero (vB c g) (Prf.hyp0 : Θ ⊢[PRAAx] lt (var 0) (Syn.shift N)) hV'
    rw [inst2_vB] at tz
    have hv : Θ ⊢[PRAAx] sg (inst2 c (var 0) (Syn.shift x)) * monus one (monus (Syn.shift R) (inst2 g (var 0) (Syn.shift x))) ≐ zero :=
      (congrMul (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrInst2 c (.eqRefl _) (snd_pair _ _))))
        (congrMonus (.eqRefl _) (congrMonus (fst_pair _ _) (congrInst2 g (.eqRefl _) (snd_pair _ _))))).eqSymm.eqTrans tz
    exact (row_val c g hv).eqSymm
  have fb := fubini (Γ := Γ) (eB c g) N R x
  have cols : Γ ⊢[PRAAx] le (ap2 (sumF (pB (eB c g))) R (pairT N x)) (R * one) := by
    refine sum_le_uniform_bound (pB (eB c g)) (.allI (.impI ?_))
    rw [inst2_pB, show Syn.shift (one : PTm n) = one by simp [Syn.shift],
      show Syn.shift (pairT N x) = pairT (Syn.shift N) (Syn.shift x) by simp [Syn.shift]]
    refine le_congr (congrAp2 (sumF (colB (eB c g))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
      (.eqRefl _) ?_
    have hK' : (lt (var 0) (Syn.shift R) :: Γ.map Fm.shift) ⊢[PRAAx] coll c g (Syn.shift N) (Syn.shift x) ≐ zero := by
      have s0 : Γ.map Fm.shift ⊢[PRAAx] coll c g (Syn.shift N) (Syn.shift x) ≐ zero := by
        simpa [Fm.shift, Syn.shift, subst_ap2] using hK.shift
      exact s0.wk
    exact col_le c g hK'
  exact le_congr (rows.eqTrans fb).eqSymm (Common.mul_one_right R) cols

end Inj

end LeanProofs.IPRA.Foundations.InjectionCount
