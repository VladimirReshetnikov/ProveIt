import IPRADerivations.Foundations.IntervalCover
import IPRADerivations.Foundations.LatticeCount
import IPRADerivations.Foundations.InjectionCount
import IPRADerivations.Core.Reindex
import IPRADerivations.Core.Header

/-!
# Additivity of length for disjoint finite unions

Framework (packet `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: "For a finite union of
intervals with rational endpoints, write `|U|` for its exact rational length"; used in (K8): "They are
pairwise disjoint at each fixed scale … `Lt_k/128 ≤ |E_k(J)|`").

On the grid `{0, …, T}` of `Foundations/IntervalCover`, a family of intervals `[lo_j, hi_j)`, `j < K`, with
`hi_j ≤ T` and no cell in two members has length equal to the total length (`additive`):

  `measure lo hi T K x = Σ_{j<K} (hi_j ∸ lo_j)`,

the companion of `IntervalCover.subadditive`. The hypotheses are closed equations:

* `Σ_{j<K} (hi_j ∸ T) = 0` (every member inside the grid);
* `Σ_{c<T} Σ_{j<K} Σ_{j'<j} [c ∈ I_{j'}][c ∈ I_j] = 0` (no cell covered twice).

The general `at_most_one`: a family of bits `[a(j)]` with no two set has at most one set,
`Σ_{j<K}[a(j)] ≤ 1` (the row of `j` is `[a(j)] Σ_{j'<j} [a(j')]`, so a vanishing row empties the prefix).
-/

namespace LeanProofs.IPRA.Foundations.IntervalAdditive

open_ipra
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (sg_bit shift_inst2')
open LeanProofs.IPRA.Foundations.IntervalCover (cnt indB inst3_indB covB measure lenB)
open LeanProofs.IPRA.Foundations.LatticeCount (icB icS exact_count)
open LeanProofs.IPRA.Foundations.InjectionCount (term_zero)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## At most one bit -/

section AMO

variable (a : PTm 2)

/-- `[a(j')] [a(j)]` over `0 = j'`, `1 = ⟨j, y⟩`. -/
def prB : PTm 2 := sg (Syn.subst ![var 0, sndT (var 1)] a) * sg (Syn.subst ![fstT (var 1), sndT (var 1)] a)

theorem inst2_prB (j' z : PTm n) :
    inst2 (prB a) j' z = sg (inst2 a j' (sndT z)) * sg (inst2 a (fstT z) (sndT z)) := by
  simp only [inst2, prB, PTm.subst_mul, Signum.sg, PTm.subst_monus, subst_reindex2]
  simp

/-- The pairs below `j`: `Σ_{j'<j} [a(j')][a(j)]` over `0 = j`, `1 = y`. -/
abbrev rwB : PTm 2 := ap2 (sumF (prB a)) (var 0) (pairT (var 0) (var 1))

theorem inst2_rwB (j y : PTm n) : inst2 (rwB a) j y = ap2 (sumF (prB a)) j (pairT j y) := by
  simp [inst2, subst_ap2]

/-- `[a(j)]` as a body. -/
abbrev sgaB : PTm 2 := sg a

theorem inst2_sgaB (j y : PTm n) : inst2 (sgaB a) j y = sg (inst2 a j y) := by simp [inst2, Signum.sg]

/-- The row of `j` is `[a(j)] Σ_{j'<j} [a(j')]`. -/
theorem row_eq (j y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (prB a)) j (pairT j y) ≐ sg (inst2 a j y) * ap2 (sumF (sgaB a)) j y := by
  refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_prB, inst2_sgaB, show Syn.shift (pairT j y) = pairT (Syn.shift j) (Syn.shift y) by simp [Syn.shift],
    show Syn.shift (sg (inst2 a j y)) = sg (inst2 a (Syn.shift j) (Syn.shift y)) by
      rw [← shift_inst2']; simp [Syn.shift, Signum.sg]]
  refine (congrMul (congrSg (congrInst2 a (.eqRefl _) (snd_pair _ _)))
    (congrSg (congrInst2 a (fst_pair _ _) (snd_pair _ _)))).eqTrans (mul_comm _ _)

/-- `K' ≤ K → Σ_{j<K'} [a(j)] ≤ 1`. -/
def amoInv (K' K y : PTm n) : Fm PTm n := le K' K ⟶ le (ap2 (sumF (sgaB a)) K' y) one

@[simp] theorem subst_amoInv {k : ℕ} (σ : Fin n → PTm k) (K' K y : PTm n) :
    (amoInv a K' K y).subst σ = amoInv a (Syn.subst σ K') (Syn.subst σ K) (Syn.subst σ y) := by
  simp [amoInv, subst_ap2]

theorem amoInv_QF (K' K y : PTm n) : (amoInv a K' K y).QF := by
  unfold amoInv; exact ⟨le_QF _ _, le_QF _ _⟩

theorem amo_step {K' K y : PTm n} (hD : Γ ⊢[PRAAx] ap2 (sumF (rwB a)) K y ≐ zero) (ih : Γ ⊢[PRAAx] amoInv a K' K y) :
    Γ ⊢[PRAAx] amoInv a (succ K') K y := by
  refine .impI ?_
  let Δ : List (Fm PTm n) := le (succ K') K :: Γ
  have hK : Δ ⊢[PRAAx] lt K' K := Prf.hyp0
  have ih' : Δ ⊢[PRAAx] le (ap2 (sumF (sgaB a)) K' y) one := Prf.impE ih.wk (le_trans (le_succ_self K') Prf.hyp0)
  have es := (sum_succ' (Γ := Δ) (sgaB a) K' y).eqTrans (congrAdd (.eqRefl _) (by rw [inst2_sgaB]; exact .eqRefl _))
  refine le_congr es.eqSymm (.eqRefl _) ?_
  refine .orE (sg_bit (Γ := Δ) (inst2 a K' y)) ?_ ?_
  · have h0 : ((sg (inst2 a K' y) ≐ zero) :: Δ) ⊢[PRAAx] sg (inst2 a K' y) ≐ zero := Prf.hyp0
    exact le_congr ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) h0.eqSymm)) (.eqRefl _) ih'.wk
  · let Δ' : List (Fm PTm n) := (sg (inst2 a K' y) ≐ one) :: Δ
    have h1 : Δ' ⊢[PRAAx] sg (inst2 a K' y) ≐ one := Prf.hyp0
    have rz := term_zero (rwB a) (hK.wk : Δ' ⊢[PRAAx] lt K' K) hD.wk.wk
    rw [inst2_rwB] at rz
    have z : Δ' ⊢[PRAAx] ap2 (sumF (sgaB a)) K' y ≐ zero :=
      (one_mul _).eqSymm.eqTrans ((congrMul h1.eqSymm (.eqRefl _)).eqTrans ((row_eq a K' y).eqSymm.eqTrans rz))
    exact le_congr ((congrAdd z h1).eqTrans (zero_add _)).eqSymm (.eqRefl _) (le_refl _)

/-- No two bits set: `Σ_{j<K}[a(j)] ≤ 1`. -/
theorem at_most_one {K y : PTm n} (hD : Γ ⊢[PRAAx] ap2 (sumF (rwB a)) K y ≐ zero) :
    Γ ⊢[PRAAx] le (ap2 (sumF (sgaB a)) K y) one := by
  have hall : Γ ⊢[PRAAx] Fm.all (amoInv a (var 0) (Syn.shift K) (Syn.shift y)) := by
    refine PRA.qfInd _ (amoInv_QF _ _ _ _) ?_ ?_
    · rw [subst_amoInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact .impI (le_congr (sum_zero _ _).eqSymm (.eqRefl _) (zero_le _))
    · rw [subst_amoInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have hD' : (amoInv a (var 0) (Syn.shift K) (Syn.shift y) :: Γ.map Fm.shift) ⊢[PRAAx]
          ap2 (sumF (rwB a)) (Syn.shift K) (Syn.shift y) ≐ zero := by
        have s0 : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF (rwB a)) (Syn.shift K) (Syn.shift y) ≐ zero := by
          simpa [Fm.shift, Syn.shift, subst_ap2] using hD.shift
        exact s0.wk
      exact amo_step a hD' Prf.hyp0
  have h := Prf.allE K hall
  rw [subst_amoInv] at h
  simp only [Syn.subst_inst_shift] at h
  exact Prf.impE h (le_refl K)

end AMO

/-! ## Bits of the cell indicator -/

theorem sg_one_eq : Γ ⊢[PRAAx] sg (one : PTm n) ≐ one := sg_succ _

/-- `cnt lo hi c` is a bit: `sg(cnt) = cnt`. -/
theorem cnt_bit (lo hi c : PTm n) : Γ ⊢[PRAAx] sg (cnt lo hi c) ≐ cnt lo hi c := by
  have b1 : Γ ⊢[PRAAx] (monus one (monus lo c) ≐ zero) ⋎ (monus one (monus lo c) ≐ one) := by
    refine .orE (zero_or_succ (monus lo c)) ?_ ?_
    · exact .orI₂ ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _))
    · exact .orI₁ ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _)))
  refine .orE b1 ?_ ?_
  · have z : ((monus one (monus lo c) ≐ zero) :: Γ) ⊢[PRAAx] cnt lo hi c ≐ zero :=
      (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
    exact (congrSg z).eqTrans (sg_zero.eqTrans z.eqSymm)
  · let Δ : List (Fm PTm n) := (monus one (monus lo c) ≐ one) :: Γ
    have o : Δ ⊢[PRAAx] cnt lo hi c ≐ sg (monus hi c) := (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _)
    refine .orE (sg_bit (Γ := Δ) (monus hi c)) ?_ ?_
    · have z : ((sg (monus hi c) ≐ zero) :: Δ) ⊢[PRAAx] cnt lo hi c ≐ zero := o.wk.eqTrans Prf.hyp0
      exact (congrSg z).eqTrans (sg_zero.eqTrans z.eqSymm)
    · have z : ((sg (monus hi c) ≐ one) :: Δ) ⊢[PRAAx] cnt lo hi c ≐ one := o.wk.eqTrans Prf.hyp0
      exact (congrSg z).eqTrans (sg_one_eq.eqTrans z.eqSymm)

/-- A sum of bits at most `1` is fixed by `sg`. -/
theorem sg_of_le_one {y : PTm n} (h : Γ ⊢[PRAAx] le y one) : Γ ⊢[PRAAx] sg y ≐ y := by
  refine .orE (zero_or_succ y) ?_ ?_
  · exact (congrSg Prf.hyp0).eqTrans (sg_zero.eqTrans (Prf.hyp0 : ((y ≐ zero) :: Γ) ⊢[PRAAx] y ≐ zero).eqSymm)
  · let Δ : List (Fm PTm n) := (y ≐ succ (pred y)) :: Γ
    have hy : Δ ⊢[PRAAx] y ≐ succ (pred y) := Prf.hyp0
    have e := natEq hy
    have h' : Δ ⊢[PRAAx] le y one := h.wk
    have p0 : Δ ⊢[PRAAx] pred y ≐ zero := by
      refine le_antisymm ?_ (zero_le _)
      ipra_le sl h' with e
    have y1 : Δ ⊢[PRAAx] y ≐ one := hy.eqTrans (congrSucc p0)
    exact (congrSg y1).eqTrans (sg_one_eq.eqTrans y1.eqSymm)

/-! ## Additivity -/

section Add

variable (lo hi : PTm 2)

/-- `[lo_j ≤ c < hi_j]` over `0 = j`, `1 = ⟨c, x⟩`. -/
def ajB : PTm 2 := cnt (Syn.subst ![var 0, sndT (var 1)] lo) (Syn.subst ![var 0, sndT (var 1)] hi) (fstT (var 1))

theorem inst2_ajB (j z : PTm n) : inst2 (ajB lo hi) j z = cnt (inst2 lo j (sndT z)) (inst2 hi j (sndT z)) (fstT z) := by
  simp only [inst2, ajB, cnt, PTm.subst_mul, Signum.sg, PTm.subst_monus, subst_reindex2]
  simp

/-- The doubly covered pairs of the cell `c`: `Σ_{j<K} Σ_{j'<j} [c ∈ I_{j'}][c ∈ I_j]` over `0 = c`, `1 = ⟨K, x⟩`. -/
abbrev ovlB : PTm 2 := ap2 (sumF (rwB (ajB lo hi))) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

theorem inst2_ovlB (c z : PTm n) :
    inst2 (ovlB lo hi) c z = ap2 (sumF (rwB (ajB lo hi))) (fstT z) (pairT c (sndT z)) := by
  simp [inst2, subst_ap2]

/-- `hi_j ∸ T` over `0 = j`, `1 = ⟨T, x⟩`. -/
def outB : PTm 2 := monus (Syn.subst ![var 0, sndT (var 1)] hi) (fstT (var 1))

theorem inst2_outB (j z : PTm n) : inst2 (outB hi) j z = monus (inst2 hi j (sndT z)) (fstT z) := by
  simp only [inst2, outB, PTm.subst_monus, subst_reindex2]
  simp

/-- A covered-cell count `Σ_{j<K} [c ∈ I_j]` is the bit sum of `ajB`. -/
theorem cover_eq (c K x : PTm n) :
    Γ ⊢[PRAAx] inst2 (oB (indB lo hi)) c (pairT K x) ≐ ap2 (sumF (sgaB (ajB lo hi))) K (pairT c x) := by
  refine (oB_at (indB lo hi) c K x).eqTrans ?_
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_rowB, inst2_sgaB, inst2_ajB, show Syn.shift (pairT c x) = pairT (Syn.shift c) (Syn.shift x) by simp [Syn.shift]]
  refine (congrInst3 (indB lo hi) (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
  rw [inst3_indB]
  refine (cnt_bit _ _ _).eqSymm.eqTrans (congrSg ?_)
  exact congrMul (congrMonus (.eqRefl _) (congrMonus (congrInst2 lo (.eqRefl _) (snd_pair _ _)).eqSymm (fst_pair _ _).eqSymm))
    (congrSg (congrMonus (congrInst2 hi (.eqRefl _) (snd_pair _ _)).eqSymm (fst_pair _ _).eqSymm))

/-- Additivity: a family of intervals inside the grid with no cell covered twice has length
`Σ_{j<K} (hi_j ∸ lo_j)`. -/
theorem additive {T K x : PTm n}
    (hT : Γ ⊢[PRAAx] ap2 (sumF (outB hi)) K (pairT T x) ≐ zero)
    (hD : Γ ⊢[PRAAx] ap2 (sumF (ovlB lo hi)) T (pairT K x) ≐ zero) :
    Γ ⊢[PRAAx] measure lo hi T K x ≐ ap2 (sumF (lenB lo hi)) K x := by
  -- each cell is covered at most once, so `sg` is the identity on its cover count
  have s1 : Γ ⊢[PRAAx] measure lo hi T K x ≐ ap2 (sumF (oB (indB lo hi))) T (pairT K x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    have e : inst2 (covB lo hi) (var 0) (Syn.shift (pairT K x)) =
        sg (inst2 (oB (indB lo hi)) (var 0) (Syn.shift (pairT K x))) := by
      simp [covB, inst2, Signum.sg]
    rw [e, show Syn.shift (pairT K x) = pairT (Syn.shift K) (Syn.shift x) by simp [Syn.shift]]
    let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift T) :: Γ.map Fm.shift
    have hD' : Θ ⊢[PRAAx] ap2 (sumF (ovlB lo hi)) (Syn.shift T) (pairT (Syn.shift K) (Syn.shift x)) ≐ zero := by
      have s0 : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF (ovlB lo hi)) (Syn.shift T) (pairT (Syn.shift K) (Syn.shift x)) ≐ zero := by
        simpa [Fm.shift, Syn.shift, subst_ap2] using hD.shift
      exact s0.wk
    have tz := term_zero (ovlB lo hi) (Prf.hyp0 : Θ ⊢[PRAAx] lt (var 0) (Syn.shift T)) hD'
    rw [inst2_ovlB] at tz
    have tz' : Θ ⊢[PRAAx] ap2 (sumF (rwB (ajB lo hi))) (Syn.shift K) (pairT (var 0) (Syn.shift x)) ≐ zero :=
      (congrAp2 (sumF (rwB (ajB lo hi))) (fst_pair _ _).eqSymm (congrPairT (.eqRefl _) (snd_pair _ _).eqSymm)).eqTrans tz
    have amo := at_most_one (ajB lo hi) tz'
    have ce := cover_eq (Γ := Θ) lo hi (var 0) (Syn.shift K) (Syn.shift x)
    exact (congrSg ce).eqTrans ((sg_of_le_one amo).eqTrans ce.eqSymm)
  -- exchange the sums and count each interval exactly
  have s2 := fubini (Γ := Γ) (indB lo hi) T K x
  have s3 : Γ ⊢[PRAAx] ap2 (sumF (pB (indB lo hi))) K (pairT T x) ≐ ap2 (sumF (lenB lo hi)) K x := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_pB, show Syn.shift (pairT T x) = pairT (Syn.shift T) (Syn.shift x) by simp [Syn.shift],
      show inst2 (lenB lo hi) (var 0 : PTm (n + 1)) (Syn.shift x) =
        monus (inst2 hi (var 0) (Syn.shift x)) (inst2 lo (var 0) (Syn.shift x)) by simp [lenB, inst2]]
    let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift
    have hT' : Θ ⊢[PRAAx] ap2 (sumF (outB hi)) (Syn.shift K) (pairT (Syn.shift T) (Syn.shift x)) ≐ zero := by
      have s0 : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF (outB hi)) (Syn.shift K) (pairT (Syn.shift T) (Syn.shift x)) ≐ zero := by
        simpa [Fm.shift, Syn.shift, subst_ap2] using hT.shift
      exact s0.wk
    have tz := term_zero (outB hi) (Prf.hyp0 : Θ ⊢[PRAAx] lt (var 0) (Syn.shift K)) hT'
    rw [inst2_outB] at tz
    have hle : Θ ⊢[PRAAx] le (inst2 hi (var 0) (Syn.shift x)) (Syn.shift T) :=
      (congrMonus (congrInst2 hi (.eqRefl _) (snd_pair _ _)) (fst_pair _ _)).eqSymm.eqTrans tz
    refine (congrAp2 (sumF (colB (indB lo hi))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
    refine (sum_congr_bounded _ icB _ (pairT (inst2 lo (var 0) (Syn.shift x)) (inst2 hi (var 0) (Syn.shift x))) _
      (.allI (.impI ?_))).eqTrans (exact_count _ _ _ hle)
    rw [inst2_colB, show Syn.shift (pairT (var 0 : PTm (n + 1)) (Syn.shift x)) = pairT (var 1) (Syn.shift (Syn.shift x)) by
        simp [Syn.shift],
      show Syn.shift (pairT (inst2 lo (var 0 : PTm (n + 1)) (Syn.shift x)) (inst2 hi (var 0) (Syn.shift x))) =
        pairT (inst2 lo (var 1) (Syn.shift (Syn.shift x))) (inst2 hi (var 1) (Syn.shift (Syn.shift x))) by
        rw [show Syn.shift (pairT (inst2 lo (var 0 : PTm (n + 1)) (Syn.shift x)) (inst2 hi (var 0) (Syn.shift x))) =
          pairT (Syn.shift (inst2 lo (var 0 : PTm (n + 1)) (Syn.shift x))) (Syn.shift (inst2 hi (var 0) (Syn.shift x))) by
            simp [Syn.shift], shift_inst2', shift_inst2']
        simp [Syn.shift]]
    refine (congrInst3 (indB lo hi) (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_indB, show inst2 icB (var 0 : PTm (n + 1 + 1))
        (pairT (inst2 lo (var 1) (Syn.shift (Syn.shift x))) (inst2 hi (var 1) (Syn.shift (Syn.shift x)))) =
        cnt (fstT (pairT (inst2 lo (var 1) (Syn.shift (Syn.shift x))) (inst2 hi (var 1) (Syn.shift (Syn.shift x)))))
          (sndT (pairT (inst2 lo (var 1) (Syn.shift (Syn.shift x))) (inst2 hi (var 1) (Syn.shift (Syn.shift x))))) (var 0) by
        simp [inst2, Signum.sg, cnt]]
    exact congrMul (congrMonus (.eqRefl _) (congrMonus (fst_pair _ _).eqSymm (.eqRefl _)))
      (congrSg (congrMonus (snd_pair _ _).eqSymm (.eqRefl _)))
  exact s1.eqTrans (s2.eqTrans s3)

end Add

end LeanProofs.IPRA.Foundations.IntervalAdditive
