import IPRADerivations.Core.Fubini
import IPRADerivations.Core.SumOrder
import IPRADerivations.Core.Signum
import IPRADerivations.Core.LinearCombination

/-!
# Finite unions of grid intervals and their exact length

Framework (packet `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: "For a finite
union of intervals with rational endpoints, write `|U|` for its exact rational length. ... Every
measure argument below is an identity or inequality about these finite rational sums"; reusable for
any finite-measure argument on `[0, 1]`).

Rational endpoints with a common denominator `T` are integers on the grid `{0, …, T}`. An interval
`[lo, hi)` of cells covers the cells `c` with `lo ≤ c < hi`; a finite family `j < K` of intervals
(endpoints `lo(j, x)`, `hi(j, x)`, parameter `x`) covers a cell when some member does, and the exact
length of the union is the number of covered cells `c < T` divided by `T`:

* `indB lo hi`: `[lo(j, x) ≤ c] · [c < hi(j, x)]` as a body in `(c, j, x)`;
* `measure lo hi T K x = Σ_{c<T} sg(Σ_{j<K} [lo_j ≤ c < hi_j])`, the covered cells;
* `count_le`: one interval covers at most `hi ∸ lo` cells (`count_step`, by induction on `T`);
* `subadditive`: `measure ≤ Σ_{j<K} (hi_j ∸ lo_j)`, finite subadditivity of length.

The proof of `subadditive`: a covered cell is counted at most by the number of members covering it
(`sg y ≤ y`), the double sum is exchanged (`Core/Fubini`), and each column is `count_le`.
-/

namespace LeanProofs.IPRA.Foundations.IntervalCover

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## One interval -/

section Count

variable {Γ : List (Fm PTm n)}

/-- `[lo ≤ c] · [c < hi]`. -/
abbrev cnt (lo hi c : PTm n) : PTm n := monus one (monus lo c) * sg (monus hi c)

theorem monus_mono_succ (T lo : PTm n) : Γ ⊢[PRAAx] le (monus T lo) (monus (succ T) lo) := by
  refine .orE (lt_or_le T lo) ?_ ?_
  · exact le_congr (le_of_lt Prf.hyp0).eqSymm (.eqRefl _) (zero_le _)
  · have hT := eq_add_of_le (Γ := le lo T :: Γ) Prf.hyp0
    have e : (le lo T :: Γ) ⊢[PRAAx] monus (succ T) lo ≐ succ (monus T lo) := by
      refine (congrMonus (?_ : _ ⊢[PRAAx] succ T ≐ lo + succ (monus T lo)) (.eqRefl _)).eqTrans (add_monus' _ _)
      ipra_lc natEq hT
    exact le_congr (.eqRefl _) e.eqSymm (le_succ_self _)

theorem le_of_le_succ_add {S a : PTm n} (h : Γ ⊢[PRAAx] le S a) : Γ ⊢[PRAAx] le (S + one) (succ a) :=
  le_congr (succ_eq_add_one S) (.eqRefl _) ((succ_monus_succ _ _).eqTrans h)

/-- The induction step of `count_le`. -/
theorem count_step {S T lo hi : PTm n} (h1 : Γ ⊢[PRAAx] le S (monus T lo)) (h2 : Γ ⊢[PRAAx] le S (monus hi lo)) :
    Γ ⊢[PRAAx] le (S + cnt lo hi T) (monus (succ T) lo) ⋏ le (S + cnt lo hi T) (monus hi lo) := by
  -- the cases with `cnt = 0`
  have zero_case : ∀ {Δ : List (Fm PTm n)}, (∀ ψ, (Γ ⊢[PRAAx] ψ) → (Δ ⊢[PRAAx] ψ)) →
      (Δ ⊢[PRAAx] cnt lo hi T ≐ zero) →
      (Δ ⊢[PRAAx] le (S + cnt lo hi T) (monus (succ T) lo) ⋏ le (S + cnt lo hi T) (monus hi lo)) := by
    intro Δ hext hc
    have e : Δ ⊢[PRAAx] S + cnt lo hi T ≐ S := (congrAdd (.eqRefl _) hc).eqTrans (add_zero _)
    exact .andI (le_congr e.eqSymm (.eqRefl _) (le_trans (hext _ h1) (monus_mono_succ T lo)))
      (le_congr e.eqSymm (.eqRefl _) (hext _ h2))
  refine .orE (lt_or_le T lo) ?_ ?_
  · -- `T < lo`
    refine zero_case (fun ψ h => h.wk) ?_
    have e := eq_add_of_le (Γ := lt T lo :: Γ) Prf.hyp0
    have hm : (lt T lo :: Γ) ⊢[PRAAx] monus lo T ≐ succ (monus lo (succ T)) := by
      refine (congrMonus (?_ : _ ⊢[PRAAx] lo ≐ T + succ (monus lo (succ T))) (.eqRefl _)).eqTrans (add_monus' _ _)
      ipra_lc natEq e
    have h0 : (lt T lo :: Γ) ⊢[PRAAx] monus one (monus lo T) ≐ zero :=
      (congrMonus (.eqRefl _) hm).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))
    exact (congrMul h0 (.eqRefl _)).eqTrans (zero_mul _)
  · let Δ : List (Fm PTm n) := le lo T :: Γ
    have hc1 : Δ ⊢[PRAAx] monus one (monus lo T) ≐ one := (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)
    refine .orE (lt_or_le T hi) ?_ ?_
    · -- `lo ≤ T < hi`: `cnt = 1`
      let Δ' : List (Fm PTm n) := lt T hi :: Δ
      let α : PTm n := monus T lo
      let β : PTm n := monus hi (succ T)
      have e1 : Δ' ⊢[PRAAx] monus (succ T) lo ≐ succ α := by
        refine (congrMonus (?_ : _ ⊢[PRAAx] succ T ≐ lo + succ α) (.eqRefl _)).eqTrans (add_monus' _ _)
        ipra_lc natEq (eq_add_of_le (Γ := Δ') Prf.hyp1)
      have e2 : Δ' ⊢[PRAAx] monus hi lo ≐ succ (α + β) := by
        refine (congrMonus (?_ : _ ⊢[PRAAx] hi ≐ lo + succ (α + β)) (.eqRefl _)).eqTrans (add_monus' _ _)
        ipra_lc natEq (eq_add_of_le (Γ := Δ') Prf.hyp0) + natEq (eq_add_of_le (Γ := Δ') Prf.hyp1)
      have e3 : Δ' ⊢[PRAAx] monus hi T ≐ succ β := by
        refine (congrMonus (?_ : _ ⊢[PRAAx] hi ≐ T + succ β) (.eqRefl _)).eqTrans (add_monus' _ _)
        ipra_lc natEq (eq_add_of_le (Γ := Δ') Prf.hyp0)
      have hc : Δ' ⊢[PRAAx] cnt lo hi T ≐ one :=
        (congrMul hc1.wk ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) e3)).eqTrans (sg_succ _))).eqTrans (one_mul _)
      have hS : Δ' ⊢[PRAAx] le (S + one) (succ α) := le_of_le_succ_add h1.wk.wk
      have hS' : Δ' ⊢[PRAAx] le (S + cnt lo hi T) (succ α) := le_congr (congrAdd (.eqRefl _) hc).eqSymm (.eqRefl _) hS
      refine .andI (le_congr (.eqRefl _) e1.eqSymm hS') (le_congr (.eqRefl _) e2.eqSymm ?_)
      exact le_trans hS' ((succ_monus_succ _ _).eqTrans (le_add_right _ _))
    · -- `hi ≤ T`: `cnt = 0`
      refine zero_case (fun ψ h => h.wk.wk) ?_
      have hs : (le hi T :: Δ) ⊢[PRAAx] sg (monus hi T) ≐ zero := (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans sg_zero
      exact (congrMul (.eqRefl _) hs).eqTrans (mul_zero _)

end Count

/-! ## Finite families -/

section Family

variable (lo hi : PTm 2)

/-- `[lo(j, x) ≤ c] · [c < hi(j, x)]` in `(c, j, x)`. -/
def indB : PTm 3 := cnt (Syn.subst ![var 1, var 2] lo) (Syn.subst ![var 1, var 2] hi) (var 0)

theorem inst3_indB (c j x : PTm n) : inst3 (indB lo hi) c j x = cnt (inst2 lo j x) (inst2 hi j x) c := by
  have e : ∀ t : PTm 2, Syn.subst ![c, j, x] (Syn.subst ![var 1, var 2] t) = Syn.subst ![j, x] t := fun t => by
    rw [Syn.subst_subst]; congr 1; funext i; fin_cases i <;> rfl
  simp [inst3, inst2, indB, cnt, Signum.sg, e]

/-- `sg(Σ_{j<K} [lo_j ≤ c < hi_j])` in `(c, ⟨K, x⟩)`. -/
def covB : PTm 2 := sg (oB (indB lo hi))

/-- The number of cells `c < T` covered by the intervals `j < K`. -/
def measure (T K x : PTm n) : PTm n := ap2 (sumF (covB lo hi)) T (pairT K x)

/-- The lengths `hi_j ∸ lo_j`. -/
def lenB : PTm 2 := monus hi lo

/-- The column sum `Σ_{c<T} [lo ≤ c < hi]` for the interval `z = ⟨j, x⟩`. -/
abbrev colSum (T z : PTm n) : PTm n := ap2 (sumF (colB (indB lo hi))) T z

/-- The invariant of `count_le`. -/
def countInv (T z : PTm n) : Fm PTm n :=
  le (colSum lo hi T z) (monus T (inst2 lo (fstT z) (sndT z))) ⋏
    le (colSum lo hi T z) (monus (inst2 hi (fstT z) (sndT z)) (inst2 lo (fstT z) (sndT z)))

theorem subst_countInv {k : ℕ} (σ : Fin n → PTm k) (T z : PTm n) :
    (countInv lo hi T z).subst σ = countInv lo hi (Syn.subst σ T) (Syn.subst σ z) := by
  simp [countInv]

/-- One interval covers at most `hi ∸ lo` cells. -/
theorem count_le {Γ : List (Fm PTm n)} (T z : PTm n) :
    Γ ⊢[PRAAx] le (colSum lo hi T z) (monus (inst2 hi (fstT z) (sndT z)) (inst2 lo (fstT z) (sndT z))) := by
  have hall : Γ ⊢[PRAAx] Fm.all (countInv lo hi (var 0) (Syn.shift z)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · rw [subst_countInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact .andI (le_congr (sum_zero _ _).eqSymm (.eqRefl _) (zero_le _))
        (le_congr (sum_zero _ _).eqSymm (.eqRefl _) (zero_le _))
    · rw [subst_countInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have ih : (countInv lo hi (var 0) (Syn.shift z) :: Γ.map Fm.shift) ⊢[PRAAx]
          countInv lo hi (var 0) (Syn.shift z) := Prf.hyp0
      have st := count_step (Prf.andE₁ ih) (Prf.andE₂ ih)
      have es := sum_succ' (Γ := countInv lo hi (var 0) (Syn.shift z) :: Γ.map Fm.shift) (colB (indB lo hi))
        (var 0) (Syn.shift z)
      rw [inst2_colB, inst3_indB] at es
      exact .andI (le_congr es.eqSymm (.eqRefl _) (Prf.andE₁ st)) (le_congr es.eqSymm (.eqRefl _) (Prf.andE₂ st))
  have a := Prf.allE T hall
  rw [subst_countInv] at a
  simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at a
  exact Prf.andE₂ a

theorem sg_le_self {Γ : List (Fm PTm n)} (y : PTm n) : Γ ⊢[PRAAx] le (sg y) y := by
  refine .orE (zero_or_succ y) ?_ ?_
  · exact le_congr ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans sg_zero).eqSymm
      (.eqRefl _) (zero_le _)
  · refine le_congr ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans (sg_succ _)).eqSymm
      (.eqRefl _) ?_
    exact le_congr (.eqRefl _) Prf.hyp0.eqSymm ((succ_monus_succ _ _).eqTrans (zero_monus _))

/-- Finite subadditivity of length: the covered cells are at most the total length. -/
theorem subadditive {Γ : List (Fm PTm n)} (T K x : PTm n) :
    Γ ⊢[PRAAx] le (measure lo hi T K x) (ap2 (sumF (lenB lo hi)) K x) := by
  -- a covered cell is counted at most by its covering members
  have s1 : Γ ⊢[PRAAx] le (measure lo hi T K x) (ap2 (sumF (oB (indB lo hi))) T (pairT K x)) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    have e : inst2 (covB lo hi) (var 0) (Syn.shift (pairT K x)) =
        sg (inst2 (oB (indB lo hi)) (var 0) (Syn.shift (pairT K x))) := by
      simp [covB, inst2, Signum.sg]
    rw [e]
    exact sg_le_self _
  -- exchange the double sum
  have s2 := fubini (Γ := Γ) (indB lo hi) T K x
  -- each column is a single interval
  have s3 : Γ ⊢[PRAAx] le (ap2 (sumF (pB (indB lo hi))) K (pairT T x)) (ap2 (sumF (lenB lo hi)) K x) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_pB]
    have hz : (lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) ⊢[PRAAx]
        pairT (var 0) (sndT (Syn.shift (pairT T x))) ≐ pairT (var 0) (Syn.shift x) :=
      congrPairT (.eqRefl _) (by rw [shift_pairT]; exact snd_pair _ _)
    have hT : (lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) ⊢[PRAAx]
        fstT (Syn.shift (pairT T x)) ≐ Syn.shift T := by rw [shift_pairT]; exact fst_pair _ _
    have c := count_le lo hi (Γ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) (Syn.shift T)
      (pairT (var 0) (Syn.shift x))
    have hlen : (lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) ⊢[PRAAx]
        monus (inst2 hi (fstT (pairT (var 0) (Syn.shift x))) (sndT (pairT (var 0) (Syn.shift x))))
          (inst2 lo (fstT (pairT (var 0) (Syn.shift x))) (sndT (pairT (var 0) (Syn.shift x)))) ≐
        inst2 (lenB lo hi) (var 0) (Syn.shift x) := by
      have e : inst2 (lenB lo hi) (var 0) (Syn.shift x) = monus (inst2 hi (var 0) (Syn.shift x)) (inst2 lo (var 0) (Syn.shift x)) := by
        simp [lenB, inst2]
      rw [e]
      exact congrMonus (congrInst2 hi (fst_pair _ _) (snd_pair _ _)) (congrInst2 lo (fst_pair _ _) (snd_pair _ _))
    exact le_congr (congrAp2 (sumF (colB (indB lo hi))) hT hz).eqSymm hlen c
  exact le_trans s1 (le_congr s2.eqSymm (.eqRefl _) s3)

end Family

/-! ## Unions of arbitrary cell sets -/

/-- The union bound for cell sets given by `0/1` indicators `a(c, j, x)`: the number of cells `c < T`
in some set `j < K` is at most `Σ_{j<K} Σ_{c<T} a(c, j, x)`, the sum of the sizes of the sets. -/
theorem union_le (a : PTm 3) {Γ : List (Fm PTm n)} (T K x : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF (sg (oB a))) T (pairT K x)) (ap2 (sumF (pB a)) K (pairT T x)) := by
  have s1 : Γ ⊢[PRAAx] le (ap2 (sumF (sg (oB a))) T (pairT K x)) (ap2 (sumF (oB a)) T (pairT K x)) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    have e : inst2 (sg (oB a)) (var 0) (Syn.shift (pairT K x)) = sg (inst2 (oB a) (var 0) (Syn.shift (pairT K x))) := by
      simp [inst2, Signum.sg]
    rw [e]
    exact sg_le_self _
  exact le_congr (.eqRefl _) (fubini (Γ := Γ) a T K x) s1

end LeanProofs.IPRA.Foundations.IntervalCover
