import IPRADerivations.Foundations.LeastBoundedWitness
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.SumReflect

/-!
# Frontier soundness: rank induction over bounded states

Packet: `foundations/ipra_uniformity_framework_2026-11-15`, `report.tex`, Definition `def:frontier` and
Theorem `thm:frontier` ("Frontier soundness"), with its corollary "DAG certificate reuse".

States are the numbers `s ≤ S`; `ρ(s, x)` is a rank, `p(s, x)` the bit of the desired property (`P(s)` is
`p(s, x) ≠ 0`), `A(s, x)` the acceptance bit of terminal states, `d(s, x)` the branching bound and
`T(i, ⟨s, x⟩)` the `i`-th successor. A frontier certificate consists of the three clauses, for `s ≤ S`:

* terminal soundness: `A(s) ≠ 0 → P(s)`;
* descent: `A(s) = 0 → ∀ i < d(s). T(s, i) ≤ S ∧ ρ(T(s, i)) < ρ(s)`;
* local soundness: `A(s) = 0 → (∀ i < d(s). P(T(s, i))) → P(s)`.

`frontier_soundness`: from derivations of the three clauses, `∀ s ≤ S. P(s)`.

The proof has two parts.

* `rank_induction`: if `∀ s ≤ S. [∀ t ≤ S. ρ(t) < ρ(s) → P(t)] → P(s)` (the formula `Loc`), then
  `∀ s ≤ S. P(s)`. The invariant "every state of rank below `r` satisfies `P`" (`Low`) has a bounded
  quantifier, so the induction on `r` is carried by its bit: with
  `viol(s, ⟨r, x⟩) = ((ρ(s) + 1) ∸ r) + p(s)`, which vanishes exactly at a state of rank below `r` violating
  `P`, the invariant is the equation `1 ∸ fnd viol (S + 1) ⟨r, x⟩ = 1` of `LeastBoundedWitness` (`LevelBit`),
  and quantifier-free induction applies (`level_all`). The level `r = ρ(s) + 1` gives `P(s)`.
* `loc_of_frontier`: a frontier certificate implies `Loc`, by cases on the acceptance bit.

The condition `d(s) > 0` of the packet is not needed. For a finite dependency graph with a topological rank
(the corollary) the predecessors are the successors and `rank_induction` applies as it stands.
-/

namespace LeanProofs.IPRA.Foundations.FrontierSoundness

open_ipra exports
open LeanProofs.IPRA.Foundations.LeastBoundedWitness (fnd NoW all_of_bit bit_of_all)

variable {n : ℕ} {Γ : List (Fm PTm n)} {ρ p A d T : PTm 2}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Syntax -/

theorem up_shift {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  simp [Syn.subst_shift, Syn.shift_subst]

theorem shift_succ' (t : PTm n) : Syn.shift (succ t) = succ (Syn.shift t) := by simp [Syn.shift]

theorem le_of_lt_succ' {a b : PTm n} (h : Γ ⊢[PRAAx] lt a (succ b)) : Γ ⊢[PRAAx] le a b :=
  Order.le_of_lt_succ h

theorem lt_succ_of_le' {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] lt a (succ b) :=
  Order.lt_succ_of_le h

/-- Every state `t ≤ S` of rank below `b` satisfies `P`. -/
def Low (ρ p : PTm 2) (S x b : PTm n) : Fm PTm n :=
  Fm.all (le (var 0) (Syn.shift S) ⟶ lt (inst2 ρ (var 0) (Syn.shift x)) (Syn.shift b) ⟶
    neg (inst2 p (var 0) (Syn.shift x) ≐ zero))

theorem subst_Low {m : ℕ} (σ : Fin n → PTm m) (S x b : PTm n) :
    (Low ρ p S x b).subst σ = Low ρ p (Syn.subst σ S) (Syn.subst σ x) (Syn.subst σ b) := by
  simp [Low, up_shift, subst_le, subst_lt, subst_inst2, subst_neg]

theorem shift_Low (S x b : PTm n) :
    Fm.shift (Low ρ p S x b) = Low ρ p (Syn.shift S) (Syn.shift x) (Syn.shift b) := by
  unfold Fm.shift
  rw [subst_Low]
  rfl

/-- The local rule: a state all of whose lower-rank states satisfy `P` satisfies `P`. -/
def Loc (ρ p : PTm 2) (S x : PTm n) : Fm PTm n :=
  Fm.all (le (var 0) (Syn.shift S) ⟶
    Low ρ p (Syn.shift S) (Syn.shift x) (inst2 ρ (var 0) (Syn.shift x)) ⟶
    neg (inst2 p (var 0) (Syn.shift x) ≐ zero))

theorem subst_Loc {m : ℕ} (σ : Fin n → PTm m) (S x : PTm n) :
    (Loc ρ p S x).subst σ = Loc ρ p (Syn.subst σ S) (Syn.subst σ x) := by
  simp [Loc, subst_Low, up_shift, subst_le, subst_inst2, subst_neg]

theorem shift_Loc (S x : PTm n) : Fm.shift (Loc ρ p S x) = Loc ρ p (Syn.shift S) (Syn.shift x) := by
  unfold Fm.shift
  rw [subst_Loc]
  rfl

/-! ## The invariant `Low` -/

theorem low_intro {S x b : PTm n}
    (h : (lt (inst2 ρ (var 0) (Syn.shift x)) (Syn.shift b) :: le (var 0) (Syn.shift S) :: Γ.map Fm.shift)
      ⊢[PRAAx] neg (inst2 p (var 0) (Syn.shift x) ≐ zero)) :
    Γ ⊢[PRAAx] Low ρ p S x b := by
  unfold Low
  exact .allI (.impI (.impI h))

theorem low_at {S x b t : PTm n} (h : Γ ⊢[PRAAx] Low ρ p S x b) (ht : Γ ⊢[PRAAx] le t S)
    (hr : Γ ⊢[PRAAx] lt (inst2 ρ t x) b) : Γ ⊢[PRAAx] neg (inst2 p t x ≐ zero) := by
  unfold Low at h
  have a := Prf.allE t h
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_lt, subst_neg, subst_inst2, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at a
  exact Prf.impE (Prf.impE a ht) hr

theorem low_zero {S x : PTm n} : Γ ⊢[PRAAx] Low ρ p S x zero := by
  refine low_intro ?_
  have e : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
  rw [e]
  exact succ_ne_zero' _ (Prf.eqTrans (Prf.eqSymm (monus_zero _)) Prf.hyp0)

theorem low_mono {S x b c : PTm n} (h : Γ ⊢[PRAAx] Low ρ p S x c) (hbc : Γ ⊢[PRAAx] le b c) :
    Γ ⊢[PRAAx] Low ρ p S x b := by
  refine low_intro ?_
  have h' := h.shift
  rw [shift_Low] at h'
  have hbc' := hbc.shift
  simp only [Fm.shift, subst_le] at hbc'
  exact low_at h'.wk.wk Prf.hyp1 (le_trans Prf.hyp0 hbc'.wk.wk)

/-- One level up: from `Low` at `r` and the local rule, `Low` at `r + 1`. -/
theorem low_succ {S x r : PTm n} (hloc : Γ ⊢[PRAAx] Loc ρ p S x) (hl : Γ ⊢[PRAAx] Low ρ p S x r) :
    Γ ⊢[PRAAx] Low ρ p S x (succ r) := by
  refine low_intro ?_
  rw [shift_succ']
  have hl' := hl.shift
  rw [shift_Low] at hl'
  unfold Loc at hloc
  have c := hloc.allOpen
  exact Prf.impE (Prf.impE c.wk.wk Prf.hyp1) (low_mono hl'.wk.wk (le_of_lt_succ' Prf.hyp0))

/-! ## The violation term and the level bit -/

/-- `g(i, snd y)`. -/
def rdB (g : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] g

theorem inst2_rdB (g : PTm 2) (i y : PTm n) : inst2 (rdB g) i y = inst2 g i (sndT y) := by
  simp only [inst2, rdB, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

/-- `viol(s, ⟨r, x⟩) = ((ρ(s, x) + 1) ∸ r) + p(s, x)`: zero exactly when `ρ(s) < r` and `p(s) = 0`. -/
def viol (ρ p : PTm 2) : PTm 2 := monus (succ (rdB ρ)) (fstT (var 1)) + rdB p

theorem inst2_viol (s y : PTm n) :
    inst2 (viol ρ p) s y = monus (succ (inst2 (rdB ρ) s y)) (fstT y) + inst2 (rdB p) s y := by
  simp [inst2, viol]

theorem viol_at (s r x : PTm n) :
    Γ ⊢[PRAAx] inst2 (viol ρ p) s (pairT r x) ≐ monus (succ (inst2 ρ s x)) r + inst2 p s x := by
  rw [inst2_viol, inst2_rdB, inst2_rdB]
  exact congrAdd (congrMonus (congrSucc (congrInst2 ρ (.eqRefl s) (snd_pair r x))) (fst_pair r x))
    (congrInst2 p (.eqRefl s) (snd_pair r x))

/-- No violation at `t` gives `P(t)` for `t ≤ S` of rank below `r`. -/
theorem viol_rule {S x r t : PTm n}
    (a : Γ ⊢[PRAAx] lt t (succ S) ⟶ neg (inst2 (viol ρ p) t (pairT r x) ≐ zero))
    (ht : Γ ⊢[PRAAx] le t S) (hr : Γ ⊢[PRAAx] lt (inst2 ρ t x) r) :
    Γ ⊢[PRAAx] neg (inst2 p t x ≐ zero) := by
  refine Prf.impI ?_
  have hm : ((inst2 p t x ≐ zero) :: Γ) ⊢[PRAAx] monus (succ (inst2 ρ t x)) r ≐ zero := hr.wk
  have hv : ((inst2 p t x ≐ zero) :: Γ) ⊢[PRAAx] inst2 (viol ρ p) t (pairT r x) ≐ zero :=
    (viol_at t r x).eqTrans ((congrAdd hm Prf.hyp0).eqTrans (add_zero zero))
  exact Prf.impE (Prf.impE a.wk (lt_succ_of_le' ht).wk) hv

/-- A state of the range that is no counterexample to `Low` is no violation. -/
theorem low_viol {S x r t : PTm n} (hl : Γ ⊢[PRAAx] Low ρ p S x r) (hlt : Γ ⊢[PRAAx] lt t (succ S)) :
    Γ ⊢[PRAAx] neg (inst2 (viol ρ p) t (pairT r x) ≐ zero) := by
  refine Prf.impI ?_
  have hv : ((inst2 (viol ρ p) t (pairT r x) ≐ zero) :: Γ) ⊢[PRAAx]
      monus (succ (inst2 ρ t x)) r + inst2 p t x ≐ zero := (viol_at t r x).eqSymm.eqTrans Prf.hyp0
  exact Prf.impE (low_at hl.wk (le_of_lt_succ' hlt).wk (add_eq_zero_left hv)) (add_eq_zero_right hv)

theorem low_of_now {S x r : PTm n} (h : Γ ⊢[PRAAx] NoW (viol ρ p) (succ S) (pairT r x)) :
    Γ ⊢[PRAAx] Low ρ p S x r := by
  refine low_intro ?_
  have b := h.allOpen
  rw [shift_succ', shift_pairT] at b
  exact viol_rule b.wk.wk Prf.hyp1 Prf.hyp0

theorem now_of_low {S x r : PTm n} (hl : Γ ⊢[PRAAx] Low ρ p S x r) :
    Γ ⊢[PRAAx] NoW (viol ρ p) (succ S) (pairT r x) := by
  refine .allI (.impI ?_)
  rw [shift_succ', shift_pairT]
  have hl' := hl.shift
  rw [shift_Low] at hl'
  exact low_viol hl'.wk Prf.hyp0

/-- The quantifier-free form of `Low ρ p S x r`. -/
abbrev LevelBit (ρ p : PTm 2) (S x r : PTm n) : Fm PTm n :=
  monus (succ zero) (fnd (viol ρ p) (succ S) (pairT r x)) ≐ succ zero

theorem low_of_bit {S x r : PTm n} (h : Γ ⊢[PRAAx] LevelBit ρ p S x r) : Γ ⊢[PRAAx] Low ρ p S x r :=
  low_of_now (all_of_bit h)

theorem bit_of_low {S x r : PTm n} (h : Γ ⊢[PRAAx] Low ρ p S x r) : Γ ⊢[PRAAx] LevelBit ρ p S x r :=
  bit_of_all (now_of_low h)

/-! ## The induction on the level -/

theorem level_all {S x : PTm n} (hloc : Γ ⊢[PRAAx] Loc ρ p S x) :
    Γ ⊢[PRAAx] Fm.all (LevelBit ρ p (Syn.shift S) (Syn.shift x) (var 0)) := by
  refine PRA.qfInd _ trivial ?_ ?_
  · have e : (LevelBit ρ p (Syn.shift S) (Syn.shift x) (var 0)).subst (Syn.inst zero) =
        LevelBit ρ p S x zero := by simp
    rw [e]
    exact bit_of_low low_zero
  · have e : (LevelBit ρ p (Syn.shift S) (Syn.shift x) (var 0)).subst (Syn.repl (succ (var 0))) =
        LevelBit ρ p (Syn.shift S) (Syn.shift x) (succ (var 0)) := by simp
    rw [e]
    have hloc' := hloc.shift
    rw [shift_Loc] at hloc'
    exact bit_of_low (low_succ hloc'.wk (low_of_bit Prf.hyp0))

/-- Every level holds. -/
theorem level {S x : PTm n} (hloc : Γ ⊢[PRAAx] Loc ρ p S x) (r : PTm n) : Γ ⊢[PRAAx] Low ρ p S x r := by
  have a := Prf.allE r (level_all hloc)
  have e : (LevelBit ρ p (Syn.shift S) (Syn.shift x) (var 0)).subst (Syn.inst r) = LevelBit ρ p S x r := by
    simp
  rw [e] at a
  exact low_of_bit a

/-- Rank induction at a state: from the local rule, `P(s)` for every `s ≤ S`. -/
theorem rank_induction_at {S x s : PTm n} (hloc : Γ ⊢[PRAAx] Loc ρ p S x) (hs : Γ ⊢[PRAAx] le s S) :
    Γ ⊢[PRAAx] neg (inst2 p s x ≐ zero) :=
  low_at (level hloc (succ (inst2 ρ s x))) hs (lt_succ_of_le' (le_refl _))

/-- Rank induction over bounded states: `Loc` gives `∀ s ≤ S. P(s)`. -/
theorem rank_induction {S x : PTm n} (hloc : Γ ⊢[PRAAx] Loc ρ p S x) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift S) ⟶ neg (inst2 p (var 0) (Syn.shift x) ≐ zero)) := by
  refine .allI (.impI ?_)
  have hloc' := hloc.shift
  rw [shift_Loc] at hloc'
  exact rank_induction_at hloc'.wk Prf.hyp0

/-! ## Frontier certificates -/

/-- Descent at `s`: every successor is a state of smaller rank. -/
def DescAt (ρ d T : PTm 2) (S x s : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift (inst2 d s x)) ⟶
    (le (inst2 T (var 0) (Syn.shift (pairT s x))) (Syn.shift S) ⋏
      lt (inst2 ρ (inst2 T (var 0) (Syn.shift (pairT s x))) (Syn.shift x)) (Syn.shift (inst2 ρ s x))))

/-- Every successor of `s` satisfies `P`. -/
def SuccHold (p d T : PTm 2) (x s : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift (inst2 d s x)) ⟶
    neg (inst2 p (inst2 T (var 0) (Syn.shift (pairT s x))) (Syn.shift x) ≐ zero))

/-- If the successors of `s` descend and all lower-rank states satisfy `P`, every successor does. -/
theorem succ_hold {S x s : PTm n} (hd : Γ ⊢[PRAAx] DescAt ρ d T S x s)
    (hl : Γ ⊢[PRAAx] Low ρ p S x (inst2 ρ s x)) : Γ ⊢[PRAAx] SuccHold p d T x s := by
  unfold SuccHold
  unfold DescAt at hd
  refine .allI (.impI ?_)
  have b : (lt (var 0) (Syn.shift (inst2 d s x)) :: Γ.map Fm.shift) ⊢[PRAAx]
      (le (inst2 T (var 0) (Syn.shift (pairT s x))) (Syn.shift S) ⋏
        lt (inst2 ρ (inst2 T (var 0) (Syn.shift (pairT s x))) (Syn.shift x)) (Syn.shift (inst2 ρ s x))) :=
    Prf.impE hd.allOpen.wk Prf.hyp0
  have hl' := hl.shift
  rw [shift_Low] at hl'
  exact low_at hl'.wk (Prf.andE₁ b) (Prf.andE₂ b)

/-- The three clauses at one state give the local rule there. -/
theorem loc_case {S x s : PTm n} (hlow : Γ ⊢[PRAAx] Low ρ p S x (inst2 ρ s x))
    (hT : Γ ⊢[PRAAx] neg (inst2 A s x ≐ zero) ⟶ neg (inst2 p s x ≐ zero))
    (hD : Γ ⊢[PRAAx] (inst2 A s x ≐ zero) ⟶ DescAt ρ d T S x s)
    (hL : Γ ⊢[PRAAx] (inst2 A s x ≐ zero) ⟶ SuccHold p d T x s ⟶ neg (inst2 p s x ≐ zero)) :
    Γ ⊢[PRAAx] neg (inst2 p s x ≐ zero) := by
  refine .orE (zero_or_succ (inst2 A s x)) ?_ ?_
  · exact Prf.impE (Prf.impE hL.wk Prf.hyp0) (succ_hold (Prf.impE hD.wk Prf.hyp0) hlow.wk)
  · refine Prf.impE hT.wk (Prf.impI ?_)
    exact succ_ne_zero' _ (Prf.eqTrans (Prf.eqSymm Prf.hyp1) Prf.hyp0)

/-- A frontier certificate gives the local rule. -/
theorem loc_of_frontier {S x : PTm n}
    (hT : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift S) ⟶ neg (inst2 A (var 0) (Syn.shift x) ≐ zero) ⟶
      neg (inst2 p (var 0) (Syn.shift x) ≐ zero)))
    (hD : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift S) ⟶ (inst2 A (var 0) (Syn.shift x) ≐ zero) ⟶
      DescAt ρ d T (Syn.shift S) (Syn.shift x) (var 0)))
    (hL : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift S) ⟶ (inst2 A (var 0) (Syn.shift x) ≐ zero) ⟶
      SuccHold p d T (Syn.shift x) (var 0) ⟶ neg (inst2 p (var 0) (Syn.shift x) ≐ zero))) :
    Γ ⊢[PRAAx] Loc ρ p S x := by
  unfold Loc
  refine .allI (.impI (.impI ?_))
  exact loc_case Prf.hyp0 (Prf.impE hT.allOpen.wk.wk Prf.hyp1) (Prf.impE hD.allOpen.wk.wk Prf.hyp1)
    (Prf.impE hL.allOpen.wk.wk Prf.hyp1)

/-- `thm:frontier`: a valid frontier certificate implies `P(s)` for every state `s ≤ S`. -/
theorem frontier_soundness {S x : PTm n}
    (hT : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift S) ⟶ neg (inst2 A (var 0) (Syn.shift x) ≐ zero) ⟶
      neg (inst2 p (var 0) (Syn.shift x) ≐ zero)))
    (hD : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift S) ⟶ (inst2 A (var 0) (Syn.shift x) ≐ zero) ⟶
      DescAt ρ d T (Syn.shift S) (Syn.shift x) (var 0)))
    (hL : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift S) ⟶ (inst2 A (var 0) (Syn.shift x) ≐ zero) ⟶
      SuccHold p d T (Syn.shift x) (var 0) ⟶ neg (inst2 p (var 0) (Syn.shift x) ≐ zero))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift S) ⟶ neg (inst2 p (var 0) (Syn.shift x) ≐ zero)) :=
  rank_induction (loc_of_frontier hT hD hL)

end LeanProofs.IPRA.Foundations.FrontierSoundness

export_ipra Foundations.FrontierSoundness (inst2_rdB le_of_lt_succ' lt_succ_of_le' rdB)
