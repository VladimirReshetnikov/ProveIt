import BoundedPAConsistency.InternalRelativization
import BoundedPAConsistency.SizedDerivation

/-!
# The relativization engine with explicit derivation-size bounds

`InternalRelativization.derivable_relSet` turns every internal `T`-derivation
into a `U`-derivation of the relativized sequent, but states the result with
`Derivable`, so the output code is lost. This module proves the same
transport with an explicit elementary bound on the output code
(`derivableLe_relSet`), in every model of `𝗜𝚺₁`.

Everything is measured by one numeric parameter `a`, which must bound the
domain formula `d`, its negation, and the domain side formulas
`¬δ(&i)`/`δ(&i)` (below `2^(a·(i+1))`); the bounded axiom obligations are
also stated with `a`.

* `relativize_le`: `relativize L d p ≤ relB a p = 2^(2^((a+12)·(p+1)))`, by
  formula induction (each quantifier step adds a fixed number of Cantor
  pairings).
* `derivableLe_relSet`: a `T`-derivation with code `n` yields a relativized
  `U`-derivation with code at most `T a n = 2^(2^(2^(A·(n+1))))`, by the same
  derivation induction as the unbounded engine. Every member of every sequent
  built at node `n` sits below one bound `B a n`, and each input node costs at
  most four bounded rule applications, a factor `2^40` in the exponent, which
  the tower absorbs (`stage_le_T`).
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.BoundedPAConsistency.InternalRelativizationBound

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.InternalRelativization
open LeanProofs.BoundedPAConsistency.SizedDerivation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Exponential bookkeeping -/

section Arith

theorem exp_three : Exp.exp (3 : V) = 8 := by
  rw [show (3 : V) = 2 + 1 by norm_num, exp_succ, exp_two]
  norm_num

theorem exp_five : Exp.exp (5 : V) = 32 := by
  rw [show (5 : V) = 3 + 2 by norm_num, exp_add, exp_three, exp_two]
  norm_num

theorem exp_ten : Exp.exp (10 : V) = 1024 := by
  rw [show (10 : V) = 2 * 5 by norm_num, exp_even, exp_five]
  norm_num

theorem mul1024_exp (w : V) : 1024 * Exp.exp w = Exp.exp (w + 10) := by
  rw [exp_add, exp_ten]
  ring

theorem mul4096_exp (w : V) : 4 * (1024 * Exp.exp w) = Exp.exp (w + 12) := by
  rw [show w + 12 = w + 10 + 2 by ring, exp_add (w + 10), exp_two, ← mul1024_exp]
  ring

theorem le_mul_of_one_le {x k : V} (hk : 1 ≤ k) : x ≤ k * x :=
  le_mul_of_one_le_left (Arithmetic.zero_le x) hk

theorem exp_exp_mono {x y : V} (h : x ≤ y) : Exp.exp (Exp.exp x) ≤ Exp.exp (Exp.exp y) :=
  exp_monotone_le.mpr (exp_monotone_le.mpr h)

theorem one_le_of_lt {x y : V} (h : x < y) : 1 ≤ y := by
  simpa using lt_iff_succ_le.mp (lt_of_le_of_lt (Arithmetic.zero_le x) h)

theorem self_le_exp_exp (x : V) : x ≤ Exp.exp (Exp.exp x) :=
  le_trans (le_exp_self x) (le_exp_self _)

/-- `x + 1 ≤ 2^x`'s doubling form: `2^y + 1 ≤ 2^(y+1)`. -/
theorem exp_succ_ge (y : V) : Exp.exp y + 1 ≤ Exp.exp (y + 1) := by
  rw [exp_succ]
  calc Exp.exp y + 1 ≤ Exp.exp y + Exp.exp y := _root_.add_le_add le_rfl (one_le_exp y)
    _ = 2 * Exp.exp y := by ring

end Arith

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ## Size of relativized formulas -/

section Formula

/-- The size bound for relativized formulas. -/
def relB (a x : V) : V := Exp.exp (Exp.exp ((a + 12) * (x + 1)))

theorem self_le_relB (a x : V) : x ≤ relB a x := by
  unfold relB
  refine le_trans ?_ (self_le_exp_exp _)
  calc x ≤ x + 1 := le_self_add
    _ ≤ (a + 12) * (x + 1) := le_mul_of_one_le (le_trans (by norm_num) le_add_self)

theorem relB_mono (a : V) {x y : V} (h : x ≤ y) : relB a x ≤ relB a y := by
  unfold relB
  exact exp_exp_mono (mul_le_mul_of_nonneg_left (_root_.add_le_add h le_rfl) (Arithmetic.zero_le _))

/-- A subformula `x` of a node `n` is bounded at the level `(a+12)·n`. -/
theorem relB_le_of_lt (a : V) {x n : V} (h : x < n) :
    relB a x ≤ Exp.exp (Exp.exp ((a + 12) * n)) := by
  unfold relB
  exact exp_exp_mono (mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp h) (Arithmetic.zero_le _))

theorem four_le_level (a : V) {n : V} (hn : 1 ≤ n) : 4 ≤ Exp.exp ((a + 12) * n) := by
  refine le_trans ?_ (le_exp_self _)
  calc (4 : V) ≤ 12 := by norm_num
    _ ≤ a + 12 := le_add_self
    _ ≤ (a + 12) * n := le_mul_of_one_le_right (Arithmetic.zero_le _) hn

/-- One node step: a fixed four-pairing cost at level `(a+12)·n` fits under `relB a n`. -/
theorem node_le_relB (a : V) {n : V} :
    Exp.exp (4 * (1024 * Exp.exp ((a + 12) * n))) ≤ relB a n := by
  unfold relB
  rw [mul4096_exp]
  refine exp_monotone_le.mpr (exp_monotone_le.mpr ?_)
  calc (a + 12) * n + 12 ≤ (a + 12) * n + (a + 12) := _root_.add_le_add le_rfl le_add_self
    _ = (a + 12) * (n + 1) := by ring

theorem node3_le_relB (a : V) {n : V} :
    Exp.exp (1024 * Exp.exp ((a + 12) * n)) ≤ relB a n :=
  le_trans (exp_monotone_le.mpr le_four_mul) (node_le_relB a)

variable {d : V}

/-- **Relativized formulas stay below `relB a p`.** -/
theorem relativize_le {a : V} (hda : d ≤ a) (hna : neg L d ≤ a) (p : V) :
    relativize L d p ≤ relB a p := by
  by_cases hp : IsUFormula L p
  swap
  · rw [relativize_not_uformula hp]
    exact Arithmetic.zero_le _
  refine IsUFormula.ISigma1.sigma1_succ_induction
    (P := fun p => relativize L d p ≤ Exp.exp (Exp.exp ((a + 12) * (p + 1)))) (by definability)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro k R v hR hv
    rw [relativize_rel hR hv]
    exact self_le_relB a _
  · intro k R v hR hv
    rw [relativize_nrel hR hv]
    exact self_le_relB a _
  · rw [relativize_verum]
    exact self_le_relB a _
  · rw [relativize_falsum]
    exact self_le_relB a _
  · intro p q hp hq ihp ihq
    rw [relativize_and hp hq]
    have hn : 1 ≤ p ^⋏ q := one_le_of_lt (lt_K!_left p q)
    have he := four_le_level a hn
    refine le_trans ?_ (node3_le_relB a)
    exact tuple3_le he (tag_le (by norm_num) he)
      (le_trans ihp (relB_le_of_lt a (lt_K!_left p q)))
      (le_trans ihq (relB_le_of_lt a (lt_K!_right p q)))
  · intro p q hp hq ihp ihq
    rw [relativize_or hp hq]
    have hn : 1 ≤ p ^⋎ q := one_le_of_lt (lt_or_left p q)
    have he := four_le_level a hn
    refine le_trans ?_ (node3_le_relB a)
    exact tuple3_le he (tag_le (by norm_num) he)
      (le_trans ihp (relB_le_of_lt a (lt_or_left p q)))
      (le_trans ihq (relB_le_of_lt a (lt_or_right p q)))
  · intro p hp ih
    rw [relativize_all hp]
    have hn : 1 ≤ ^∀ p := one_le_of_lt (lt_forall p)
    have he := four_le_level a hn
    have hlev : a ≤ Exp.exp ((a + 12) * ^∀ p) :=
      le_trans (le_trans le_self_add (le_mul_of_one_le_right (Arithmetic.zero_le _) hn))
        (le_exp_self _)
    have hin : ⟪5, neg L d, relativize L d p⟫ + 1 ≤ Exp.exp (1024 * Exp.exp ((a + 12) * ^∀ p)) :=
      tuple3_le he (tag_le (by norm_num) he) (le_exp_of_le_self (le_trans hna hlev))
        (le_trans ih (relB_le_of_lt a (lt_forall p)))
    refine le_trans ?_ (node_le_relB a)
    exact pair_succ_le_exp (le_trans (by norm_num) (DerivableLe.four_le_1024 he))
      (tag_le (by norm_num) (DerivableLe.four_le_1024 he)) hin
  · intro p hp ih
    rw [relativize_exs hp]
    have hn : 1 ≤ ^∃ p := one_le_of_lt (lt_exists p)
    have he := four_le_level a hn
    have hlev : a ≤ Exp.exp ((a + 12) * ^∃ p) :=
      le_trans (le_trans le_self_add (le_mul_of_one_le_right (Arithmetic.zero_le _) hn))
        (le_exp_self _)
    have hin : ⟪4, d, relativize L d p⟫ + 1 ≤ Exp.exp (1024 * Exp.exp ((a + 12) * ^∃ p)) :=
      tuple3_le he (tag_le (by norm_num) he) (le_exp_of_le_self (le_trans hda hlev))
        (le_trans ih (relB_le_of_lt a (lt_exists p)))
    refine le_trans ?_ (node_le_relB a)
    exact pair_succ_le_exp (le_trans (by norm_num) (DerivableLe.four_le_1024 he))
      (tag_le (by norm_num) (DerivableLe.four_le_1024 he)) hin

end Formula

/-! ## Node budgets -/

section Budget

/-- The member-level constant. -/
def kc (a : V) : V := a * a + 2 * a + 12

/-- The tower constant. -/
def ac (a : V) : V := 2 * kc a + 40

/-- Atomic sequent members at node `n` (relativized formulas, side formulas). -/
def bat (a n : V) : V := Exp.exp (Exp.exp (kc a * (n + 1)))

/-- Every sequent member at node `n` is below `memB a n`. -/
def memB (a n : V) : V := Exp.exp (Exp.exp (kc a * (n + 1) + 10)) + 1

/-- The exponent budget at node `n`: children and sequents are below `2^(nodeE a n)`. -/
def nodeE (a n : V) : V := Exp.exp (Exp.exp (ac a * n))

/-- **The output bound** for a relativized derivation of an input of code `n`. -/
def towerB (a n : V) : V := Exp.exp (Exp.exp (Exp.exp (ac a * (n + 1))))

variable {a : V}

theorem a12_le_kc (a : V) : a + 12 ≤ kc a := by
  unfold kc
  calc a + 12 ≤ 2 * a + 12 := _root_.add_le_add (le_mul_of_one_le (by norm_num)) le_rfl
    _ ≤ a * a + 2 * a + 12 := by rw [add_assoc]; exact le_add_self

theorem forty_le_ac (a : V) : 40 ≤ ac a := by unfold ac; exact le_add_self

theorem a_le_ac (a : V) : a ≤ ac a := by
  unfold ac
  calc a ≤ a + 12 := le_self_add
    _ ≤ kc a := a12_le_kc a
    _ ≤ 2 * kc a := le_mul_of_one_le (by norm_num)
    _ ≤ 2 * kc a + 40 := le_self_add

theorem dom_index_le (a : V) {i n : V} (hi : i ≤ n + a) : a * (i + 1) ≤ kc a * (n + 1) := by
  have h1 : a * (i + 1) ≤ a * (n + a + 1) :=
    mul_le_mul_of_nonneg_left (_root_.add_le_add hi le_rfl) (Arithmetic.zero_le a)
  have h2 : kc a * (n + 1) = a * (n + a + 1) + (a * a * n + a * n + a + 12 * n + 12) := by
    unfold kc
    ring
  rw [h2]
  exact le_trans h1 le_self_add

variable {d : V}

theorem rel_le_bat (hda : d ≤ a) (hna : neg L d ≤ a) {x n : V} (hx : x ≤ n) :
    relativize L d x ≤ bat a n := by
  refine le_trans (relativize_le hda hna x) (le_trans (relB_mono a hx) ?_)
  unfold relB bat
  exact exp_exp_mono (mul_le_mul_of_nonneg_right (a12_le_kc a) (Arithmetic.zero_le _))

theorem dom_le_bat {X i n : V} (hi : i ≤ n + a) (h : X ≤ Exp.exp (a * (i + 1))) : X ≤ bat a n := by
  unfold bat
  exact le_trans h (le_trans (exp_monotone_le.mpr (dom_index_le a hi))
    (exp_monotone_le.mpr (le_exp_self _)))

theorem bat_lt_memB (a n : V) : bat a n < memB a n := by
  unfold bat memB
  exact lt_of_le_of_lt (exp_exp_mono le_self_add) (lt_add_one _)

theorem four_le_kcexp (a n : V) : 4 ≤ Exp.exp (kc a * (n + 1)) := by
  refine le_trans ?_ (le_exp_self _)
  calc (4 : V) ≤ 12 := by norm_num
    _ ≤ a + 12 := le_add_self
    _ ≤ kc a := a12_le_kc a
    _ ≤ kc a * (n + 1) := le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self

/-- A binary connective of two atomic members is still a member. -/
theorem tuple_lt_memB {k x y n : V} (hk : k ≤ 9) (hx : x ≤ bat a n) (hy : y ≤ bat a n) :
    ⟪k, x, y⟫ + 1 < memB a n := by
  have he := four_le_kcexp a n
  have h := tuple3_le he (tag_le hk he) hx hy
  rw [mul1024_exp] at h
  unfold memB
  exact lt_of_le_of_lt h (lt_add_one _)

theorem or_lt_memB {x y n : V} (hx : x ≤ bat a n) (hy : y ≤ bat a n) : x ^⋎ y < memB a n :=
  tuple_lt_memB (by norm_num) hx hy

theorem and_lt_memB {x y n : V} (hx : x ≤ bat a n) (hy : y ≤ bat a n) : x ^⋏ y < memB a n :=
  tuple_lt_memB (by norm_num) hx hy

theorem memB_le_nodeE (a : V) {n : V} (hn : 1 ≤ n) : memB a n ≤ nodeE a n := by
  unfold memB nodeE
  refine le_trans (exp_succ_ge _) (exp_monotone_le.mpr ?_)
  refine le_trans (exp_succ_ge _) (exp_monotone_le.mpr ?_)
  have hk : kc a ≤ kc a * n := le_mul_of_one_le_right (Arithmetic.zero_le _) hn
  have h40 : (11 : V) ≤ 40 * n :=
    le_trans (by norm_num : (11 : V) ≤ 40) (le_mul_of_one_le_right (Arithmetic.zero_le _) hn)
  calc kc a * (n + 1) + 10 + 1 = kc a * n + kc a + 11 := by ring
    _ ≤ kc a * n + kc a * n + 40 * n := _root_.add_le_add (_root_.add_le_add le_rfl hk) h40
    _ = ac a * n := by unfold ac; ring

theorem ac_mul_ge (a : V) {n : V} (hn : 1 ≤ n) : 40 ≤ ac a * n :=
  le_trans (forty_le_ac a) (le_mul_of_one_le_right (Arithmetic.zero_le _) hn)

theorem four_le_nodeE (a : V) {n : V} (hn : 1 ≤ n) : 4 ≤ nodeE a n := by
  unfold nodeE
  refine le_trans ?_ (self_le_exp_exp _)
  exact le_trans (by norm_num) (ac_mul_ge a hn)

theorem child_le (a : V) {c n : V} (h : c < n) : towerB a c ≤ Exp.exp (nodeE a n) := by
  unfold towerB nodeE
  exact exp_monotone_le.mpr (exp_exp_mono
    (mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp h) (Arithmetic.zero_le _)))

theorem le_nodeE (a : V) {x n : V} (hx : x ≤ n) : x ≤ Exp.exp (nodeE a n) := by
  unfold nodeE
  refine le_trans hx (le_trans ?_ (le_trans (self_le_exp_exp _) (le_exp_self _)))
  exact le_mul_of_one_le (le_trans (by norm_num) (forty_le_ac a))

theorem ax_le (a : V) {p n : V} (h : p < n) :
    Exp.exp (Exp.exp (Exp.exp (a * (p + 1)))) ≤ Exp.exp (nodeE a n) := by
  unfold nodeE
  refine exp_monotone_le.mpr (exp_exp_mono ?_)
  exact le_trans (mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp h) (Arithmetic.zero_le a))
    (mul_le_mul_of_nonneg_right (a_le_ac a) (Arithmetic.zero_le _))

/-- **Four bounded rule applications per node fit under the tower.** -/
theorem stage4_le (a : V) {n : V} (hn : 1 ≤ n) :
    Exp.exp (1024 * (1024 * (1024 * (1024 * nodeE a n)))) ≤ towerB a n := by
  unfold towerB nodeE
  rw [mul1024_exp, mul1024_exp, mul1024_exp, mul1024_exp]
  refine exp_monotone_le.mpr (exp_monotone_le.mpr ?_)
  have hwe : (40 : V) ≤ Exp.exp (ac a * n) := le_trans (ac_mul_ge a hn) (le_exp_self _)
  have h2 : (2 : V) ≤ Exp.exp (ac a) :=
    le_trans (by norm_num : (2 : V) ≤ 40) (le_trans (forty_le_ac a) (le_exp_self _))
  rw [show ac a * (n + 1) = ac a * n + ac a by ring, exp_add]
  calc Exp.exp (ac a * n) + 10 + 10 + 10 + 10 = Exp.exp (ac a * n) + 40 := by ring
    _ ≤ Exp.exp (ac a * n) + Exp.exp (ac a * n) := _root_.add_le_add le_rfl hwe
    _ = Exp.exp (ac a * n) * 2 := by ring
    _ ≤ Exp.exp (ac a * n) * Exp.exp (ac a) :=
        mul_le_mul_of_nonneg_left h2 (Arithmetic.zero_le _)

theorem st1 (e : V) : 1024 * e ≤ 1024 * (1024 * (1024 * (1024 * e))) :=
  le_trans DerivableLe.le_1024 (le_trans DerivableLe.le_1024 DerivableLe.le_1024)

theorem st2 (e : V) : 1024 * (1024 * e) ≤ 1024 * (1024 * (1024 * (1024 * e))) :=
  le_trans DerivableLe.le_1024 DerivableLe.le_1024

theorem st3 (e : V) : e ≤ 1024 * (1024 * (1024 * e)) :=
  le_trans DerivableLe.le_1024 (le_trans DerivableLe.le_1024 DerivableLe.le_1024)

theorem fstIdx_le (x : V) : fstIdx x ≤ x := by
  unfold fstIdx
  exact le_trans (pi₁_le_self _) (sub_le_self _ _)

theorem mem_child_le {c n x : V} (hc : c < n) (hx : x ∈ fstIdx c) : x ≤ n :=
  le_of_lt (lt_trans (lt_of_lt_of_le (lt_of_mem hx) (fstIdx_le c)) hc)

theorem seq_mem_le {s n : V} (hs : s < n) : ∀ x ∈ s, x ≤ n :=
  fun x hx => le_of_lt (lt_trans (lt_of_mem hx) hs)

theorem cup_lt {s t B : V} (h₁ : ∀ y ∈ s, y < B) (h₂ : ∀ y ∈ t, y < B) : ∀ y ∈ s ∪ t, y < B := by
  intro y hy
  rcases mem_cup_iff.mp hy with hy | hy
  · exact h₁ y hy
  · exact h₂ y hy

theorem subset_lt {s t B : V} (h : s ⊆ t) (ht : ∀ y ∈ t, y < B) : ∀ y ∈ s, y < B :=
  fun y hy => ht y (h hy)

theorem relSet_lt (hda : d ≤ a) (hna : neg L d ≤ a) {s n : V} (hs : ∀ x ∈ s, x ≤ n) :
    ∀ y ∈ relSet L d s, y < memB a n := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_relSet_iff.mp hy
  exact lt_of_le_of_lt (rel_le_bat hda hna (hs x hx)) (bat_lt_memB a n)

theorem domSet_lt (hdom : ∀ i, domF L d i ≤ Exp.exp (a * (i + 1))) {m n : V} (hm : m ≤ n + a + 1) :
    ∀ y ∈ domSet L d m, y < memB a n := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := mem_domSet_iff.mp hy
  have : i ≤ n + a := lt_succ_iff_le.mp (lt_of_lt_of_le hi hm)
  exact lt_of_le_of_lt (dom_le_bat this (hdom i)) (bat_lt_memB a n)

end Budget

/-! ## The bounded transport -/

section Transport

variable {T U : Theory L} [T.Δ₁] [U.Δ₁] {d a : V}

/-- `derivable_insert_of_relSet` with sizes. -/
theorem derivableLe_insert_of_relSet {x s m m' e : V} (he : 4 ≤ e) (hm : m ≤ m')
    (hsb : insert (relativize L d x) (relSet L d s ∪ domSet L d m') ≤ Exp.exp e)
    (hT : IsFormulaSet L (insert (relativize L d x) (relSet L d s ∪ domSet L d m')))
    (h : DerivableLe U (relSet L d (insert x s) ∪ domSet L d m) (Exp.exp e)) :
    DerivableLe U (insert (relativize L d x) (relSet L d s ∪ domSet L d m'))
      (Exp.exp (1024 * e)) := by
  refine DerivableLe.wk he hsb hT ?_ h
  intro y hy
  rcases mem_cup_iff.mp hy with hy | hy
  · rw [relSet_insert] at hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · simp
    · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inl hy)))
  · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inr (domSet_subset hm hy))))

/-- The bounded transport invariant. -/
def RelInv (U : Theory L) [U.Δ₁] (d a der : V) : Prop :=
  ∃ m, m ≤ der + a ∧ DerivableLe U (relSet L d (fstIdx der) ∪ domSet L d m) (towerB a der)

/-- **Relativization of internal derivations, with an explicit size bound.**
A `T`-derivation with code `der` yields a `U`-derivation of the relativized
sequent with at most `der + a` domain side formulas and code at most
`towerB a der = 2^(2^(2^(ac a·(der+1))))`. -/
theorem derivableLe_relSet (hd : IsSemiformula L 1 d) (hds : shift L d = d)
    (hTerm : ∀ t : V, IsTerm L t → ∃ j, t = ^&j)
    (hda : d ≤ a) (hna : neg L d ≤ a)
    (hdom : ∀ i, domF L d i ≤ Exp.exp (a * (i + 1)))
    (hsubd : ∀ i, substs1 L ^&i d ≤ Exp.exp (a * (i + 1)))
    (hAx : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class →
      ∃ m, m ≤ p + a ∧ DerivableLe U (insert (relativize L d p) (domSet L d m))
        (Exp.exp (Exp.exp (Exp.exp (a * (p + 1))))))
    {der : V} (h : Derivation T der) : RelInv U d a der := by
  have hdU := hd.isUFormula
  have hFS : ∀ s m, IsFormulaSet L s → IsFormulaSet L (relSet L d s ∪ domSet L d m) :=
    fun s m hs => by simp [isFormulaSet_relSet hd hs, isFormulaSet_domSet hd m]
  obtain ⟨A0, hA0⟩ : ∃ A0, A0 = ac a := ⟨_, rfl⟩
  have key : ∃ m, m ≤ der + a ∧ ∃ z, z ≤ Exp.exp (Exp.exp (Exp.exp (A0 * (der + 1)))) ∧
      (fstIdx z = relSet L d (fstIdx der) ∪ domSet L d m ∧ Derivation U z) := by
    apply Derivation.induction1 𝚺
      (P := fun der : V => ∃ m, m ≤ der + a ∧ ∃ z, z ≤ Exp.exp (Exp.exp (Exp.exp (A0 * (der + 1)))) ∧
        (fstIdx z = relSet L d (fstIdx der) ∪ domSet L d m ∧ Derivation U z))
      (by definability) h
    all_goals subst hA0
    -- axL
    · intro s hs p hp hn
      have hn1 : 1 ≤ axL s p := one_le_of_lt (seq_lt_axL s p)
      have he := four_le_nodeE a hn1
      have hS : ∀ y ∈ relSet L d s ∪ domSet L d 0, y < memB a (axL s p) :=
        cup_lt (relSet_lt hda hna (seq_mem_le (seq_lt_axL s p))) (domSet_lt hdom (by simp))
      refine ⟨0, Arithmetic.zero_le _, ?_⟩
      simp only [fstIdx_axL]
      have hD := DerivableLe.em (T := U) he (DerivableLe.seq_le (memB_le_nodeE a hn1) hS)
        (hFS s 0 hs) (relativize L d p) (mem_cup_iff.mpr (Or.inl (relativize_mem_relSet hp))) (by
          rw [relativize_neg hdU (hs p hp).isUFormula]
          exact mem_cup_iff.mpr (Or.inl (relativize_mem_relSet hn)))
      exact hD.mono (le_trans (exp_monotone_le.mpr (st1 _)) (stage4_le a hn1))
    -- verum
    · intro s hs hv
      have hn1 : 1 ≤ verumIntro s := one_le_of_lt (seq_lt_verumIntro s)
      have he := four_le_nodeE a hn1
      have hS : ∀ y ∈ relSet L d s ∪ domSet L d 0, y < memB a (verumIntro s) :=
        cup_lt (relSet_lt hda hna (seq_mem_le (seq_lt_verumIntro s))) (domSet_lt hdom (by simp))
      refine ⟨0, Arithmetic.zero_le _, ?_⟩
      simp only [fstIdx_verumIntro]
      have hD := DerivableLe.verum (T := U) he (DerivableLe.seq_le (memB_le_nodeE a hn1) hS)
        (hFS s 0 hs) (mem_cup_iff.mpr (Or.inl (by simpa using relativize_mem_relSet (d := d) hv)))
      exact hD.mono (le_trans (exp_monotone_le.mpr (st1 _)) (stage4_le a hn1))
    -- and
    · intro s hs p q dp dq hpq hdp hdq ⟨m₁, hm₁, ih₁⟩ ⟨m₂, hm₂, ih₂⟩
      have hn1 : 1 ≤ andIntro s p q dp dq := one_le_of_lt (seq_lt_andIntro s p q dp dq)
      have he := four_le_nodeE a hn1
      have hBe := memB_le_nodeE a hn1
      have ih₁' : DerivableLe U (relSet L d (insert p s) ∪ domSet L d m₁)
          (Exp.exp (nodeE a (andIntro s p q dp dq))) := by
        have := DerivableLe.mono (T := U) ih₁ (child_le a (dp_lt_andIntro s p q dp dq))
        rwa [hdp.1] at this
      have ih₂' : DerivableLe U (relSet L d (insert q s) ∪ domSet L d m₂)
          (Exp.exp (nodeE a (andIntro s p q dp dq))) := by
        have := DerivableLe.mono (T := U) ih₂ (child_le a (dq_lt_andIntro s p q dp dq))
        rwa [hdq.1] at this
      have hpqF := hs _ hpq
      have hp : IsFormula L p := (IsSemiformula.and.mp hpqF).1
      have hq : IsFormula L q := (IsSemiformula.and.mp hpqF).2
      have hmax : max m₁ m₂ ≤ andIntro s p q dp dq + a := max_le
        (le_trans hm₁ (_root_.add_le_add (le_of_lt (dp_lt_andIntro s p q dp dq)) le_rfl))
        (le_trans hm₂ (_root_.add_le_add (le_of_lt (dq_lt_andIntro s p q dp dq)) le_rfl))
      have hS : ∀ y ∈ relSet L d s ∪ domSet L d (max m₁ m₂), y < memB a (andIntro s p q dp dq) :=
        cup_lt (relSet_lt hda hna (seq_mem_le (seq_lt_andIntro s p q dp dq)))
          (domSet_lt hdom (le_trans hmax le_self_add))
      have hpn : p ≤ andIntro s p q dp dq := le_of_lt (lt_trans (lt_K!_left p q)
        (lt_trans (lt_of_mem hpq) (seq_lt_andIntro s p q dp dq)))
      have hqn : q ≤ andIntro s p q dp dq := le_of_lt (lt_trans (lt_K!_right p q)
        (lt_trans (lt_of_mem hpq) (seq_lt_andIntro s p q dp dq)))
      refine ⟨max m₁ m₂, hmax, ?_⟩
      simp only [fstIdx_andIntro]
      have hmem : relativize L d p ^⋏ relativize L d q ∈ relSet L d s ∪ domSet L d (max m₁ m₂) := by
        rw [← relativize_and hp.isUFormula hq.isUFormula]
        exact mem_cup_iff.mpr (Or.inl (relativize_mem_relSet hpq))
      have w₁ := derivableLe_insert_of_relSet he (le_max_left m₁ m₂)
        (DerivableLe.seq_le hBe (DerivableLe.insert_lt
          (lt_of_le_of_lt (rel_le_bat hda hna hpn) (bat_lt_memB a _)) hS))
        (by simp [hFS s _ hs, isSemiformula_relativize hd hp]) ih₁'
      have w₂ := derivableLe_insert_of_relSet he (le_max_right m₁ m₂)
        (DerivableLe.seq_le hBe (DerivableLe.insert_lt
          (lt_of_le_of_lt (rel_le_bat hda hna hqn) (bat_lt_memB a _)) hS))
        (by simp [hFS s _ hs, isSemiformula_relativize hd hq]) ih₂'
      have hD := DerivableLe.and_m (DerivableLe.four_le_1024 he)
        (le_exp_of_le (DerivableLe.seq_le hBe hS) DerivableLe.le_1024) hmem w₁ w₂
      exact hD.mono (le_trans (exp_monotone_le.mpr (st2 _)) (stage4_le a hn1))
    -- or
    · intro s hs p q dp hpq hdp ⟨m, hm, ih⟩
      have hn1 : 1 ≤ orIntro s p q dp := one_le_of_lt (seq_lt_orIntro s p q dp)
      have he := four_le_nodeE a hn1
      have hBe := memB_le_nodeE a hn1
      have ih' : DerivableLe U (relSet L d (insert p (insert q s)) ∪ domSet L d m)
          (Exp.exp (nodeE a (orIntro s p q dp))) := by
        have := DerivableLe.mono (T := U) ih (child_le a (d_lt_orIntro s p q dp))
        rwa [hdp.1] at this
      have hpqF := hs _ hpq
      have hp : IsFormula L p := (IsSemiformula.or.mp hpqF).1
      have hq : IsFormula L q := (IsSemiformula.or.mp hpqF).2
      have hm' : m ≤ orIntro s p q dp + a :=
        le_trans hm (_root_.add_le_add (le_of_lt (d_lt_orIntro s p q dp)) le_rfl)
      have hS : ∀ y ∈ relSet L d s ∪ domSet L d m, y < memB a (orIntro s p q dp) :=
        cup_lt (relSet_lt hda hna (seq_mem_le (seq_lt_orIntro s p q dp)))
          (domSet_lt hdom (le_trans hm' le_self_add))
      have hpn : p ≤ orIntro s p q dp := le_of_lt (lt_trans (lt_or_left p q)
        (lt_trans (lt_of_mem hpq) (seq_lt_orIntro s p q dp)))
      have hqn : q ≤ orIntro s p q dp := le_of_lt (lt_trans (lt_or_right p q)
        (lt_trans (lt_of_mem hpq) (seq_lt_orIntro s p q dp)))
      refine ⟨m, hm', ?_⟩
      simp only [fstIdx_orIntro]
      have hmem : relativize L d p ^⋎ relativize L d q ∈ relSet L d s ∪ domSet L d m := by
        rw [← relativize_or hp.isUFormula hq.isUFormula]
        exact mem_cup_iff.mpr (Or.inl (relativize_mem_relSet hpq))
      have w := DerivableLe.wk he
        (DerivableLe.seq_le hBe (DerivableLe.insert_lt
          (lt_of_le_of_lt (rel_le_bat hda hna hpn) (bat_lt_memB a _))
          (DerivableLe.insert_lt (lt_of_le_of_lt (rel_le_bat hda hna hqn) (bat_lt_memB a _)) hS)))
        (by simp [hFS s _ hs, isSemiformula_relativize hd hp, isSemiformula_relativize hd hq])
        (by
          intro y hy
          rcases mem_cup_iff.mp hy with hy | hy
          · rw [relSet_insert, relSet_insert] at hy
            rcases mem_bitInsert_iff.mp hy with rfl | hy
            · simp
            rcases mem_bitInsert_iff.mp hy with rfl | hy
            · simp
            · simp [hy]
          · simp [hy]) ih'
      have hD := DerivableLe.or_m (DerivableLe.four_le_1024 he)
        (le_exp_of_le (DerivableLe.seq_le hBe hS) DerivableLe.le_1024) hmem w
      exact hD.mono (le_trans (exp_monotone_le.mpr (st2 _)) (stage4_le a hn1))
    -- all
    · intro s hs p dp hp hdp ⟨m, hm, ih⟩
      have hn1 : 1 ≤ allIntro s p dp := one_le_of_lt (seq_lt_allIntro s p dp)
      have he := four_le_nodeE a hn1
      have hBe := memB_le_nodeE a hn1
      have hdpn : dp < allIntro s p dp := s_lt_allIntro s p dp
      have ih' : DerivableLe U (relSet L d (insert (free L p) (setShift L s)) ∪ domSet L d m)
          (Exp.exp (nodeE a (allIntro s p dp))) := by
        have := DerivableLe.mono (T := U) ih (child_le a hdpn)
        rwa [hdp.1] at this
      have hpF : IsSemiformula L 1 p := by simpa using hs _ hp
      have hm' : m ≤ allIntro s p dp + a := le_trans hm (_root_.add_le_add (le_of_lt hdpn) le_rfl)
      have hS : ∀ y ∈ relSet L d s ∪ domSet L d m, y < memB a (allIntro s p dp) :=
        cup_lt (relSet_lt hda hna (seq_mem_le (seq_lt_allIntro s p dp)))
          (domSet_lt hdom (le_trans hm' le_self_add))
      have hchild : ∀ x ∈ insert (free L p) (setShift L s), x ≤ allIntro s p dp := by
        intro x hx
        rw [← hdp.1] at hx
        exact mem_child_le hdpn hx
      refine ⟨m, hm', ?_⟩
      simp only [fstIdx_allIntro]
      have hmem : ^∀ (neg L d ^⋎ relativize L d p) ∈ relSet L d s ∪ domSet L d m := by
        rw [← relativize_all hpF.isUFormula]
        exact mem_cup_iff.mpr (Or.inl (relativize_mem_relSet hp))
      have hS' : ∀ y ∈ relSet L d (setShift L s) ∪ setShift L (domSet L d m),
          y < memB a (allIntro s p dp) :=
        cup_lt (relSet_lt hda hna (fun x hx => hchild x (mem_bitInsert_iff.mpr (Or.inr hx))))
          (subset_lt (setShift_domSet_subset hd hds m)
            (domSet_lt hdom (_root_.add_le_add hm' le_rfl)))
      have hfreeN : free L p ≤ allIntro s p dp := hchild _ (by simp)
      have hdom0 : domF L d 0 ≤ bat a (allIntro s p dp) := dom_le_bat (Arithmetic.zero_le _) (hdom 0)
      have hrf : relativize L d (free L p) ≤ bat a (allIntro s p dp) := rel_le_bat hda hna hfreeN
      have w := DerivableLe.wk he
        (DerivableLe.seq_le hBe (DerivableLe.insert_lt (lt_of_le_of_lt hdom0 (bat_lt_memB a _))
          (DerivableLe.insert_lt (lt_of_le_of_lt hrf (bat_lt_memB a _)) hS')))
        (by simp [isFormula_domF hd, isSemiformula_relativize hd hpF.free,
          isFormulaSet_relSet hd hs.setShift, (isFormulaSet_domSet hd m).setShift])
        (by
          intro y hy
          rcases mem_cup_iff.mp hy with hy | hy
          · rw [relSet_insert] at hy
            rcases mem_bitInsert_iff.mp hy with rfl | hy
            · simp
            · simp [hy]
          · rcases mem_bitInsert_iff.mp (domSet_subset_insert_setShift hd hds m hy) with rfl | hy
            · simp
            · simp [hy]) ih'
      have w2 := DerivableLe.or (DerivableLe.four_le_1024 he)
        (le_trans hBe DerivableLe.le_1024) hS' (or_lt_memB hdom0 hrf) w
      have hD := DerivableLe.all_m (DerivableLe.four_le_1024 (DerivableLe.four_le_1024
          (DerivableLe.four_le_1024 he)))
        (le_exp_of_le (DerivableLe.seq_le hBe hS) (st3 _)) hmem (by
          rw [free_or (isSemiformula_of_one (n := 0) hd |>.neg |> fun h => by simpa using h)
              (isSemiformula_relativize hd hpF),
            free_neg_domain hd hds, relativize_free hd hds hpF, mem_setShift_union,
            setShift_relSet hd hds hs]
          exact w2)
      exact hD.mono (stage4_le a hn1)
    -- exs
    · intro s hs p t dp hp ht hdp ⟨m, hm, ih⟩
      have hn1 : 1 ≤ exsIntro s p t dp := one_le_of_lt (seq_lt_exsIntro s p t dp)
      have he := four_le_nodeE a hn1
      have hBe := memB_le_nodeE a hn1
      have hdpn : dp < exsIntro s p t dp := d_lt_exsIntro s p t dp
      have htn : t < exsIntro s p t dp := t_lt_exsIntro s p t dp
      have ih' : DerivableLe U (relSet L d (insert (substs1 L t p) s) ∪ domSet L d m)
          (Exp.exp (nodeE a (exsIntro s p t dp))) := by
        have := DerivableLe.mono (T := U) ih (child_le a hdpn)
        rwa [hdp.1] at this
      have hchild : ∀ x ∈ insert (substs1 L t p) s, x ≤ exsIntro s p t dp := by
        intro x hx
        rw [← hdp.1] at hx
        exact mem_child_le hdpn hx
      have hpF : IsSemiformula L 1 p := by simpa using hs _ hp
      obtain ⟨j, rfl⟩ := hTerm _ ht
      have hjn : j + 1 ≤ exsIntro s p ^&j dp := lt_iff_succ_le.mp (lt_trans (var_lt_qqFvar j) htn)
      have hm' : max m (j + 1) ≤ exsIntro s p ^&j dp + a := max_le
        (le_trans hm (_root_.add_le_add (le_of_lt hdpn) le_rfl)) (le_trans hjn le_self_add)
      have hS : ∀ y ∈ relSet L d s ∪ domSet L d (max m (j + 1)), y < memB a (exsIntro s p ^&j dp) :=
        cup_lt (relSet_lt hda hna (seq_mem_le (seq_lt_exsIntro s p _ dp)))
          (domSet_lt hdom (le_trans hm' le_self_add))
      refine ⟨max m (j + 1), hm', ?_⟩
      simp only [fstIdx_exsIntro]
      have hmem : ^∃ (d ^⋏ relativize L d p) ∈ relSet L d s ∪ domSet L d (max m (j + 1)) := by
        rw [← relativize_exs hpF.isUFormula]
        exact mem_cup_iff.mpr (Or.inl (relativize_mem_relSet hp))
      have hsub : substs1 L ^&j (d ^⋏ relativize L d p) =
          substs1 L ^&j d ^⋏ relativize L d (substs1 L ^&j p) := by
        simp only [substs1]
        rw [substs_and hdU (isUFormula_relativize hdU hpF.isUFormula)]
        congr 1
        exact relativize_substs1 hd (show IsSemiterm L 0 (^&j : V) by simp) hpF
      have hFS' := hFS s (max m (j + 1)) hs
      have hjle : j ≤ exsIntro s p ^&j dp + a := le_trans (le_trans le_self_add hjn) le_self_add
      have hsd : substs1 L ^&j d ≤ bat a (exsIntro s p ^&j dp) := dom_le_bat hjle (hsubd j)
      have hrs : relativize L d (substs1 L ^&j p) ≤ bat a (exsIntro s p ^&j dp) :=
        rel_le_bat hda hna (hchild _ (by simp))
      have hpS := hpF.substs1 (show IsSemiterm L 0 (^&j : V) by simp)
      have w₁ := DerivableLe.em (T := U) he
        (DerivableLe.seq_le hBe (DerivableLe.insert_lt (lt_of_le_of_lt hsd (bat_lt_memB a _)) hS))
        (by simp [hFS', hd.substs1 (show IsSemiterm L 0 (^&j : V) by simp)])
        (substs1 L ^&j d) (by simp) (by
          refine mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inr ?_)))
          exact domF_mem_domSet (lt_of_lt_of_le (by simp) (le_max_right m (j + 1))))
      have w₂ := derivableLe_insert_of_relSet he (le_max_left m (j + 1))
        (DerivableLe.seq_le hBe (DerivableLe.insert_lt (lt_of_le_of_lt hrs (bat_lt_memB a _)) hS))
        (by simp [hFS', isSemiformula_relativize hd hpS]) ih'
      have w3 := DerivableLe.and (DerivableLe.four_le_1024 he) (le_trans hBe DerivableLe.le_1024)
        hS (and_lt_memB hsd hrs) w₁ w₂
      have htb : ^&j ≤ Exp.exp (1024 * (1024 * (1024 * nodeE a (exsIntro s p ^&j dp)))) :=
        le_exp_of_le (le_nodeE a (le_of_lt htn)) (st3 _)
      have hD := DerivableLe.ex_m (DerivableLe.four_le_1024 (DerivableLe.four_le_1024
          (DerivableLe.four_le_1024 he)))
        (le_exp_of_le (DerivableLe.seq_le hBe hS) (st3 _))
        htb hmem ht (by rw [hsub]; exact w3)
      exact hD.mono (stage4_le a hn1)
    -- wk
    · intro s hs d' hss hd' ⟨m, hm, ih⟩
      have hn1 : 1 ≤ wkRule s d' := one_le_of_lt (seq_lt_wkRule s d')
      have he := four_le_nodeE a hn1
      have hBe := memB_le_nodeE a hn1
      have hdn : d' < wkRule s d' := d_lt_wkRule s d'
      have hm' : m ≤ wkRule s d' + a := le_trans hm (_root_.add_le_add (le_of_lt hdn) le_rfl)
      have hS : ∀ y ∈ relSet L d s ∪ domSet L d m, y < memB a (wkRule s d') :=
        cup_lt (relSet_lt hda hna (seq_mem_le (seq_lt_wkRule s d')))
          (domSet_lt hdom (le_trans hm' le_self_add))
      refine ⟨m, hm', ?_⟩
      simp only [fstIdx_wkRule]
      have hD := DerivableLe.wk he (DerivableLe.seq_le hBe hS) (hFS s m hs) (by
          intro y hy
          rcases mem_cup_iff.mp hy with hy | hy
          · exact mem_cup_iff.mpr (Or.inl (relSet_subset hss hy))
          · exact mem_cup_iff.mpr (Or.inr hy))
        (DerivableLe.mono (T := U) ih (child_le a hdn))
      exact hD.mono (le_trans (exp_monotone_le.mpr (st1 _)) (stage4_le a hn1))
    -- shift
    · intro s hs d' hes hd' ⟨m, hm, ih⟩
      have hn1 : 1 ≤ shiftRule s d' := one_le_of_lt (seq_lt_shiftRule s d')
      have he := four_le_nodeE a hn1
      have hBe := memB_le_nodeE a hn1
      have hdn : d' < shiftRule s d' := d_lt_shiftRule s d'
      have hs' : IsFormulaSet L (fstIdx d') := hd'.isFormulaSet
      have hm1 : m + 1 ≤ shiftRule s d' + a := by
        calc m + 1 ≤ d' + a + 1 := _root_.add_le_add hm le_rfl
          _ = d' + 1 + a := by ring
          _ ≤ shiftRule s d' + a := _root_.add_le_add (lt_iff_succ_le.mp hdn) le_rfl
      have hS : ∀ y ∈ relSet L d s ∪ domSet L d (m + 1), y < memB a (shiftRule s d') :=
        cup_lt (relSet_lt hda hna (seq_mem_le (seq_lt_shiftRule s d')))
          (domSet_lt hdom (le_trans hm1 le_self_add))
      have heq : setShift L (relSet L d (fstIdx d') ∪ domSet L d m) =
          relSet L d s ∪ setShift L (domSet L d m) := by
        rw [mem_setShift_union, setShift_relSet hd hds hs', ← hes]
      have hS2 : ∀ y ∈ relSet L d s ∪ setShift L (domSet L d m), y < memB a (shiftRule s d') :=
        cup_lt (relSet_lt hda hna (seq_mem_le (seq_lt_shiftRule s d')))
          (subset_lt (setShift_domSet_subset hd hds m) (domSet_lt hdom (le_trans hm1 le_self_add)))
      refine ⟨m + 1, hm1, ?_⟩
      simp only [fstIdx_shiftRule]
      have hsh := DerivableLe.shift he (by rw [heq]; exact DerivableLe.seq_le hBe hS2)
        (DerivableLe.mono (T := U) ih (child_le a hdn))
      rw [heq] at hsh
      have hD := DerivableLe.wk (DerivableLe.four_le_1024 he)
        (le_exp_of_le (DerivableLe.seq_le hBe hS) DerivableLe.le_1024) (hFS s _ hs) (by
          intro y hy
          rcases mem_cup_iff.mp hy with hy | hy
          · exact mem_cup_iff.mpr (Or.inl hy)
          · exact mem_cup_iff.mpr (Or.inr (setShift_domSet_subset hd hds m hy))) hsh
      exact hD.mono (le_trans (exp_monotone_le.mpr (st2 _)) (stage4_le a hn1))
    -- cut
    · intro s hs p d₁ d₂ hd₁ hd₂ ⟨m₁, hm₁, ih₁⟩ ⟨m₂, hm₂, ih₂⟩
      have hn1 : 1 ≤ cutRule s p d₁ d₂ := one_le_of_lt (seq_lt_cutRule s p d₁ d₂)
      have he := four_le_nodeE a hn1
      have hBe := memB_le_nodeE a hn1
      have h₁n : d₁ < cutRule s p d₁ d₂ := d₁_lt_cutRule s p d₁ d₂
      have h₂n : d₂ < cutRule s p d₁ d₂ := d₂_lt_cutRule s p d₁ d₂
      have ih₁' : DerivableLe U (relSet L d (insert p s) ∪ domSet L d m₁)
          (Exp.exp (nodeE a (cutRule s p d₁ d₂))) := by
        have := DerivableLe.mono (T := U) ih₁ (child_le a h₁n)
        rwa [hd₁.1] at this
      have ih₂' : DerivableLe U (relSet L d (insert (neg L p) s) ∪ domSet L d m₂)
          (Exp.exp (nodeE a (cutRule s p d₁ d₂))) := by
        have := DerivableLe.mono (T := U) ih₂ (child_le a h₂n)
        rwa [hd₂.1] at this
      have hp : IsFormula L p := (IsFormulaSet.insert_iff.mp hd₁.isFormulaSet).1
      have hpn : p ≤ cutRule s p d₁ d₂ := mem_child_le h₁n (by rw [hd₁.1]; simp)
      have hnpn : neg L p ≤ cutRule s p d₁ d₂ := mem_child_le h₂n (by rw [hd₂.1]; simp)
      have hmax : max m₁ m₂ ≤ cutRule s p d₁ d₂ + a := max_le
        (le_trans hm₁ (_root_.add_le_add (le_of_lt h₁n) le_rfl))
        (le_trans hm₂ (_root_.add_le_add (le_of_lt h₂n) le_rfl))
      have hS : ∀ y ∈ relSet L d s ∪ domSet L d (max m₁ m₂), y < memB a (cutRule s p d₁ d₂) :=
        cup_lt (relSet_lt hda hna (seq_mem_le (seq_lt_cutRule s p d₁ d₂)))
          (domSet_lt hdom (le_trans hmax le_self_add))
      refine ⟨max m₁ m₂, hmax, ?_⟩
      simp only [fstIdx_cutRule]
      have hFS' := hFS s (max m₁ m₂) hs
      have hrp : relativize L d p ≤ bat a (cutRule s p d₁ d₂) := rel_le_bat hda hna hpn
      have hrnp : relativize L d (neg L p) ≤ bat a (cutRule s p d₁ d₂) := rel_le_bat hda hna hnpn
      have w₁ := derivableLe_insert_of_relSet he (le_max_left m₁ m₂)
        (DerivableLe.seq_le hBe (DerivableLe.insert_lt (lt_of_le_of_lt hrp (bat_lt_memB a _)) hS))
        (by simp [hFS', isSemiformula_relativize hd hp]) ih₁'
      have w₂ := derivableLe_insert_of_relSet he (le_max_right m₁ m₂)
        (DerivableLe.seq_le hBe (DerivableLe.insert_lt (lt_of_le_of_lt hrnp (bat_lt_memB a _)) hS))
        (by simp [hFS', isSemiformula_relativize hd hp.neg]) ih₂'
      have hrpE : relativize L d p ≤ Exp.exp (1024 * nodeE a (cutRule s p d₁ d₂)) :=
        le_exp_of_le_self (le_trans hrp (le_trans (le_of_lt (bat_lt_memB a _))
          (le_trans hBe DerivableLe.le_1024)))
      have hD := DerivableLe.cut (DerivableLe.four_le_1024 he)
        (le_exp_of_le (DerivableLe.seq_le hBe hS) DerivableLe.le_1024) (relativize L d p) hrpE
        w₁ (by
          rw [relativize_neg hdU hp.isUFormula]
          exact w₂)
      exact hD.mono (le_trans (exp_monotone_le.mpr (st2 _)) (stage4_le a hn1))
    -- axm
    · intro s hs p hp hT
      have hn1 : 1 ≤ axm s p := one_le_of_lt (seq_lt_axm s p)
      have he := four_le_nodeE a hn1
      have hBe := memB_le_nodeE a hn1
      have hpn : p < axm s p := p_lt_axm s p
      obtain ⟨m, hm, hD0⟩ := hAx p (hs p hp) hT
      have hm' : m ≤ axm s p + a := le_trans hm (_root_.add_le_add (le_of_lt hpn) le_rfl)
      have hS : ∀ y ∈ relSet L d s ∪ domSet L d m, y < memB a (axm s p) :=
        cup_lt (relSet_lt hda hna (seq_mem_le (seq_lt_axm s p)))
          (domSet_lt hdom (le_trans hm' le_self_add))
      refine ⟨m, hm', ?_⟩
      simp only [fstIdx_axm]
      have hD := DerivableLe.wk he (DerivableLe.seq_le hBe hS) (hFS s m hs) (by
          intro y hy
          rcases mem_bitInsert_iff.mp hy with rfl | hy
          · exact mem_cup_iff.mpr (Or.inl (relativize_mem_relSet hp))
          · exact mem_cup_iff.mpr (Or.inr hy)) (hD0.mono (ax_le a hpn))
      exact hD.mono (le_trans (exp_monotone_le.mpr (st1 _)) (stage4_le a hn1))
  subst hA0
  exact key

end Transport

/-! ## Discharging the side formulas, with sizes -/

section Discharge

variable {U : Theory L} [U.Δ₁] {d a : V}

theorem exp30_mul (W : V) : 1024 * (1024 * (1024 * W)) = Exp.exp 30 * W := by
  rw [show (30 : V) = 10 + 10 + 10 by norm_num, exp_add, exp_add, exp_ten]
  ring

/-- One side formula `¬δ(&0)` is discharged (generalize, then cut against
`∃x δ(x)`) at the cost of three bounded rule applications. -/
theorem derivableLe_of_domSet_succ (hd : IsSemiformula L 1 d) (hds : shift L d = d)
    {w Bm : V} (he : 4 ≤ w) (hBw : Bm ≤ w)
    (hne : DerivableLe U (insert (^∃ d) (∅ : V)) (Exp.exp w))
    {r m : V} (hr : IsFormula L r) (hrs : shift L r = r)
    (hrB : r < Bm) (hdomB : ∀ i ≤ m, domF L d i < Bm)
    (hallB : ^∀ (neg L d) < Bm) (hexB : ^∃ d < Bm)
    (h : DerivableLe U (insert r (domSet L d (m + 1))) (Exp.exp w)) :
    DerivableLe U (insert r (domSet L d m)) (Exp.exp (1024 * (1024 * (1024 * w)))) := by
  have hΓ : IsFormulaSet L (insert r (domSet L d m)) := by
    simp [hr, isFormulaSet_domSet hd m]
  have hdomS : ∀ y ∈ domSet L d m, y < Bm := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_domSet_iff.mp hy
    exact hdomB i (le_of_lt hi)
  have hdomS1 : ∀ y ∈ domSet L d (m + 1), y < Bm := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_domSet_iff.mp hy
    exact hdomB i (lt_succ_iff_le.mp hi)
  have hΓB : ∀ y ∈ insert r (domSet L d m), y < Bm := DerivableLe.insert_lt hrB hdomS
  have h' : DerivableLe U (insert (free L (neg L d)) (setShift L (insert r (domSet L d m))))
      (Exp.exp w) := by
    rw [free_neg_domain hd hds, mem_setShift_insert, hrs]
    refine DerivableLe.ofSetEq (fun x => ?_) h
    rw [domSet_succ hd hds m]
    simp only [mem_bitInsert_iff]
    tauto
  have hshAll : shift L (^∀ (neg L d)) = ^∀ (neg L d) := by
    rw [shift_all hd.isUFormula.neg, shift_neg hd, hds]
  have hT1B : ∀ y ∈ insert (free L (neg L d))
      (setShift L (insert (^∀ (neg L d)) (insert r (domSet L d m)))), y < Bm := by
    rw [free_neg_domain hd hds, mem_setShift_insert, mem_setShift_insert, hshAll, hrs]
    exact DerivableLe.insert_lt (hdomB 0 (Arithmetic.zero_le _))
      (DerivableLe.insert_lt hallB (DerivableLe.insert_lt hrB
        (subset_lt (setShift_domSet_subset hd hds m) hdomS1)))
  have hall1 := DerivableLe.wk he (DerivableLe.seq_le hBw hT1B)
    (by simp [hd.neg, by simpa using h'.isFormulaSet]) (by intro x; simp; tauto) h'
  have hall := DerivableLe.all_m (p := neg L d) (DerivableLe.four_le_1024 he)
    (le_exp_of_le (DerivableLe.seq_le hBw (DerivableLe.insert_lt hallB hΓB)) DerivableLe.le_1024)
    (by simp) hall1
  have hex := DerivableLe.wk he (DerivableLe.seq_le hBw (DerivableLe.insert_lt hexB hΓB))
    (by simp [hd, hΓ]) (by
      intro y hy
      rcases mem_bitInsert_iff.mp hy with rfl | hy
      · simp
      · simp at hy) hne
  have hex' := hex.mono (exp_monotone_le.mpr (DerivableLe.le_1024 (e := 1024 * w)))
  have hcut := DerivableLe.cut (DerivableLe.four_le_1024 (DerivableLe.four_le_1024 he))
    (le_exp_of_le (DerivableLe.seq_le hBw hΓB) (le_trans DerivableLe.le_1024 DerivableLe.le_1024))
    (^∀ (neg L d))
    (le_exp_of_le_self (le_trans (le_of_lt hallB)
      (le_trans hBw (le_trans DerivableLe.le_1024 DerivableLe.le_1024)))) hall (by
      rw [neg_all hd.isUFormula.neg, hd.isUFormula.neg_neg]
      exact hex')
  exact hcut

/-- **All side formulas are discharged, with an explicit bound**: `m` side
formulas cost a factor `2^(30·m)` in the exponent. -/
theorem derivableLe_of_domSet (hd : IsSemiformula L 1 d) (hds : shift L d = d)
    {w₀ Bm : V} (he : 4 ≤ w₀) (hBw : Bm ≤ w₀)
    (hne : DerivableLe U (insert (^∃ d) (∅ : V)) (Exp.exp w₀))
    {r : V} (hr : IsFormula L r) (hrs : shift L r = r) (hrB : r < Bm)
    (hallB : ^∀ (neg L d) < Bm) (hexB : ^∃ d < Bm)
    (m : V) (hdomB : ∀ i ≤ m, domF L d i < Bm)
    (h : DerivableLe U (insert r (domSet L d m)) (Exp.exp w₀)) :
    DerivableLe U (insert r (∅ : V)) (Exp.exp (Exp.exp (30 * m) * w₀)) := by
  have key : ∀ k ≤ m, ∃ j, j + k = m ∧ ∃ z, z ≤ Exp.exp (Exp.exp (30 * k) * w₀) ∧
      (fstIdx z = insert r (domSet L d j) ∧ Derivation U z) := by
    intro k
    induction k using ISigma1.sigma1_succ_induction
    · definability
    · intro _
      refine ⟨m, by simp, ?_⟩
      have h0 : Exp.exp (Exp.exp (30 * (0 : V)) * w₀) = Exp.exp w₀ := by simp
      rw [h0]
      exact h
    · case succ k ih =>
      intro hk
      obtain ⟨j, hj, hder⟩ := ih (le_trans (by simp) hk)
      rcases zero_or_succ j with (rfl | ⟨j', rfl⟩)
      · exfalso
        simp [← hj] at hk
      · refine ⟨j', ?_, ?_⟩
        · rw [← hj, add_comm k 1, ← add_assoc]
        · have hW : w₀ ≤ Exp.exp (30 * k) * w₀ :=
            le_mul_of_one_le_left (Arithmetic.zero_le _) (one_le_exp _)
          have hj'm : j' ≤ m := by
            rw [← hj]
            exact le_trans le_self_add le_self_add
          have := derivableLe_of_domSet_succ hd hds (le_trans he hW) (le_trans hBw hW)
            (hne.mono (exp_monotone_le.mpr hW)) hr hrs hrB
            (fun i hi => hdomB i (le_trans hi hj'm)) hallB hexB hder
          rw [exp30_mul, ← mul_assoc, ← exp_add,
            show 30 + 30 * k = 30 * (k + 1) by ring] at this
          exact this
  obtain ⟨j, hj, hder⟩ := key m le_rfl
  have hj0 : j = 0 := by simpa using hj
  have hempty : domSet L d (0 : V) = ∅ := mem_ext fun y => by simp [mem_domSet_iff]
  rw [hj0, hempty] at hder
  exact hder

end Discharge

/-! ## The bounded interpretation theorem -/

section Interpretation

variable {T U : Theory L} [T.Δ₁] [U.Δ₁] {d a : V}

/-- `φ` has a `T`-proof with code at most `b`. -/
def ProvableLe (T : Theory L) [T.Δ₁] (φ b : V) : Prop := ∃ z ≤ b, Proof T z φ

theorem ProvableLe.toProvable {φ b : V} (h : ProvableLe T φ b) : Provable T φ :=
  let ⟨z, _, hz⟩ := h
  ⟨z, hz⟩

/-- **The bound for a relativized proof** of an input proof with code `n`. -/
def provB (a n : V) : V := Exp.exp (Exp.exp (30 * (n + a)) * nodeE a (n + 1))

theorem quant_lt_memB {k x n : V} (hk : k ≤ 9) (hx : x ≤ a) : ⟪k, x⟫ + 1 < memB a n := by
  have he := four_le_kcexp a n
  have hxe : x ≤ Exp.exp (Exp.exp (kc a * (n + 1))) :=
    le_trans hx (le_trans (le_trans le_self_add (le_trans (a12_le_kc a)
      (le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self))) (self_le_exp_exp _))
  have h := pair_succ_le_exp (le_trans (by norm_num) he) (tag_le hk he) hxe
  unfold memB
  refine lt_of_le_of_lt (le_trans h (exp_monotone_le.mpr ?_)) (lt_add_one _)
  rw [← mul1024_exp]
  exact mul_le_mul_of_nonneg_right (by norm_num) (Arithmetic.zero_le _)

/-- **Internal relative interpretation, with an explicit proof-size bound.**
A `T`-proof of a shift-fixed `φ` with code `n` yields a `U`-proof of `φ^δ`
with code at most `provB a n`, an explicit elementary function of `n`. -/
theorem provableLe_relativize (hd : IsSemiformula L 1 d) (hds : shift L d = d)
    (hTerm : ∀ t : V, IsTerm L t → ∃ j, t = ^&j)
    (hda : d ≤ a) (hna : neg L d ≤ a)
    (hdom : ∀ i, domF L d i ≤ Exp.exp (a * (i + 1)))
    (hsubd : ∀ i, substs1 L ^&i d ≤ Exp.exp (a * (i + 1)))
    (hAx : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class →
      ∃ m, m ≤ p + a ∧ DerivableLe U (insert (relativize L d p) (domSet L d m))
        (Exp.exp (Exp.exp (Exp.exp (a * (p + 1))))))
    (hne : DerivableLe U (insert (^∃ d) (∅ : V)) (Exp.exp a))
    {φ n : V} (hφ : Proof T n φ) (hφs : shift L φ = φ) :
    ProvableLe U (relativize L d φ) (provB a n) := by
  have hfst : fstIdx n = insert φ ∅ := by simpa using hφ.1
  have hder : Derivation T n := hφ.2
  have hφF : IsFormula L φ := by
    have := hder.isFormulaSet
    rw [hfst] at this
    simpa using this
  obtain ⟨m, hm, hD⟩ := derivableLe_relSet hd hds hTerm hda hna hdom hsubd hAx hder
  rw [hfst, relSet_insert] at hD
  have hrelempty : relSet L d (∅ : V) = ∅ := mem_ext fun y => by simp [mem_relSet_iff]
  rw [hrelempty] at hD
  have hD' : DerivableLe U (insert (relativize L d φ) (domSet L d m)) (towerB a n) := by
    refine DerivableLe.ofSetEq (fun x => ?_) hD
    simp
  have hn1 : (1 : V) ≤ n + 1 := le_add_self
  have he := four_le_nodeE a hn1
  have hBw := memB_le_nodeE a hn1
  have hφn : φ ≤ n + 1 := by
    have : φ ∈ fstIdx n := by rw [hfst]; simp
    exact le_trans (le_of_lt (lt_of_lt_of_le (lt_of_mem this) (fstIdx_le n))) le_self_add
  have hrB : relativize L d φ < memB a (n + 1) :=
    lt_of_le_of_lt (rel_le_bat hda hna hφn) (bat_lt_memB a _)
  have hdomB : ∀ i ≤ m, domF L d i < memB a (n + 1) := fun i hi =>
    lt_of_le_of_lt (dom_le_bat (le_trans hi (le_trans hm (_root_.add_le_add le_self_add le_rfl)))
      (hdom i)) (bat_lt_memB a _)
  have hallB : ^∀ (neg L d) < memB a (n + 1) := quant_lt_memB (by norm_num) hna
  have hexB : ^∃ d < memB a (n + 1) := quant_lt_memB (by norm_num) hda
  have hane : a ≤ nodeE a (n + 1) := le_trans (a_le_ac a)
    (le_trans (le_mul_of_one_le_right (Arithmetic.zero_le _) hn1) (self_le_exp_exp _))
  have hfin := derivableLe_of_domSet hd hds he hBw (hne.mono (exp_monotone_le.mpr hane))
    (isSemiformula_relativize hd hφF) (by rw [relativize_shift hd hds hφF.isUFormula, hφs])
    hrB hallB hexB m hdomB hD'
  obtain ⟨z, hz, hzD⟩ := hfin.mono (exp_monotone_le.mpr (mul_le_mul_of_nonneg_right
    (exp_monotone_le.mpr (mul_le_mul_of_nonneg_left hm (Arithmetic.zero_le _)))
    (Arithmetic.zero_le _)) : _ ≤ provB a n)
  exact ⟨z, hz, by simpa using! hzD⟩

/-- **Consistency transfer with sizes**: a `T`-refutation with code `n`
yields a `U`-refutation with code at most `provB a n`. -/
theorem provableLe_falsum_of_relativize (hd : IsSemiformula L 1 d) (hds : shift L d = d)
    (hTerm : ∀ t : V, IsTerm L t → ∃ j, t = ^&j)
    (hda : d ≤ a) (hna : neg L d ≤ a)
    (hdom : ∀ i, domF L d i ≤ Exp.exp (a * (i + 1)))
    (hsubd : ∀ i, substs1 L ^&i d ≤ Exp.exp (a * (i + 1)))
    (hAx : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class →
      ∃ m, m ≤ p + a ∧ DerivableLe U (insert (relativize L d p) (domSet L d m))
        (Exp.exp (Exp.exp (Exp.exp (a * (p + 1))))))
    (hne : DerivableLe U (insert (^∃ d) (∅ : V)) (Exp.exp a))
    {n : V} (h : Proof T n (^⊥ : V)) : ProvableLe U (^⊥ : V) (provB a n) := by
  simpa using provableLe_relativize hd hds hTerm hda hna hdom hsubd hAx hne h (by simp)

end Interpretation

end LeanProofs.BoundedPAConsistency.InternalRelativizationBound
