import BoundedPAConsistency.InternalRelativizationBound

/-!
# Size-bounded Hilbert combinators for internal proofs

Foundation's typed internal proofs (`T ⊢! φ`) expose explicit codes only for
the primitive constructors (`TDerivation.em`, `and'`, `or'`, `all'`, `exs'`,
`wk`, `shift`, `cut`). The derived constructors `TDerivation.and`/`or`/`all`/
`exs` go through `Derivable.toTDerivation`, so their codes are chosen by
`Classical.choose`, and therefore so are the codes of modus ponens and of
every Hilbert axiom of the internal `Entailment` instance. No size bound
follows from those definitions.

This module re-derives, from the bounded primitive rules of
`SizedDerivation`, the six combinators used by the constructible-universe
schema obligations: modus ponens (`mdp`), `K_intro`, `K_left`, `K_right`,
`C_id` and `E_id`. Each takes one member bound `B` for the formulas it puts
into sequents and costs at most four bounded rule applications.
`neg_code_le` bounds negation codes so that callers can supply those member
bounds: `neg L q ≤ 2^(2^(12·(q+1)))`.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.BoundedPAConsistency.SizedProof

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.BoundedPAConsistency.InternalRelativizationBound

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ## Negation codes -/

theorem lt_node_le {x n : V} (h : x < n) : x ≤ Exp.exp (Exp.exp ((0 + 12) * n)) := by
  refine le_trans (le_of_lt h) (le_trans ?_ (self_le_exp_exp _))
  exact le_mul_of_one_le (by norm_num)

theorem small_le_relB {k : V} (hk : k ≤ 9) (x : V) : ⟪k, 0⟫ + 1 ≤ relB 0 x := by
  have h := pair_succ_le_exp (show (3 : V) ≤ 4 by norm_num) (tag_le hk le_rfl)
    (Arithmetic.zero_le (Exp.exp (4 : V)))
  refine le_trans h ?_
  unfold relB
  refine exp_monotone_le.mpr ?_
  calc (4 : V) * 4 = 16 := by norm_num
    _ = Exp.exp 4 := by rw [show (4 : V) = 2 * 2 by norm_num, exp_even, exp_two]; norm_num
    _ ≤ Exp.exp ((0 + 12) * (x + 1)) := exp_monotone_le.mpr (by
        rw [zero_add]
        exact le_trans (by norm_num : (4 : V) ≤ 12)
          (le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self))

/-- **Negation codes stay below `relB 0 q = 2^(2^(12·(q+1)))`.** -/
theorem neg_code_le (q : V) : neg L q ≤ relB 0 q := by
  by_cases hq : IsUFormula L q
  swap
  · rw [neg_not_uformula hq]
    exact Arithmetic.zero_le _
  refine IsUFormula.ISigma1.sigma1_succ_induction
    (P := fun p => neg L p ≤ Exp.exp (Exp.exp ((0 + 12) * (p + 1)))) (by definability)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
  · intro k R v hR hv
    rw [neg_rel hR hv]
    have hn := one_le_of_lt (arity_lt_rel k R v)
    have he := four_le_level 0 hn
    refine le_trans ?_ (node3_le_relB 0)
    exact tuple4_le he (tag_le (by norm_num) he)
      (lt_node_le (arity_lt_rel k R v)) (lt_node_le (r_lt_rel k R v))
      (lt_node_le (v_lt_rel k R v))
  · intro k R v hR hv
    rw [neg_nrel hR hv]
    have hn := one_le_of_lt (arity_lt_nrel k R v)
    have he := four_le_level 0 hn
    refine le_trans ?_ (node3_le_relB 0)
    exact tuple4_le he (tag_le (by norm_num) he)
      (lt_node_le (arity_lt_nrel k R v)) (lt_node_le (r_lt_nrel k R v))
      (lt_node_le (v_lt_nrel k R v))
  · rw [neg_verum]
    exact small_le_relB (by norm_num) _
  · rw [neg_falsum]
    exact small_le_relB (by norm_num) _
  · intro p q hp hq ihp ihq
    rw [neg_and hp hq]
    have hn : 1 ≤ p ^⋏ q := one_le_of_lt (lt_K!_left p q)
    have he := four_le_level 0 hn
    refine le_trans ?_ (node3_le_relB 0)
    exact tuple3_le he (tag_le (by norm_num) he)
      (le_trans ihp (relB_le_of_lt 0 (lt_K!_left p q)))
      (le_trans ihq (relB_le_of_lt 0 (lt_K!_right p q)))
  · intro p q hp hq ihp ihq
    rw [neg_or hp hq]
    have hn : 1 ≤ p ^⋎ q := one_le_of_lt (lt_or_left p q)
    have he := four_le_level 0 hn
    refine le_trans ?_ (node3_le_relB 0)
    exact tuple3_le he (tag_le (by norm_num) he)
      (le_trans ihp (relB_le_of_lt 0 (lt_or_left p q)))
      (le_trans ihq (relB_le_of_lt 0 (lt_or_right p q)))
  · intro p hp ih
    rw [neg_all hp]
    have hn : 1 ≤ ^∀ p := one_le_of_lt (lt_forall p)
    have he := four_le_level 0 hn
    refine le_trans ?_ (node3_le_relB 0)
    exact le_trans (pair_succ_le_exp (le_trans (by norm_num) he) (tag_le (by norm_num) he)
      (le_trans ih (relB_le_of_lt 0 (lt_forall p)))) (exp_monotone_le.mpr
        (mul_le_mul_of_nonneg_right (by norm_num) (Arithmetic.zero_le _)))
  · intro p hp ih
    rw [neg_ex hp]
    have hn : 1 ≤ ^∃ p := one_le_of_lt (lt_exists p)
    have he := four_le_level 0 hn
    refine le_trans ?_ (node3_le_relB 0)
    exact le_trans (pair_succ_le_exp (le_trans (by norm_num) he) (tag_le (by norm_num) he)
      (le_trans ih (relB_le_of_lt 0 (lt_exists p)))) (exp_monotone_le.mpr
        (mul_le_mul_of_nonneg_right (by norm_num) (Arithmetic.zero_le _)))

/-! ## The Hilbert combinators, with sizes

All statements are about singleton sequents `insert φ ∅`, i.e. internal
proofs (`Proof T z φ ↔ DerivationOf T z {φ}`). The member bound `B` must
bound every formula listed in the hypotheses; `e ≥ B` is the exponent
budget of the inputs. -/

section Combinators

variable {T : Theory L} [T.Δ₁] {e B : V}

theorem empty_lt (B : V) : ∀ y ∈ (∅ : V), y < B := fun y hy => by simp at hy

theorem single_lt {x B : V} (hx : x < B) : ∀ y ∈ insert x (∅ : V), y < B :=
  DerivableLe.insert_lt hx (empty_lt B)

theorem stage_mono₁ (e : V) : Exp.exp (1024 * e) ≤ Exp.exp (1024 * (1024 * e)) :=
  exp_monotone_le.mpr DerivableLe.le_1024

theorem stage_mono₂ (e : V) :
    Exp.exp (1024 * (1024 * e)) ≤ Exp.exp (1024 * (1024 * (1024 * e))) :=
  exp_monotone_le.mpr DerivableLe.le_1024

theorem stage_mono₃ (e : V) :
    Exp.exp (1024 * (1024 * (1024 * e))) ≤ Exp.exp (1024 * (1024 * (1024 * (1024 * e)))) :=
  exp_monotone_le.mpr DerivableLe.le_1024

/-- **`⊢ φ → φ`** (`C_id`). -/
theorem C_id {φ : V} (hφ : IsFormula L φ) (he : 4 ≤ e) (hBe : B ≤ e)
    (hφB : φ < B) (hnB : neg L φ < B) (himpB : neg L φ ^⋎ φ < B) :
    DerivableLe T (insert (neg L φ ^⋎ φ) (∅ : V)) (Exp.exp (1024 * (1024 * e))) := by
  have hS := single_lt (B := B) himpB
  refine DerivableLe.or_m (DerivableLe.four_le_1024 he)
    (le_exp_of_le (DerivableLe.seq_le hBe hS) DerivableLe.le_1024) (p := neg L φ) (q := φ)
    (by simp) ?_
  refine DerivableLe.em he (DerivableLe.seq_le hBe (DerivableLe.insert_lt hnB
    (DerivableLe.insert_lt hφB hS))) (by simp [hφ, hφ.neg]) φ (by simp) (by simp)

/-- **`⊢ φ ∧ ψ` from `⊢ φ` and `⊢ ψ`** (`K_intro`). -/
theorem K_intro {φ ψ : V} (he : 4 ≤ e) (hBe : B ≤ e) (hB : φ ^⋏ ψ < B)
    (hφ : DerivableLe T (insert φ (∅ : V)) (Exp.exp e))
    (hψ : DerivableLe T (insert ψ (∅ : V)) (Exp.exp e)) :
    DerivableLe T (insert (φ ^⋏ ψ) (∅ : V)) (Exp.exp (1024 * (1024 * e))) :=
  DerivableLe.and he hBe (empty_lt B) hB hφ hψ

/-- **`⊢ φ` from `⊢ φ ∧ ψ`** (`K_left`). -/
theorem K_left {φ ψ : V} (he : 4 ≤ e) (hBe : B ≤ e)
    (hφB : φ < B) (hpqB : φ ^⋏ ψ < B) (hnφB : neg L φ < B) (hnψB : neg L ψ < B)
    (hnB : neg L φ ^⋎ neg L ψ < B)
    (h : DerivableLe T (insert (φ ^⋏ ψ) (∅ : V)) (Exp.exp e)) :
    DerivableLe T (insert φ (∅ : V)) (Exp.exp (1024 * (1024 * (1024 * e)))) := by
  have hF := h.isFormulaSet
  have hpq : IsFormula L (φ ^⋏ ψ) := by simpa using hF
  have hφ : IsFormula L φ := (IsSemiformula.and.mp hpq).1
  have hψ : IsFormula L ψ := (IsSemiformula.and.mp hpq).2
  have hS := single_lt (B := B) hφB
  have d₁ := DerivableLe.wk he (DerivableLe.seq_le hBe (DerivableLe.insert_lt hpqB hS))
    (by simp [hpq, hφ]) (by intro x; simp; tauto) h
  have hS₂ := DerivableLe.insert_lt hnB hS
  have d₂ := DerivableLe.or_m (T := T) (DerivableLe.four_le_1024 he)
    (le_exp_of_le (DerivableLe.seq_le hBe hS₂) DerivableLe.le_1024) (p := neg L φ) (q := neg L ψ)
    (by simp)
    (DerivableLe.em he (DerivableLe.seq_le hBe (DerivableLe.insert_lt hnφB
      (DerivableLe.insert_lt hnψB hS₂))) (by simp [hφ, hφ.neg, hψ.neg]) φ (by simp) (by simp))
  refine DerivableLe.cut (DerivableLe.four_le_1024 (DerivableLe.four_le_1024 he))
    (le_exp_of_le (DerivableLe.seq_le hBe hS) (le_trans DerivableLe.le_1024 DerivableLe.le_1024))
    (φ ^⋏ ψ) (le_exp_of_le_self (le_trans (le_of_lt hpqB)
      (le_trans hBe (le_trans DerivableLe.le_1024 DerivableLe.le_1024))))
    (d₁.mono (stage_mono₁ e)) ?_
  rw [neg_and hφ.isUFormula hψ.isUFormula]
  exact d₂

/-- **`⊢ ψ` from `⊢ φ ∧ ψ`** (`K_right`). -/
theorem K_right {φ ψ : V} (he : 4 ≤ e) (hBe : B ≤ e)
    (hψB : ψ < B) (hpqB : φ ^⋏ ψ < B) (hnφB : neg L φ < B) (hnψB : neg L ψ < B)
    (hnB : neg L φ ^⋎ neg L ψ < B)
    (h : DerivableLe T (insert (φ ^⋏ ψ) (∅ : V)) (Exp.exp e)) :
    DerivableLe T (insert ψ (∅ : V)) (Exp.exp (1024 * (1024 * (1024 * e)))) := by
  have hF := h.isFormulaSet
  have hpq : IsFormula L (φ ^⋏ ψ) := by simpa using hF
  have hφ : IsFormula L φ := (IsSemiformula.and.mp hpq).1
  have hψ : IsFormula L ψ := (IsSemiformula.and.mp hpq).2
  have hS := single_lt (B := B) hψB
  have d₁ := DerivableLe.wk he (DerivableLe.seq_le hBe (DerivableLe.insert_lt hpqB hS))
    (by simp [hpq, hψ]) (by intro x; simp; tauto) h
  have hS₂ := DerivableLe.insert_lt hnB hS
  have d₂ := DerivableLe.or_m (T := T) (DerivableLe.four_le_1024 he)
    (le_exp_of_le (DerivableLe.seq_le hBe hS₂) DerivableLe.le_1024) (p := neg L φ) (q := neg L ψ)
    (by simp)
    (DerivableLe.em he (DerivableLe.seq_le hBe (DerivableLe.insert_lt hnφB
      (DerivableLe.insert_lt hnψB hS₂))) (by simp [hψ, hφ.neg, hψ.neg]) ψ (by simp) (by simp))
  refine DerivableLe.cut (DerivableLe.four_le_1024 (DerivableLe.four_le_1024 he))
    (le_exp_of_le (DerivableLe.seq_le hBe hS) (le_trans DerivableLe.le_1024 DerivableLe.le_1024))
    (φ ^⋏ ψ) (le_exp_of_le_self (le_trans (le_of_lt hpqB)
      (le_trans hBe (le_trans DerivableLe.le_1024 DerivableLe.le_1024))))
    (d₁.mono (stage_mono₁ e)) ?_
  rw [neg_and hφ.isUFormula hψ.isUFormula]
  exact d₂

/-- **Modus ponens**: `⊢ ψ` from `⊢ φ → ψ` and `⊢ φ` (`φ → ψ` is `¬φ ∨ ψ`). -/
theorem mdp {φ ψ : V} (he : 4 ≤ e) (hBe : B ≤ e)
    (hφB : φ < B) (hψB : ψ < B) (hnψB : neg L ψ < B) (himpB : neg L φ ^⋎ ψ < B)
    (handB : φ ^⋏ neg L ψ < B)
    (h₁ : DerivableLe T (insert (neg L φ ^⋎ ψ) (∅ : V)) (Exp.exp e))
    (h₂ : DerivableLe T (insert φ (∅ : V)) (Exp.exp e)) :
    DerivableLe T (insert ψ (∅ : V)) (Exp.exp (1024 * (1024 * (1024 * (1024 * e))))) := by
  have hφ : IsFormula L φ := by simpa using h₂.isFormulaSet
  have himp : IsFormula L (neg L φ ^⋎ ψ) := by simpa using h₁.isFormulaSet
  have hψ : IsFormula L ψ := (IsSemiformula.or.mp himp).2
  have hS := single_lt (B := B) hψB
  have d := DerivableLe.wk he (DerivableLe.seq_le hBe (DerivableLe.insert_lt himpB hS))
    (by simp [himp, hψ]) (by intro x; simp; tauto) h₁
  have p₁ := DerivableLe.wk he (DerivableLe.seq_le hBe (DerivableLe.insert_lt hφB hS))
    (by simp [hφ, hψ]) (by intro x; simp; tauto) h₂
  have p₂ := DerivableLe.em (T := T) he
    (DerivableLe.seq_le hBe (DerivableLe.insert_lt hnψB hS)) (by simp [hψ, hψ.neg]) ψ
    (by simp) (by simp)
  have b := DerivableLe.and (DerivableLe.four_le_1024 he) (le_trans hBe DerivableLe.le_1024)
    hS handB p₁ p₂
  refine DerivableLe.cut (DerivableLe.four_le_1024 (DerivableLe.four_le_1024
      (DerivableLe.four_le_1024 he)))
    (le_exp_of_le (DerivableLe.seq_le hBe hS)
      (le_trans DerivableLe.le_1024 (le_trans DerivableLe.le_1024 DerivableLe.le_1024)))
    (neg L φ ^⋎ ψ) (le_exp_of_le_self (le_trans (le_of_lt himpB)
      (le_trans hBe (le_trans DerivableLe.le_1024 (le_trans DerivableLe.le_1024
        DerivableLe.le_1024)))))
    (d.mono (le_trans (stage_mono₁ e) (stage_mono₂ e))) ?_
  rw [neg_or hφ.isUFormula.neg hψ.isUFormula, hφ.isUFormula.neg_neg]
  exact b

/-- **`⊢ φ ↔ φ`** (`E_id`), with `φ ↔ φ` coded as `(φ → φ) ∧ (φ → φ)`. -/
theorem E_id {φ : V} (hφ : IsFormula L φ) (he : 4 ≤ e) (hBe : B ≤ e)
    (hφB : φ < B) (hnB : neg L φ < B) (himpB : neg L φ ^⋎ φ < B)
    (hiffB : (neg L φ ^⋎ φ) ^⋏ (neg L φ ^⋎ φ) < B) :
    DerivableLe T (insert ((neg L φ ^⋎ φ) ^⋏ (neg L φ ^⋎ φ)) (∅ : V))
      (Exp.exp (1024 * (1024 * (1024 * (1024 * e))))) := by
  have c := C_id (T := T) hφ he hBe hφB hnB himpB
  exact K_intro (DerivableLe.four_le_1024 (DerivableLe.four_le_1024 he))
    (le_trans hBe (le_trans DerivableLe.le_1024 DerivableLe.le_1024)) hiffB c c

end Combinators

end LeanProofs.BoundedPAConsistency.SizedProof
