import BoundedPAConsistency.InternalRelativization
import BoundedPAConsistency.SizedDerivation

/-!
# Shifting at most squares a code

In every model of `𝗜𝚺₁`, the free-variable shift of an internal term or
formula is at most the square of its code (`termShift_le_sq`, `shift_le_sq`).
The reason is arithmetic: a Cantor pairing of two entries bounded by squares
is bounded by the square of the pairing (`pair_le_sq`, `pair_succ_le_sq`),
and the only leaf the shift changes, `&x ↦ &(x+1)`, also stays below the
square (`fvar_succ_le_sq`).

Since the domain side formulas satisfy `¬δ(&(i+1)) = shift (¬δ(&i))`
(`InternalRelativization.shift_domF`), iterating gives the double-exponential
bounds `domF L d i ≤ 2^(2^(a·(i+1)))` and `δ(&i) ≤ 2^(2^(a·(i+1)))` from bounds
on the two codes at `i = 0` (`domF_le`, `substs1_fvar_le`). These are the
side-formula hypotheses of `InternalRelativizationBound`.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.BoundedPAConsistency.ShiftBound

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.InternalRelativization

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Squares and Cantor pairs -/

section Arith

theorem le_sq (x : V) : x ≤ x * x := by
  rcases zero_or_succ x with rfl | ⟨y, rfl⟩
  · simp
  · exact le_mul_of_one_le_left (Arithmetic.zero_le _) le_add_self

theorem pair_sq_sq (a b : V) : ⟪a * a, b * b⟫ ≤ ⟪a, b⟫ * ⟪a, b⟫ := by
  simp only [pair]
  split_ifs with h₁ h₂ h₂
  · have e : (b * b + a) * (b * b + a) = b * b * (b * b) + a * a + 2 * a * (b * b) := by ring
    rw [e]
    exact le_self_add
  · exfalso
    have hba : b ≤ a := not_lt.mp h₂
    exact absurd h₁ (not_lt.mpr (mul_le_mul hba hba (Arithmetic.zero_le _) (Arithmetic.zero_le _)))
  · exfalso
    exact h₁ (mul_self_lt_mul_self (Arithmetic.zero_le _) h₂)
  · have e : (a * a + a + b) * (a * a + a + b) =
        a * a * (a * a) + a * a + b * b + 2 * (a * a * a + a * a * b + a * b) := by ring
    rw [e]
    exact le_self_add

/-- **A pairing of entries below squares is below the square of the pairing.** -/
theorem pair_le_sq {a b a' b' : V} (ha : a' ≤ a * a) (hb : b' ≤ b * b) :
    ⟪a', b'⟫ ≤ ⟪a, b⟫ * ⟪a, b⟫ :=
  le_trans (pair_le_pair ha hb) (pair_sq_sq a b)

theorem succ_sq_le {x y : V} (h : y ≤ x * x) : y + 1 ≤ (x + 1) * (x + 1) := by
  have e : (x + 1) * (x + 1) = x * x + 1 + 2 * x := by ring
  rw [e]
  exact le_trans (_root_.add_le_add h le_rfl) le_self_add

theorem pair_succ_le_sq {a b a' b' : V} (ha : a' ≤ a * a) (hb : b' ≤ b * b) :
    ⟪a', b'⟫ + 1 ≤ (⟪a, b⟫ + 1) * (⟪a, b⟫ + 1) :=
  succ_sq_le (pair_le_sq ha hb)

/-- The free variable `&x` shifted to `&(x+1)` stays below `(&x)²`. -/
theorem fvar_succ_le_sq (x : V) : (^&(x + 1) : V) ≤ ^&x * ^&x := by
  simp only [qqFvar]
  rcases zero_or_succ x with rfl | ⟨y, rfl⟩
  · rw [zero_add, show (⟪(1 : V), 1⟫ : V) = 3 by simp [pair]; norm_num,
      show (⟪(1 : V), 0⟫ : V) = 2 by simp [pair]; norm_num]
    norm_num
  rcases zero_or_succ y with rfl | ⟨z, rfl⟩
  · rw [zero_add, show (1 : V) + 1 = 2 by norm_num,
      show (⟪(1 : V), 2⟫ : V) = 5 by simp [pair]; norm_num,
      show (⟪(1 : V), 1⟫ : V) = 3 by simp [pair]; norm_num]
    norm_num
  have hW : (2 : V) ≤ z + 1 + 1 := by
    rw [add_assoc, one_add_one_eq_two]
    exact le_add_self
  have hlt : ∀ w : V, 2 ≤ w → (1 : V) < w := fun w hw => lt_of_lt_of_le (by norm_num) hw
  have hp1 : (⟪(1 : V), z + 1 + 1 + 1⟫ : V) = (z + 1 + 1 + 1) * (z + 1 + 1 + 1) + 1 := by
    simp [pair, hlt _ (le_trans hW le_self_add)]
  have hp0 : (⟪(1 : V), z + 1 + 1⟫ : V) = (z + 1 + 1) * (z + 1 + 1) + 1 := by
    simp [pair, hlt _ hW]
  rw [hp1, hp0]
  set W := z + 1 + 1 with hWdef
  have h2W : 2 * W ≤ W * W := mul_le_mul_of_nonneg_right hW (Arithmetic.zero_le _)
  calc (W + 1) * (W + 1) + 1 + 1 = W * W + 2 * W + 3 := by ring
    _ ≤ W * W + W * W + 3 := _root_.add_le_add (_root_.add_le_add le_rfl h2W) le_rfl
    _ ≤ W * W + W * W + 3 + (W * W * (W * W) + 2 * (W * W) + 1) := le_self_add
    _ = (W * W + 1 + 1) * (W * W + 1 + 1) := by ring

end Arith

/-! ## Terms, term vectors, formulas -/

variable {L : Language} [L.Encodable] [L.LORDefinable]

theorem isUTermVec_tail {k t ts : V} (h : IsUTermVec L (k + 1) (t ∷ ts)) :
    IsUTerm L t ∧ IsUTermVec L k ts := by
  refine ⟨by simpa using h.2 0 (by simp), ?_, fun i hi => ?_⟩
  · have := h.1
    simp at this
    exact this
  · simpa using h.2 (i + 1) (by simpa using hi)

/-- Shifting a term vector whose entries shift below their squares. -/
theorem termShiftVec_le_sq : ∀ k : V, ∀ ts : V, IsUTermVec L k ts →
    (∀ i < k, termShift L ts.[i] ≤ ts.[i] * ts.[i]) → termShiftVec L k ts ≤ ts * ts := by
  intro k
  induction k using ISigma1.pi1_succ_induction
  · definability
  · intro ts hts _
    have : ts = 0 := len_zero_iff_eq_nil.mp hts.1.symm
    subst this
    simp
  · case succ k ih =>
    intro ts hts hent
    rcases adjoin_cases ts with rfl | ⟨t, ts', rfl⟩
    · exfalso
      have := hts.1
      simp at this
    · obtain ⟨ht, hts'⟩ := isUTermVec_tail hts
      rw [termShiftVec_cons ht hts']
      have h0 : termShift L t ≤ t * t := by simpa using hent 0 (by simp)
      have hr : termShiftVec L k ts' ≤ ts' * ts' := ih ts' hts' fun i hi => by
        simpa using hent (i + 1) (by simpa using hi)
      simp only [adjoin_def]
      exact pair_succ_le_sq h0 hr

/-- **Shifting a term at most squares its code.** -/
theorem termShift_le_sq : ∀ t : V, IsUTerm L t → termShift L t ≤ t * t := by
  refine IsUTerm.induction 𝚷 (P := fun t => termShift L t ≤ t * t) ?_ ?_ ?_ ?_
  · definability
  · intro z
    rw [termShift_bvar]
    exact le_sq _
  · intro x
    rw [termShift_fvar]
    exact fvar_succ_le_sq x
  · intro k f v hkf hv ih
    rw [termShift_func hkf hv]
    simp only [qqFunc]
    exact pair_succ_le_sq (le_sq _) (pair_le_sq (le_sq _) (pair_le_sq (le_sq _)
      (termShiftVec_le_sq k v hv ih)))

theorem termShiftVec_le_sq' {k ts : V} (hts : IsUTermVec L k ts) :
    termShiftVec L k ts ≤ ts * ts :=
  termShiftVec_le_sq k ts hts fun i hi => termShift_le_sq _ (hts.2 i hi)

/-- **Shifting a formula at most squares its code.** -/
theorem shift_le_sq (p : V) : shift L p ≤ p * p := by
  by_cases hp : IsUFormula L p
  swap
  · rw [shift_not_uformula hp]
    exact Arithmetic.zero_le _
  refine IsUFormula.ISigma1.sigma1_succ_induction (P := fun p => shift L p ≤ p * p)
    (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro k R v hR hv
    rw [shift_rel hR hv]
    simp only [qqRel]
    exact pair_succ_le_sq (le_sq _) (pair_le_sq (le_sq _) (pair_le_sq (le_sq _)
      (termShiftVec_le_sq' hv)))
  · intro k R v hR hv
    rw [shift_nrel hR hv]
    simp only [qqNRel]
    exact pair_succ_le_sq (le_sq _) (pair_le_sq (le_sq _) (pair_le_sq (le_sq _)
      (termShiftVec_le_sq' hv)))
  · rw [shift_verum]
    exact le_sq _
  · rw [shift_falsum]
    exact le_sq _
  · intro p q hp hq ihp ihq
    rw [shift_and hp hq]
    simp only [qqAnd]
    exact pair_succ_le_sq (le_sq _) (pair_le_sq ihp ihq)
  · intro p q hp hq ihp ihq
    rw [shift_or hp hq]
    simp only [qqOr]
    exact pair_succ_le_sq (le_sq _) (pair_le_sq ihp ihq)
  · intro p hp ih
    rw [shift_all hp]
    simp only [qqAll]
    exact pair_succ_le_sq (le_sq _) ih
  · intro p hp ih
    rw [shift_exs hp]
    simp only [qqExs]
    exact pair_succ_le_sq (le_sq _) ih

/-! ## Towers for the domain side formulas -/

section Towers

variable {d : V}

theorem sq_exp_exp (E : V) : Exp.exp E * Exp.exp E = Exp.exp (E + E) := by
  rw [exp_add]

theorem tower_step {a i : V} (ha : 1 ≤ a) :
    Exp.exp (Exp.exp (a * (i + 1)) + Exp.exp (a * (i + 1))) ≤ Exp.exp (Exp.exp (a * (i + 1 + 1))) := by
  refine exp_monotone_le.mpr ?_
  rw [show Exp.exp (a * (i + 1)) + Exp.exp (a * (i + 1)) = Exp.exp (a * (i + 1) + 1) by
    rw [exp_succ]; ring]
  refine exp_monotone_le.mpr ?_
  calc a * (i + 1) + 1 ≤ a * (i + 1) + a := _root_.add_le_add le_rfl ha
    _ = a * (i + 1 + 1) := by ring

theorem shift_substs1_fvar (hd : IsSemiformula L 1 d) (hds : shift L d = d) (i : V) :
    shift L (substs1 L ^&i d) = substs1 L ^&(i + 1) d := by
  simp only [substs1]
  rw [shift_substs hd (show IsSemitermVec L 1 0 ?[(^&i : V)] by simp), hds]
  simp

/-- **Side formulas `¬δ(&i)` grow at most double exponentially in `i`.** -/
theorem domF_le (hd : IsSemiformula L 1 d) (hds : shift L d = d) {a : V} (ha : 1 ≤ a)
    (h0 : domF L d 0 ≤ Exp.exp (Exp.exp a)) :
    ∀ i, domF L d i ≤ Exp.exp (Exp.exp (a * (i + 1))) := by
  intro i
  induction i using ISigma1.sigma1_succ_induction
  · simp only [domF]
    definability
  · simpa using h0
  · case succ i ih =>
    rw [← shift_domF hd hds i]
    exact le_trans (shift_le_sq _) (le_trans (mul_le_mul ih ih (Arithmetic.zero_le _)
      (Arithmetic.zero_le _)) (by rw [sq_exp_exp]; exact tower_step ha))

/-- **`δ(&i)` grows at most double exponentially in `i`.** -/
theorem substs1_fvar_le (hd : IsSemiformula L 1 d) (hds : shift L d = d) {a : V} (ha : 1 ≤ a)
    (h0 : substs1 L ^&0 d ≤ Exp.exp (Exp.exp a)) :
    ∀ i, substs1 L ^&i d ≤ Exp.exp (Exp.exp (a * (i + 1))) := by
  intro i
  induction i using ISigma1.sigma1_succ_induction
  · definability
  · simpa using h0
  · case succ i ih =>
    rw [← shift_substs1_fvar hd hds i]
    exact le_trans (shift_le_sq _) (le_trans (mul_le_mul ih ih (Arithmetic.zero_le _)
      (Arithmetic.zero_le _)) (by rw [sq_exp_exp]; exact tower_step ha))

end Towers

end LeanProofs.BoundedPAConsistency.ShiftBound
