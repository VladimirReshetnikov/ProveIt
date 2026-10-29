import BoundedPAConsistency.InternalRelativizationBound

/-!
# Substitution of variables at most double-exponentiates a code

In every model of `𝗜𝚺₁`: if `w` is a vector of variable terms (`^#z` or
`^&x`) whose entries are at most `2^c`, then for every internal formula `p`

`subst L w p ≤ tw (c + 12) p = 2^(2^((c+12)·(p+1)))` (`subst_le`).

Leaves only ever read the entries `w.[z]`, never the code of `w`, so only
entry bounds are needed. Under a binder the vector becomes
`qVec w = ^#0 ∷ bShift w`, and bShifting a variable at most quadruples it
(`bShift_var_le`), so the entry bound becomes `2^(c+2)`. The tower absorbs
that because a quantifier node has code at least `2(p+1)`
(`two_mul_le_all`). Terms (including function symbols) and term vectors are
bounded by the same tower shape (`termSubst_le`, `termSubstVec_le`).
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.BoundedPAConsistency.SubstBound

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.BoundedPAConsistency.InternalRelativizationBound

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The tower shape -/

section Tower

/-- The tower bound `2^(2^(K·(y+1)))`. -/
def tw (K y : V) : V := Exp.exp (Exp.exp (K * (y + 1)))

variable {K : V}

theorem tw_child {x n : V} (h : x < n) : tw K x ≤ Exp.exp (Exp.exp (K * n)) := by
  unfold tw
  exact exp_exp_mono (mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp h) (Arithmetic.zero_le _))

theorem self_le_tw (hK : 1 ≤ K) (x : V) : x ≤ tw K x := by
  unfold tw
  refine le_trans ?_ (self_le_exp_exp _)
  exact le_trans le_self_add (le_mul_of_one_le hK)

theorem lt_le_level (hK : 1 ≤ K) {x n : V} (h : x < n) : x ≤ Exp.exp (Exp.exp (K * n)) :=
  le_trans (le_of_lt h) (le_trans (le_mul_of_one_le hK) (self_le_exp_exp _))

theorem four_le_level' (hK : 4 ≤ K) {n : V} (hn : 1 ≤ n) : 4 ≤ Exp.exp (K * n) :=
  le_trans hK (le_trans (le_mul_of_one_le_right (Arithmetic.zero_le _) hn) (le_exp_self _))

/-- One pairing of entries at level `K·n` fits under `tw K n`. -/
theorem pair_tw (hK : 4 ≤ K) {a b n : V} (hn : 1 ≤ n) (ha : a ≤ Exp.exp (Exp.exp (K * n)))
    (hb : b ≤ Exp.exp (Exp.exp (K * n))) : ⟪a, b⟫ + 1 ≤ tw K n := by
  have he := four_le_level' hK hn
  refine le_trans (pair_succ_le_exp (le_trans (by norm_num) he) ha hb) ?_
  unfold tw
  refine exp_monotone_le.mpr ?_
  rw [show 4 * Exp.exp (K * n) = Exp.exp (K * n + 2) by rw [exp_add, exp_two]; ring]
  refine exp_monotone_le.mpr ?_
  calc K * n + 2 ≤ K * n + K := _root_.add_le_add le_rfl (le_trans (by norm_num) hK)
    _ = K * (n + 1) := by ring

/-- A fixed tuple (one `1024`-stage) at level `K·n` fits under `tw K n`. -/
theorem stage_tw (hK : 10 ≤ K) {x n : V} (h : x ≤ Exp.exp (1024 * Exp.exp (K * n))) :
    x ≤ tw K n := by
  refine le_trans h ?_
  unfold tw
  rw [mul1024_exp]
  refine exp_monotone_le.mpr (exp_monotone_le.mpr ?_)
  calc K * n + 10 ≤ K * n + K := _root_.add_le_add le_rfl hK
    _ = K * (n + 1) := by ring

end Tower

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ## Terms and term vectors -/

section Terms

variable {K c w : V}

theorem isUTermVec_tail {k t ts : V} (h : IsUTermVec L (k + 1) (t ∷ ts)) :
    IsUTerm L t ∧ IsUTermVec L k ts := by
  refine ⟨by simpa using h.2 0 (by simp), ?_, fun i hi => ?_⟩
  · have := h.1
    simp at this
    exact this
  · simpa using h.2 (i + 1) (by simpa using hi)

/-- Substituting into a term vector whose entries obey the tower bound. -/
theorem termSubstVec_le (hK : 4 ≤ K) : ∀ k : V, ∀ ts : V, IsUTermVec L k ts →
    (∀ i < k, termSubst L w ts.[i] ≤ tw K ts.[i]) → termSubstVec L k w ts ≤ tw K ts := by
  intro k
  induction k using ISigma1.pi1_succ_induction
  · unfold tw
    definability
  · intro ts hts _
    have : ts = 0 := len_zero_iff_eq_nil.mp hts.1.symm
    subst this
    simp [tw]
  · case succ k ih =>
    intro ts hts hent
    rcases adjoin_cases ts with rfl | ⟨t, ts', rfl⟩
    · exfalso
      have := hts.1
      simp at this
    · obtain ⟨ht, hts'⟩ := isUTermVec_tail hts
      rw [termSubstVec_cons ht hts']
      have h0 : termSubst L w t ≤ tw K t := by simpa using hent 0 (by simp)
      have hr : termSubstVec L k w ts' ≤ tw K ts' := ih ts' hts' fun i hi => by
        simpa using hent (i + 1) (by simpa using hi)
      simp only [adjoin_def]
      exact pair_tw hK (one_le_of_lt (lt_adjoin t ts'))
        (le_trans h0 (tw_child (lt_adjoin t ts'))) (le_trans hr (tw_child (lt_adjoin' t ts')))

/-- **Substitution into a term**, entries of `w` at most `2^c`. -/
theorem termSubst_le (hK : 10 ≤ K) (hc : c ≤ K) (hw : ∀ z, w.[z] ≤ Exp.exp c) :
    ∀ t, IsUTerm L t → termSubst L w t ≤ tw K t := by
  refine IsUTerm.induction 𝚷 (P := fun t => termSubst L w t ≤ tw K t) ?_ ?_ ?_ ?_
  · unfold tw
    definability
  · intro z
    rw [termSubst_bvar]
    refine le_trans (hw z) ?_
    unfold tw
    refine exp_monotone_le.mpr (le_trans ?_ (le_exp_self _))
    exact le_trans hc (le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self)
  · intro x
    rw [termSubst_fvar]
    exact self_le_tw (le_trans (by norm_num) hK) _
  · intro k f v hkf hv ih
    rw [termSubst_func hkf hv]
    have hn : 1 ≤ ^func k f v := one_le_of_lt (arity_lt_qqFunc k f v)
    have hK1 : 1 ≤ K := le_trans (by norm_num) hK
    have he := four_le_level' (le_trans (by norm_num) hK) hn
    simp only [qqFunc]
    refine stage_tw hK (tuple4_le he (tag_le (by norm_num) he)
      (lt_le_level hK1 (arity_lt_qqFunc k f v)) (lt_le_level hK1 (func_lt_qqFunc k f v))
      (le_trans (termSubstVec_le (le_trans (by norm_num) hK) k v hv ih)
        (tw_child (terms_lt_qqFunc k f v))))

end Terms

/-! ## Formulas -/

section Formulas

/-- A variable term. -/
def IsVarTerm (t : V) : Prop := ∃ z < t, t = ^#z ∨ t = ^&z

theorem isVarTerm_bvar (z : V) : IsVarTerm (^#z : V) :=
  ⟨z, lt_succ_iff_le.mpr (le_pair_right 0 z), Or.inl rfl⟩

theorem bShift_var_le {t : V} (ht : IsVarTerm t) : termBShift L t ≤ 4 * t := by
  obtain ⟨z, -, rfl | rfl⟩ := ht
  · rw [termBShift_bvar]
    simp only [qqBvar]
    rcases zero_or_succ z with rfl | ⟨y, rfl⟩
    · simp [pair]
      norm_num
    · have h1 : (0 : V) < y + 1 + 1 := by simp
      have h2 : (0 : V) < y + 1 := by simp
      simp only [pair, h1, h2, if_true]
      have e : 4 * ((y + 1) * (y + 1) + 0 + 1) =
          (y + 1 + 1) * (y + 1 + 1) + 0 + 1 + (3 * (y * y) + 4 * y + 3) := by ring
      rw [e]
      exact le_self_add
  · rw [termBShift_fvar]
    exact le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)

theorem bShift_isVar {t : V} (ht : IsVarTerm t) : IsVarTerm (termBShift L t) := by
  obtain ⟨z, -, rfl | rfl⟩ := ht
  · rw [termBShift_bvar]
    exact isVarTerm_bvar _
  · rw [termBShift_fvar]
    exact ⟨z, lt_succ_iff_le.mpr (le_pair_right 1 z), Or.inr rfl⟩

/-- A quantifier node has code at least `2(p+1)`. -/
theorem two_mul_le_pair {k p : V} (hk : 1 ≤ k) : 2 * (p + 1) ≤ ⟪k, p⟫ + 1 := by
  simp only [pair]
  split_ifs with h
  · -- k < p
    have hp1 : 1 ≤ p := le_trans hk (le_of_lt h)
    rcases zero_or_succ p with rfl | ⟨q, rfl⟩
    · simp at hp1
    · have hkq : k ≤ q := lt_succ_iff_le.mp h
      have hq1 : 1 ≤ q := le_trans hk hkq
      have hqq : 1 ≤ q * q := le_trans hq1 (le_mul_of_one_le_left (Arithmetic.zero_le _) hq1)
      calc 2 * (q + 1 + 1) = 2 * q + 2 + 1 + 1 := by ring
        _ ≤ 2 * q + 2 + q * q + k := _root_.add_le_add (_root_.add_le_add le_rfl hqq) hk
        _ = (q + 1) * (q + 1) + k + 1 := by ring
  · have hpk : p ≤ k := not_lt.mp h
    have hkk : 1 ≤ k * k := le_trans hk (le_mul_of_one_le_left (Arithmetic.zero_le _) hk)
    have h1 : p + 1 ≤ k * k + k := by
      rw [add_comm (k * k) k]
      exact _root_.add_le_add hpk hkk
    calc 2 * (p + 1) = (p + 1) + (p + 1) := by ring
      _ ≤ (k * k + k) + (p + 1) := _root_.add_le_add h1 le_rfl
      _ = k * k + k + p + 1 := by ring

theorem two_mul_le_all (p : V) : 2 * (p + 1) ≤ ^∀ p := two_mul_le_pair (by norm_num)

theorem two_mul_le_exs (p : V) : 2 * (p + 1) ≤ ^∃ p := two_mul_le_pair (by norm_num)

theorem quant_ineq (c p : V) {node : V} (hnode : 2 * (p + 1) ≤ node) :
    (c + 14) * (p + 1) + 2 ≤ (c + 12) * (node + 1) := by
  calc (c + 14) * (p + 1) + 2 ≤ (c + 14) * (p + 1) + 2 + ((c + 10) * (p + 1) + (c + 10)) :=
        le_self_add
    _ = (c + 12) * (2 * (p + 1) + 1) := by ring
    _ ≤ (c + 12) * (node + 1) :=
        mul_le_mul_of_nonneg_left (_root_.add_le_add hnode le_rfl) (Arithmetic.zero_le _)

/-- One quantifier node over a body bounded at entry level `c + 2`. -/
theorem quant_node_le {k c p X : V} (hk : k ≤ 9) (hnode : 2 * (p + 1) ≤ ⟪k, p⟫ + 1)
    (hX : X ≤ tw (c + 14) p) : ⟪k, X⟫ + 1 ≤ tw (c + 12) (⟪k, p⟫ + 1) := by
  have he : 4 ≤ Exp.exp ((c + 14) * (p + 1)) :=
    le_trans (by norm_num : (4 : V) ≤ 14) (le_trans le_add_self
      (le_trans (le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self) (le_exp_self _)))
  refine le_trans (pair_succ_le_exp (le_trans (by norm_num) he) (tag_le hk he) hX) ?_
  unfold tw
  refine exp_monotone_le.mpr ?_
  rw [show 4 * Exp.exp ((c + 14) * (p + 1)) = Exp.exp ((c + 14) * (p + 1) + 2) by
    rw [exp_add, exp_two]; ring]
  exact exp_monotone_le.mpr (quant_ineq c p hnode)

/-- **Substituting variables into a formula.** If the entries of the
semiterm vector `w` are variables at most `2^c`, then
`subst L w p ≤ 2^(2^((c+12)(p+1)))`. -/
theorem subst_le (p : V) : ∀ c ℓ n w : V, IsSemitermVec L ℓ n w →
    (∀ i < ℓ, w.[i] ≤ Exp.exp c) → (∀ i < ℓ, IsVarTerm w.[i]) →
    subst L w p ≤ tw (c + 12) p := by
  by_cases hp : IsUFormula L p
  swap
  · intro c ℓ n w _ _ _
    rw [substs_not_uformula hp]
    exact Arithmetic.zero_le _
  refine IsUFormula.ISigma1.pi1_succ_induction
    (P := fun p => ∀ c ℓ n w : V, IsSemitermVec L ℓ n w →
      (∀ i < ℓ, w.[i] ≤ Exp.exp c) → (∀ i < ℓ, ∃ z < w.[i], w.[i] = ^#z ∨ w.[i] = ^&z) →
      subst L w p ≤ Exp.exp (Exp.exp ((c + 12) * (p + 1))))
    (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro k R v hR hv c ℓ n w hw hwb hwv
    have hw' : ∀ z, w.[z] ≤ Exp.exp c := by
      intro z
      by_cases hz : z < ℓ
      · exact hwb z hz
      · rw [nth_lt_len (by rw [← hw.isUTerm.lh]; exact not_lt.mp hz)]
        exact Arithmetic.zero_le _
    rw [substs_rel hR hv]
    have hK : (10 : V) ≤ c + 12 := le_trans (by norm_num) le_add_self
    have hn : 1 ≤ ^rel k R v := one_le_of_lt (arity_lt_rel k R v)
    have he := four_le_level' (le_trans (by norm_num) hK) hn
    have hK1 : (1 : V) ≤ c + 12 := le_trans (by norm_num) hK
    simp only [qqRel]
    exact stage_tw hK (tuple4_le he (tag_le (by norm_num) he)
      (lt_le_level hK1 (arity_lt_rel k R v)) (lt_le_level hK1 (r_lt_rel k R v))
      (le_trans (termSubstVec_le (le_trans (by norm_num) hK) k v hv
        (fun i hi => termSubst_le hK le_self_add hw' _ (hv.2 i hi)))
        (tw_child (v_lt_rel k R v))))
  · intro k R v hR hv c ℓ n w hw hwb hwv
    have hw' : ∀ z, w.[z] ≤ Exp.exp c := by
      intro z
      by_cases hz : z < ℓ
      · exact hwb z hz
      · rw [nth_lt_len (by rw [← hw.isUTerm.lh]; exact not_lt.mp hz)]
        exact Arithmetic.zero_le _
    rw [substs_nrel hR hv]
    have hK : (10 : V) ≤ c + 12 := le_trans (by norm_num) le_add_self
    have hn : 1 ≤ ^nrel k R v := one_le_of_lt (arity_lt_nrel k R v)
    have he := four_le_level' (le_trans (by norm_num) hK) hn
    have hK1 : (1 : V) ≤ c + 12 := le_trans (by norm_num) hK
    simp only [qqNRel]
    exact stage_tw hK (tuple4_le he (tag_le (by norm_num) he)
      (lt_le_level hK1 (arity_lt_nrel k R v)) (lt_le_level hK1 (r_lt_nrel k R v))
      (le_trans (termSubstVec_le (le_trans (by norm_num) hK) k v hv
        (fun i hi => termSubst_le hK le_self_add hw' _ (hv.2 i hi)))
        (tw_child (v_lt_nrel k R v))))
  · intro c ℓ n w _ _ _
    rw [substs_verum]
    exact self_le_tw (le_trans (by norm_num) le_add_self) _
  · intro c ℓ n w _ _ _
    rw [substs_falsum]
    exact self_le_tw (le_trans (by norm_num) le_add_self) _
  · intro p q hp hq ihp ihq c ℓ n w hw hwb hwv
    rw [substs_and hp hq]
    have hK : (10 : V) ≤ c + 12 := le_trans (by norm_num) le_add_self
    have hn : 1 ≤ p ^⋏ q := one_le_of_lt (lt_K!_left p q)
    have he := four_le_level' (le_trans (by norm_num) hK) hn
    simp only [qqAnd]
    exact stage_tw hK (tuple3_le he (tag_le (by norm_num) he)
      (le_trans (ihp c ℓ n w hw hwb hwv) (tw_child (lt_K!_left p q)))
      (le_trans (ihq c ℓ n w hw hwb hwv) (tw_child (lt_K!_right p q))))
  · intro p q hp hq ihp ihq c ℓ n w hw hwb hwv
    rw [substs_or hp hq]
    have hK : (10 : V) ≤ c + 12 := le_trans (by norm_num) le_add_self
    have hn : 1 ≤ p ^⋎ q := one_le_of_lt (lt_or_left p q)
    have he := four_le_level' (le_trans (by norm_num) hK) hn
    simp only [qqOr]
    exact stage_tw hK (tuple3_le he (tag_le (by norm_num) he)
      (le_trans (ihp c ℓ n w hw hwb hwv) (tw_child (lt_or_left p q)))
      (le_trans (ihq c ℓ n w hw hwb hwv) (tw_child (lt_or_right p q))))
  · intro p hp ih c ℓ n w hw hwb hwv
    rw [substs_all hp]
    have hq := hw.qVec
    have hlen : len w = ℓ := hw.isUTerm.lh.symm
    have hqb : ∀ i < ℓ + 1, (qVec L w).[i] ≤ Exp.exp (c + 2) := by
      intro i hi
      rcases zero_or_succ i with rfl | ⟨j, rfl⟩
      · simp only [qVec, nth_adjoin_zero]
        exact le_trans (by simp [qqBvar, pair]) (one_le_exp _)
      · have hj : j < ℓ := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [hlen, nth_termBShiftVec hw.isUTerm hj]
        refine le_trans (bShift_var_le (hwv j hj)) ?_
        rw [exp_add, exp_two, mul_comm]
        exact mul_le_mul_of_nonneg_right (hwb j hj) (Arithmetic.zero_le _)
    have hqv : ∀ i < ℓ + 1, IsVarTerm (qVec L w).[i] := by
      intro i hi
      rcases zero_or_succ i with rfl | ⟨j, rfl⟩
      · simp only [qVec, nth_adjoin_zero]
        exact isVarTerm_bvar 0
      · have hj : j < ℓ := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [hlen, nth_termBShiftVec hw.isUTerm hj]
        exact bShift_isVar (hwv j hj)
    have hX := ih (c + 2) (ℓ + 1) (n + 1) (qVec L w) hq hqb hqv
    rw [show c + 2 + 12 = c + 14 by ring] at hX
    simp only [qqAll]
    exact quant_node_le (by norm_num) (two_mul_le_all p) hX
  · intro p hp ih c ℓ n w hw hwb hwv
    rw [substs_ex hp]
    have hq := hw.qVec
    have hlen : len w = ℓ := hw.isUTerm.lh.symm
    have hqb : ∀ i < ℓ + 1, (qVec L w).[i] ≤ Exp.exp (c + 2) := by
      intro i hi
      rcases zero_or_succ i with rfl | ⟨j, rfl⟩
      · simp only [qVec, nth_adjoin_zero]
        exact le_trans (by simp [qqBvar, pair]) (one_le_exp _)
      · have hj : j < ℓ := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [hlen, nth_termBShiftVec hw.isUTerm hj]
        refine le_trans (bShift_var_le (hwv j hj)) ?_
        rw [exp_add, exp_two, mul_comm]
        exact mul_le_mul_of_nonneg_right (hwb j hj) (Arithmetic.zero_le _)
    have hqv : ∀ i < ℓ + 1, IsVarTerm (qVec L w).[i] := by
      intro i hi
      rcases zero_or_succ i with rfl | ⟨j, rfl⟩
      · simp only [qVec, nth_adjoin_zero]
        exact isVarTerm_bvar 0
      · have hj : j < ℓ := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [hlen, nth_termBShiftVec hw.isUTerm hj]
        exact bShift_isVar (hwv j hj)
    have hX := ih (c + 2) (ℓ + 1) (n + 1) (qVec L w) hq hqb hqv
    rw [show c + 2 + 12 = c + 14 by ring] at hX
    simp only [qqExs]
    exact quant_node_le (by norm_num) (two_mul_le_exs p) hX

end Formulas

end LeanProofs.BoundedPAConsistency.SubstBound
