import IPRADerivations.Foundations.MasterCertificate
import IPRADerivations.Core.SumOrder
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.BoundedSums

/-!
# Finite capped coordinate demands

Packet: `foundations/fiber_ipra_2026-11-16`, Theorem `thm:demand-closure`.

Coordinates are read from actual primitive-recursive sequence codes. The
dimension is an object-language natural number. Coordinate order is represented
by a bounded product bit, so the induction invariants remain quantifier free.
The potential is the actual sum of the decoded coordinates.

`iterate F k r x` is the primitive-recursive update orbit from the actual
length-`r` zero sequence. `mapsInto` and `monotoneOn` quantify over encoded
vectors, with monotonicity required only when both vectors satisfy the caps.
Thus the operator respects coordinate-equivalent representatives. Equality
in the finite product is `coordinatesEQ`, equality at every index below `r`;
the proof derives it from the two coordinate orders.

`demand_closure` proves cappedness, stabilization at `K = rank r caps`,
prefixedness, and leastness. `demand_closure_closed` is the universally closed
object-theory source sentence. The dimension and all caps may be zero. No
rank-increase or stabilization property is assumed: these are derived from
the actual coordinate sums and the actual coordinatewise-maximum code.
-/

namespace LeanProofs.IPRA.Foundations.DemandClosure

open_ipra exports
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry sequence_decode entry_congr)
open LeanProofs.IPRA.Foundations.BoundedReflection

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Body of the finite product testing coordinatewise order. -/
def orderBody : PTm 2 :=
  monus one (monus (entry (fstT (var 1)) (var 0)) (entry (sndT (var 1)) (var 0)))

/-- A quantifier-free encoding of `∀ i < r, a[i] ≤ b[i]`. -/
def ordered (r a b : PTm n) : Fm PTm n := allB orderBody r (pairT a b) ≐ one

/-- The corresponding formula with its coordinate explicitly quantified. -/
def coordinatesLE (r a b : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift r) ⟶
    le (entry (Syn.shift a) (var 0)) (entry (Syn.shift b) (var 0)))

@[simp] theorem subst_ordered {m : ℕ} (σ : Fin n → PTm m) (r a b : PTm n) :
    (ordered r a b).subst σ = ordered (Syn.subst σ r) (Syn.subst σ a) (Syn.subst σ b) := by
  ipra_ind_simp [ordered, allB, subst_ap2, subst_pairT]

theorem ordered_QF (r a b : PTm n) : (ordered r a b).QF := trivial

private theorem orderBody_at (i a b : PTm n) :
    Γ ⊢[PRAAx] inst2 orderBody i (pairT a b) ≐
      monus one (monus (entry a i) (entry b i)) := by
  ipra_ind_simp [inst2, orderBody, MasterCertificate.subst_entry, subst_fstT, subst_sndT, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact congrMonus (.eqRefl _) (congrMonus
    (entry_congr (fst_pair _ _) (.eqRefl _))
    (entry_congr (snd_pair _ _) (.eqRefl _)))

/-- Extract any in-range coordinate inequality from the finite order bit. -/
theorem ordered_at {r a b i : PTm n} (h : Γ ⊢[PRAAx] ordered r a b)
    (hi : Γ ⊢[PRAAx] lt i r) : Γ ⊢[PRAAx] le (entry a i) (entry b i) := by
  have hne := all_elim orderBody h hi
  apply zero_of_compl_ne
  exact .impI (.impE hne.wk ((orderBody_at _ _ _).eqTrans Prf.hyp0))

theorem ordered_reflect {r a b : PTm n} (h : Γ ⊢[PRAAx] ordered r a b) :
    Γ ⊢[PRAAx] coordinatesLE r a b := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] ordered (Syn.shift r) (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift, subst_ordered, Syn.shift] using h.shift
  exact ordered_at hs.wk Prf.hyp0

/-- Establish the order bit by proving the coordinate inequalities. -/
theorem ordered_intro {r a b : PTm n} (h : Γ ⊢[PRAAx] coordinatesLE r a b) :
    Γ ⊢[PRAAx] ordered r a b := by
  apply all_intro orderBody
  refine .allI (.impI (.impI ?_))
  let Δ := (inst2 orderBody (var 0) (Syn.shift (pairT a b)) ≐ zero) ::
    lt (var 0) (Syn.shift r) :: Γ.map Fm.shift
  have hle : Δ ⊢[PRAAx] le (entry (Syn.shift a) (var 0)) (entry (Syn.shift b) (var 0)) :=
    Prf.impE h.allOpen.wk.wk Prf.hyp1
  have eqOne := (orderBody_at (Γ := Δ) (var 0) (Syn.shift a) (Syn.shift b)).eqTrans
    ((congrMonus (.eqRefl _) hle).eqTrans (monus_zero _))
  have zero : Δ ⊢[PRAAx] inst2 orderBody (var 0) (pairT (Syn.shift a) (Syn.shift b)) ≐ zero := by
    simpa only [Δ, Syn.shift, subst_pairT] using (Prf.hyp0 : Δ ⊢[PRAAx] _)
  exact one_ne_zero _ (eqOne.eqSymm.eqTrans zero)

theorem ordered_refl (r a : PTm n) : Γ ⊢[PRAAx] ordered r a a :=
  ordered_intro (.allI (.impI (le_refl _)))

theorem ordered_trans {r a b c : PTm n} (hab : Γ ⊢[PRAAx] ordered r a b)
    (hbc : Γ ⊢[PRAAx] ordered r b c) : Γ ⊢[PRAAx] ordered r a c := by
  apply ordered_intro
  exact .allI (.impI (le_trans (Prf.impE (ordered_reflect hab).allOpen.wk Prf.hyp0)
    (Prf.impE (ordered_reflect hbc).allOpen.wk Prf.hyp0)))

/-- The summand reads the indexed coordinate of its sequence-code parameter. -/
def coordinateBody : PTm 2 := entry (var 1) (var 0)

@[simp] theorem coordinateBody_at (i a : PTm n) : inst2 coordinateBody i a = entry a i := by
  simp only [coordinateBody, inst2, MasterCertificate.subst_entry, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The finite coordinate-sum potential. -/
def rank (r a : PTm n) : PTm n := ap2 (sumF coordinateBody) r a

@[simp] theorem subst_rank {m : ℕ} (σ : Fin n → PTm m) (r a : PTm n) :
    Syn.subst σ (rank r a) = rank (Syn.subst σ r) (Syn.subst σ a) := subst_ap2 _ _ _ _

/-- Bounded coordinatewise order implies monotonicity of the actual sum rank. -/
theorem rank_mono {r a b : PTm n} (h : Γ ⊢[PRAAx] ordered r a b) :
    Γ ⊢[PRAAx] le (rank r a) (rank r b) := by
  apply sum_le_params coordinateBody coordinateBody
  simpa only [coordinatesLE, coordinateBody_at] using ordered_reflect h

private def leftBody : PTm 2 := entry (fstT (var 1)) (var 0)
private def rightBody : PTm 2 := entry (sndT (var 1)) (var 0)
private def gapBody : PTm 2 := monus rightBody leftBody

private theorem leftBody_at (i a b : PTm n) :
    Γ ⊢[PRAAx] inst2 leftBody i (pairT a b) ≐ entry a i := by
  simp only [leftBody, inst2, MasterCertificate.subst_entry, subst_fstT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact entry_congr (fst_pair _ _) (.eqRefl _)

private theorem rightBody_at (i a b : PTm n) :
    Γ ⊢[PRAAx] inst2 rightBody i (pairT a b) ≐ entry b i := by
  simp only [rightBody, inst2, MasterCertificate.subst_entry, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact entry_congr (snd_pair _ _) (.eqRefl _)

private theorem gapBody_at (i a b : PTm n) :
    Γ ⊢[PRAAx] inst2 gapBody i (pairT a b) ≐ monus (entry b i) (entry a i) := by
  simp only [gapBody, inst2, PTm.subst_monus]
  exact congrMonus (rightBody_at _ _ _) (leftBody_at _ _ _)

private theorem left_sum (r a b : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF leftBody) r (pairT a b) ≐ rank r a := by
  apply sum_congr_bounded leftBody coordinateBody
  refine .allI (.impI ?_)
  simpa only [coordinateBody_at, Syn.shift, subst_pairT] using
    (leftBody_at (Γ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift)
      (var 0) (Syn.shift a) (Syn.shift b))

private theorem right_sum (r a b : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF rightBody) r (pairT a b) ≐ rank r b := by
  apply sum_congr_bounded rightBody coordinateBody
  refine .allI (.impI ?_)
  simpa only [coordinateBody_at, Syn.shift, subst_pairT] using
    (rightBody_at (Γ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift)
      (var 0) (Syn.shift a) (Syn.shift b))

/-- The sum of all nonnegative coordinate increments from `a` to `b`. -/
def gap (r a b : PTm n) : PTm n := ap2 (sumF gapBody) r (pairT a b)

@[simp] theorem subst_gap {m : ℕ} (σ : Fin n → PTm m) (r a b : PTm n) :
    Syn.subst σ (gap r a b) = gap (Syn.subst σ r) (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [gap, subst_ap2, subst_pairT]

/-- Under coordinate order, the rank difference is exactly the sum of increments. -/
theorem rank_gap {r a b : PTm n} (h : Γ ⊢[PRAAx] ordered r a b) :
    Γ ⊢[PRAAx] rank r b ≐ rank r a + gap r a b := by
  have sums : Γ ⊢[PRAAx] ap2 (sumF rightBody) r (pairT a b) ≐
      ap2 (sumF (addBody leftBody gapBody)) r (pairT a b) := by
    apply sum_congr_bounded rightBody (addBody leftBody gapBody)
    refine .allI (.impI ?_)
    simp only [Syn.shift, subst_pairT, inst2_addBody]
    have hle := Prf.impE (ordered_reflect h).allOpen.wk Prf.hyp0
    exact (rightBody_at _ _ _).eqTrans ((eq_add_of_le hle).eqTrans
      (congrAdd (leftBody_at _ _ _).eqSymm (gapBody_at _ _ _).eqSymm))
  exact (right_sum r a b).eqSymm.eqTrans (sums.eqTrans
    ((sum_add leftBody gapBody r (pairT a b)).eqTrans
      (congrAdd (left_sum r a b) (.eqRefl _))))

private alias one_le_succ := Common.one_le_succ

/-- A strict increase in one coordinate gives a positive total increment. -/
theorem gap_positive {r a b i : PTm n} (hi : Γ ⊢[PRAAx] lt i r)
    (hlt : Γ ⊢[PRAAx] lt (entry a i) (entry b i)) :
    Γ ⊢[PRAAx] le one (gap r a b) := by
  have pos : Γ ⊢[PRAAx] le one (monus (entry b i) (entry a i)) :=
    Order.zero_lt_of_eq_succ (AnalyticNumberTheory.Totatives.monus_succ_of_lt hlt)
  exact le_trans (le_congr (.eqRefl _) (gapBody_at i a b).eqSymm pos) (term_le_sum gapBody hi)

/-- A strict increase in one in-range coordinate strictly increases the finite rank. -/
theorem rank_strict {r a b i : PTm n} (h : Γ ⊢[PRAAx] ordered r a b)
    (hi : Γ ⊢[PRAAx] lt i r) (hlt : Γ ⊢[PRAAx] lt (entry a i) (entry b i)) :
    Γ ⊢[PRAAx] lt (rank r a) (rank r b) :=
  le_congr (succ_eq_add_one _).eqSymm (rank_gap h).eqSymm
    (add_le_add₂ (le_refl _) (gap_positive hi hlt))

/-- Equal ranks in an increasing pair force equality of each in-range coordinate. -/
theorem rank_flat_at {r a b i : PTm n} (h : Γ ⊢[PRAAx] ordered r a b)
    (hrank : Γ ⊢[PRAAx] rank r a ≐ rank r b) (hi : Γ ⊢[PRAAx] lt i r) :
    Γ ⊢[PRAAx] entry a i ≐ entry b i := by
  have gapZero : Γ ⊢[PRAAx] gap r a b ≐ zero :=
    add_left_cancel ((rank_gap h).eqSymm.eqTrans (hrank.eqSymm.eqTrans (add_zero _).eqSymm))
  have gapLe : Γ ⊢[PRAAx] le (monus (entry b i) (entry a i)) zero :=
    le_congr (gapBody_at i a b) gapZero (term_le_sum gapBody hi)
  have reverse : Γ ⊢[PRAAx] le (entry b i) (entry a i) := (monus_zero _).eqSymm.eqTrans gapLe
  exact le_antisymm (ordered_at h hi) reverse

/-- The rank has no flat steps except coordinatewise equality. -/
theorem rank_flat {r a b : PTm n} (h : Γ ⊢[PRAAx] ordered r a b)
    (hrank : Γ ⊢[PRAAx] rank r a ≐ rank r b) :
    Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift r) ⟶
      entry (Syn.shift a) (var 0) ≐ entry (Syn.shift b) (var 0)) := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] ordered (Syn.shift r) (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift, subst_ordered, Syn.shift] using h.shift
  have hrs : Γ.map Fm.shift ⊢[PRAAx] rank (Syn.shift r) (Syn.shift a) ≐ rank (Syn.shift r) (Syn.shift b) := by
    simpa only [Fm.shift, Fm.subst_eq, subst_rank, Syn.shift] using hrank.shift
  exact rank_flat_at hs.wk hrs.wk Prf.hyp0

/-- The natural-number maximum, defined using truncated subtraction. -/
def maximum (a b : PTm n) : PTm n := a + monus b a

@[simp] theorem subst_maximum {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (maximum a b) = maximum (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [maximum, PTm.subst_add, PTm.subst_monus]

theorem maximum_left (a b : PTm n) : Γ ⊢[PRAAx] le a (maximum a b) := le_add_right _ _

theorem maximum_right (a b : PTm n) : Γ ⊢[PRAAx] le b (maximum a b) := by
  refine .orE (le_total a b) ?_ ?_
  · exact le_congr (.eqRefl _) (eq_add_of_le Prf.hyp0) (le_refl _)
  · exact le_trans Prf.hyp0 (le_add_right _ _)

theorem maximum_le {a b c : PTm n} (ha : Γ ⊢[PRAAx] le a c) (hb : Γ ⊢[PRAAx] le b c) :
    Γ ⊢[PRAAx] le (maximum a b) c := by
  refine .orE (le_total a b) ?_ ?_
  · exact le_congr (eq_add_of_le Prf.hyp0) (.eqRefl _) hb.wk
  · exact le_congr ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _)).eqSymm (.eqRefl _) ha.wk

private def joinBody : PTm 2 := maximum leftBody rightBody

private theorem joinBody_at (i a b : PTm n) :
    Γ ⊢[PRAAx] inst2 joinBody i (pairT a b) ≐ maximum (entry a i) (entry b i) := by
  simp only [joinBody, maximum, inst2, PTm.subst_add, PTm.subst_monus]
  exact congrAdd (leftBody_at _ _ _) (congrMonus (rightBody_at _ _ _) (leftBody_at _ _ _))

/-- Construct an actual sequence code for the coordinatewise maximum. -/
def join (r a b : PTm n) : PTm n := sequence joinBody r (pairT a b)

@[simp] theorem subst_join {m : ℕ} (σ : Fin n → PTm m) (r a b : PTm n) :
    Syn.subst σ (join r a b) = join (Syn.subst σ r) (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [join, MasterCertificate.subst_sequence, subst_pairT]

/-- In-range decoding of the constructed coordinatewise maximum. -/
theorem join_at {r a b i : PTm n} (hi : Γ ⊢[PRAAx] lt i r) :
    Γ ⊢[PRAAx] entry (join r a b) i ≐ maximum (entry a i) (entry b i) :=
  (sequence_decode joinBody hi).eqTrans (joinBody_at _ _ _)

theorem join_left (r a b : PTm n) : Γ ⊢[PRAAx] ordered r a (join r a b) := by
  apply ordered_intro
  refine .allI (.impI ?_)
  simpa only [Syn.shift, subst_join] using
    (le_congr (.eqRefl _) (join_at (Γ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift)
      (a := Syn.shift a) (b := Syn.shift b) Prf.hyp0).eqSymm (maximum_left _ _))

theorem join_right (r a b : PTm n) : Γ ⊢[PRAAx] ordered r b (join r a b) := by
  apply ordered_intro
  refine .allI (.impI ?_)
  simpa only [Syn.shift, subst_join] using
    (le_congr (.eqRefl _) (join_at (Γ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift)
      (a := Syn.shift a) (b := Syn.shift b) Prf.hyp0).eqSymm (maximum_right _ _))

/-- Coordinate caps are preserved by the actual join code. -/
theorem join_le {r a b c : PTm n} (ha : Γ ⊢[PRAAx] ordered r a c)
    (hb : Γ ⊢[PRAAx] ordered r b c) : Γ ⊢[PRAAx] ordered r (join r a b) c := by
  apply ordered_intro
  refine .allI (.impI ?_)
  have hle := maximum_le (Prf.impE (ordered_reflect ha).allOpen.wk Prf.hyp0)
    (Prf.impE (ordered_reflect hb).allOpen.wk Prf.hyp0)
  simpa only [Syn.shift, subst_join] using
    (le_congr (join_at (Γ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift)
      (a := Syn.shift a) (b := Syn.shift b) Prf.hyp0).eqSymm (.eqRefl _) hle)

/-- The join operation is monotone in both vector inputs. -/
theorem join_mono {r a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] ordered r a a')
    (hb : Γ ⊢[PRAAx] ordered r b b') :
    Γ ⊢[PRAAx] ordered r (join r a b) (join r a' b') :=
  join_le (ordered_trans ha (join_left _ _ _)) (ordered_trans hb (join_right _ _ _))

/-- Any demanded coordinate strictly above its old value strictly increases the rank. -/
theorem join_rank_strict {r a b i : PTm n} (hi : Γ ⊢[PRAAx] lt i r)
    (hlt : Γ ⊢[PRAAx] lt (entry a i) (entry b i)) :
    Γ ⊢[PRAAx] lt (rank r a) (rank r (join r a b)) :=
  rank_strict (join_left _ _ _) hi (lt_of_lt_of_le hlt (ordered_at (join_right _ _ _) hi))

/-- A flat join rank already certifies that all demands are below the old vector. -/
theorem join_rank_flat {r a b : PTm n}
    (hrank : Γ ⊢[PRAAx] rank r a ≐ rank r (join r a b)) :
    Γ ⊢[PRAAx] ordered r b a := by
  apply ordered_intro
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift
  have hrs : Δ ⊢[PRAAx] rank (Syn.shift r) (Syn.shift a) ≐
      rank (Syn.shift r) (join (Syn.shift r) (Syn.shift a) (Syn.shift b)) := by
    simpa only [Δ, Fm.shift, Fm.subst_eq, subst_rank, subst_join, Syn.shift] using hrank.shift.wk
  exact le_congr (.eqRefl _) (rank_flat_at (join_left _ _ _) hrs Prf.hyp0).eqSymm
    (ordered_at (join_right _ _ _) Prf.hyp0)

/-- Universally closed rank monotonicity at an arbitrary finite dimension. -/
theorem rank_mono_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ordered (var 0) (var 1) (var 2) ⟶
      le (rank (var 0) (var 1)) (rank (var 0) (var 2))) :=
  closeUniv 3 (.impI (rank_mono Prf.hyp0))

/-- Universally closed strict-rank theorem with the increased coordinate internal. -/
theorem rank_strict_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ordered (var 0) (var 1) (var 2) ⟶ lt (var 3) (var 0) ⟶
      lt (entry (var 1) (var 3)) (entry (var 2) (var 3)) ⟶
      lt (rank (var 0) (var 1)) (rank (var 0) (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (rank_strict Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

/-- Universally closed flat-rank test for a prefixed point of the demand join. -/
theorem join_rank_flat_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rank (var 0) (var 1) ≐ rank (var 0) (join (var 0) (var 1) (var 2)) ⟶
      ordered (var 0) (var 2) (var 1)) :=
  closeUniv 3 (.impI (join_rank_flat Prf.hyp0))

private theorem ordered_congr {r r' a a' b b' : PTm n}
    (hr : Γ ⊢[PRAAx] r ≐ r') (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b')
    (h : Γ ⊢[PRAAx] ordered r a b) : Γ ⊢[PRAAx] ordered r' a' b' := by
  have hs : Γ ⊢[PRAAx] (ordered (var 0) (var 1) (var 2) : Fm PTm 3).subst ![r, a, b] := by
    simpa only [subst_ordered, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h
  have ht := Prf.eqSubst (ordered (var 0) (var 1) (var 2) : Fm PTm 3)
    ![r, a, b] ![r', a', b'] (fun j => by fin_cases j <;> assumption) hs
  simpa only [subst_ordered, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using ht

private theorem join_congr {r r' a a' b b' : PTm n}
    (hr : Γ ⊢[PRAAx] r ≐ r') (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] join r a b ≐ join r' a' b' := by
  have h := Prf.eqCongr (join (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![r, a, b]) (σ' := ![r', a', b']) (fun j => by fin_cases j <;> assumption)
  simpa only [subst_join, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

/-- An actual sequence code with `r` zero coordinates. -/
def zeros (r : PTm n) : PTm n := sequence (zero : PTm 2) r zero

@[simp] theorem subst_zeros {m : ℕ} (σ : Fin n → PTm m) (r : PTm n) :
    Syn.subst σ (zeros r) = zeros (Syn.subst σ r) := by
  simp only [zeros, MasterCertificate.subst_sequence, ConciseIPRA.PTm.subst_zero]

theorem zeros_at {r i : PTm n} (hi : Γ ⊢[PRAAx] lt i r) :
    Γ ⊢[PRAAx] entry (zeros r) i ≐ zero := by
  simpa only [zeros, inst2, ConciseIPRA.PTm.subst_zero] using sequence_decode (zero : PTm 2) (x := zero) hi

theorem zeros_le (r a : PTm n) : Γ ⊢[PRAAx] ordered r (zeros r) a := by
  apply ordered_intro
  refine .allI (.impI ?_)
  simpa only [Syn.shift, subst_zeros] using
    (le_congr (zeros_at (Γ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift) Prf.hyp0).eqSymm
      (.eqRefl _) (zero_le (entry (Syn.shift a) (var 0))))

private theorem zeros_congr {r r' : PTm n} (hr : Γ ⊢[PRAAx] r ≐ r') :
    Γ ⊢[PRAAx] zeros r ≐ zeros r' := by
  ipra_congr (zeros (var 0) : PTm 1) with [hr]

/-- One increasing demand update. The operator has arguments `(vector, data)`. -/
def next (F : PTm 2) (r a x : PTm n) : PTm n := join r a (inst2 F a x)

@[simp] theorem subst_next {m : ℕ} (σ : Fin n → PTm m) (F : PTm 2) (r a x : PTm n) :
    Syn.subst σ (next F r a x) = next F (Syn.subst σ r) (Syn.subst σ a) (Syn.subst σ x) := by
  simp only [next, subst_join, subst_inst2]

private def iterStep (F : PTm 2) : PTm 3 := next F (fstT (var 2)) (var 1) (sndT (var 2))
private def iterF (F : PTm 2) : PR 2 := rec2 (zeros (fstT (var 0))) (iterStep F)

/-- The actual primitive-recursive orbit from zero, with dimension and data packed. -/
def iterate (F : PTm 2) (k r x : PTm n) : PTm n := ap2 (iterF F) k (pairT r x)

@[simp] theorem subst_iterate {m : ℕ} (σ : Fin n → PTm m) (F : PTm 2) (k r x : PTm n) :
    Syn.subst σ (iterate F k r x) = iterate F (Syn.subst σ k) (Syn.subst σ r) (Syn.subst σ x) := by
  simp only [iterate, subst_ap2, subst_pairT]

theorem iterate_zero (F : PTm 2) (r x : PTm n) :
    Γ ⊢[PRAAx] iterate F zero r x ≐ zeros r := by
  have h := rec2_zero (Γ := Γ) (zeros (fstT (var 0))) (iterStep F) (pairT r x)
  simp only [subst_zeros, subst_fstT, Syn.subst_var, Matrix.cons_val_zero] at h
  exact h.eqTrans (zeros_congr (fst_pair _ _))

private theorem iter_step_at (F : PTm 2) (k old p : PTm n) :
    Syn.subst ![k, old, p] (iterStep F) = next F (fstT p) old (sndT p) := by
  simp only [iterStep, subst_next, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem iterate_succ (F : PTm 2) (k r x : PTm n) :
    Γ ⊢[PRAAx] iterate F (succ k) r x ≐ next F r (iterate F k r x) x := by
  have h := rec2_succ (Γ := Γ) (zeros (fstT (var 0))) (iterStep F) k (pairT r x)
  rw [iter_step_at] at h
  exact h.eqTrans (join_congr (fst_pair _ _) (.eqRefl _)
    (congrInst2 F (.eqRefl _) (snd_pair _ _)))

/-- The operator maps the capped finite product into itself. -/
def mapsInto (F : PTm 2) (r caps x : PTm n) : Fm PTm n :=
  .all (ordered (Syn.shift r) (var 0) (Syn.shift caps) ⟶
    ordered (Syn.shift r) (inst2 F (var 0) (Syn.shift x)) (Syn.shift caps))

/-- The operator is monotone on the capped product, with no condition outside it. -/
def monotoneOn (F : PTm 2) (r caps x : PTm n) : Fm PTm n :=
  .all (.all (
    ordered (Syn.shift (Syn.shift r)) (var 1) (Syn.shift (Syn.shift caps)) ⟶
    ordered (Syn.shift (Syn.shift r)) (var 0) (Syn.shift (Syn.shift caps)) ⟶
    ordered (Syn.shift (Syn.shift r)) (var 1) (var 0) ⟶
    ordered (Syn.shift (Syn.shift r))
      (inst2 F (var 1) (Syn.shift (Syn.shift x)))
      (inst2 F (var 0) (Syn.shift (Syn.shift x)))))

@[simp] theorem subst_mapsInto {m : ℕ} (σ : Fin n → PTm m) (F : PTm 2) (r caps x : PTm n) :
    (mapsInto F r caps x).subst σ = mapsInto F (Syn.subst σ r) (Syn.subst σ caps) (Syn.subst σ x) := by
  simp only [mapsInto, Fm.subst_all, Fm.subst_imp, subst_ordered, subst_inst2,
    Syn.subst_var, Syn.up_zero, BoundedFormulas.subst_up_shift']

@[simp] theorem subst_monotoneOn {m : ℕ} (σ : Fin n → PTm m) (F : PTm 2) (r caps x : PTm n) :
    (monotoneOn F r caps x).subst σ =
      monotoneOn F (Syn.subst σ r) (Syn.subst σ caps) (Syn.subst σ x) := by
  simp only [monotoneOn, Fm.subst_all, Fm.subst_imp, subst_ordered, subst_inst2, Syn.subst_var, Syn.up_zero, Syn.up_one,
    Syn.shift_var, Fin.succ_zero_eq_one, BoundedFormulas.subst_up_shift']

theorem mapsInto_at {F : PTm 2} {r caps x a : PTm n}
    (hF : Γ ⊢[PRAAx] mapsInto F r caps x) (ha : Γ ⊢[PRAAx] ordered r a caps) :
    Γ ⊢[PRAAx] ordered r (inst2 F a x) caps := by
  have h := Prf.allE a hF
  simp only [Fm.subst_imp, subst_ordered, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h
  exact Prf.impE h ha

theorem monotoneOn_at {F : PTm 2} {r caps x a b : PTm n}
    (hF : Γ ⊢[PRAAx] monotoneOn F r caps x)
    (ha : Γ ⊢[PRAAx] ordered r a caps) (hb : Γ ⊢[PRAAx] ordered r b caps)
    (hab : Γ ⊢[PRAAx] ordered r a b) :
    Γ ⊢[PRAAx] ordered r (inst2 F a x) (inst2 F b x) := by
  have h := Prf.allE b (Prf.allE a hF)
  simp only [Fm.subst_imp, subst_ordered, subst_inst2, Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.inst_zero,
    Syn.subst_inst_shift, BoundedFormulas.subst_up_shift'] at h
  exact Prf.impE (Prf.impE (Prf.impE h ha) hb) hab

/-- The increasing orbit remains in the capped finite product at every stage. -/
theorem iterate_bounded {F : PTm 2} {r caps x : PTm n}
    (hF : Γ ⊢[PRAAx] mapsInto F r caps x) :
    Γ ⊢[PRAAx] .all (ordered (Syn.shift r)
      (iterate F (var 0) (Syn.shift r) (Syn.shift x)) (Syn.shift caps)) := by
  ipra_qfind (trivial) [subst_ordered, subst_iterate]
  · exact ordered_congr (.eqRefl _) (iterate_zero F r x).eqSymm (.eqRefl _) (zeros_le r caps)
  · let Δ := ordered (Syn.shift r) (iterate F (var 0) (Syn.shift r) (Syn.shift x))
      (Syn.shift caps) :: Γ.map Fm.shift
    have hf : Δ ⊢[PRAAx] mapsInto F (Syn.shift r) (Syn.shift caps) (Syn.shift x) := by
      simpa only [Δ, Fm.shift, subst_mapsInto, Syn.shift] using hF.shift.wk
    have hi : Δ ⊢[PRAAx] ordered (Syn.shift r) (iterate F (var 0) (Syn.shift r) (Syn.shift x))
      (Syn.shift caps) := Prf.hyp0
    exact ordered_congr (.eqRefl _) (iterate_succ F _ _ _).eqSymm (.eqRefl _)
      (join_le hi (mapsInto_at hf hi))

/-- Each stage is below its successor, independently of monotonicity of `F`. -/
theorem iterate_increasing (F : PTm 2) (k r x : PTm n) :
    Γ ⊢[PRAAx] ordered r (iterate F k r x) (iterate F (succ k) r x) :=
  ordered_congr (.eqRefl _) (.eqRefl _) (iterate_succ F k r x).eqSymm (join_left _ _ _)

theorem iterate_bounded_at {F : PTm 2} {r caps x : PTm n}
    (hF : Γ ⊢[PRAAx] mapsInto F r caps x) (k : PTm n) :
    Γ ⊢[PRAAx] ordered r (iterate F k r x) caps := by
  have h := Prf.allE k (iterate_bounded hF)
  simpa only [subst_ordered, subst_iterate, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] using h

/-- A vector is a prefixed point when every new demand is already below it. -/
def prefixed (F : PTm 2) (r a x : PTm n) : Fm PTm n := ordered r (inst2 F a x) a

@[simp] theorem subst_prefixed {m : ℕ} (σ : Fin n → PTm m) (F : PTm 2) (r a x : PTm n) :
    (prefixed F r a x).subst σ = prefixed F (Syn.subst σ r) (Syn.subst σ a) (Syn.subst σ x) := by
  simp only [prefixed, subst_ordered, subst_inst2]

/-- Every orbit stage lies below every capped prefixed point. -/
theorem iterate_le_prefixed {F : PTm 2} {r caps x e : PTm n}
    (hMaps : Γ ⊢[PRAAx] mapsInto F r caps x) (hMono : Γ ⊢[PRAAx] monotoneOn F r caps x)
    (he : Γ ⊢[PRAAx] ordered r e caps) (hPref : Γ ⊢[PRAAx] prefixed F r e x) :
    Γ ⊢[PRAAx] .all (ordered (Syn.shift r)
      (iterate F (var 0) (Syn.shift r) (Syn.shift x)) (Syn.shift e)) := by
  ipra_qfind (trivial) [subst_ordered, subst_iterate]
  · exact ordered_congr (.eqRefl _) (iterate_zero F r x).eqSymm (.eqRefl _) (zeros_le r e)
  · let Δ := ordered (Syn.shift r) (iterate F (var 0) (Syn.shift r) (Syn.shift x))
      (Syn.shift e) :: Γ.map Fm.shift
    have hm : Δ ⊢[PRAAx] mapsInto F (Syn.shift r) (Syn.shift caps) (Syn.shift x) := by
      simpa only [Δ, Fm.shift, subst_mapsInto, Syn.shift] using hMaps.shift.wk
    have hn : Δ ⊢[PRAAx] monotoneOn F (Syn.shift r) (Syn.shift caps) (Syn.shift x) := by
      simpa only [Δ, Fm.shift, subst_monotoneOn, Syn.shift] using hMono.shift.wk
    have he' : Δ ⊢[PRAAx] ordered (Syn.shift r) (Syn.shift e) (Syn.shift caps) := by
      simpa only [Δ, Fm.shift, subst_ordered, Syn.shift] using he.shift.wk
    have hp : Δ ⊢[PRAAx] prefixed F (Syn.shift r) (Syn.shift e) (Syn.shift x) := by
      simpa only [Δ, Fm.shift, subst_prefixed, Syn.shift] using hPref.shift.wk
    have ih : Δ ⊢[PRAAx] ordered (Syn.shift r)
      (iterate F (var 0) (Syn.shift r) (Syn.shift x)) (Syn.shift e) := Prf.hyp0
    have hf := monotoneOn_at hn (iterate_bounded_at hm (var 0)) he' ih
    exact ordered_congr (.eqRefl _) (iterate_succ F _ _ _).eqSymm (.eqRefl _)
      (join_le ih (ordered_trans hf hp))

/-- The least-prefixed-point bound at an arbitrary, internally supplied stage. -/
theorem iterate_le_prefixed_at {F : PTm 2} {r caps x e : PTm n}
    (hMaps : Γ ⊢[PRAAx] mapsInto F r caps x) (hMono : Γ ⊢[PRAAx] monotoneOn F r caps x)
    (he : Γ ⊢[PRAAx] ordered r e caps) (hPref : Γ ⊢[PRAAx] prefixed F r e x) (k : PTm n) :
    Γ ⊢[PRAAx] ordered r (iterate F k r x) e := by
  have h := Prf.allE k (iterate_le_prefixed hMaps hMono he hPref)
  simpa only [subst_ordered, subst_iterate, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h

private theorem iterate_congr {F : PTm 2} {k l r x : PTm n} (hkl : Γ ⊢[PRAAx] k ≐ l) :
    Γ ⊢[PRAAx] iterate F k r x ≐ iterate F l r x := congrAp2 _ hkl (.eqRefl _)

/-- Any earlier orbit stage lies below any later one. -/
theorem iterate_ordered {F : PTm 2} {k l r x : PTm n} (hkl : Γ ⊢[PRAAx] le k l) :
    Γ ⊢[PRAAx] ordered r (iterate F k r x) (iterate F l r x) := by
  have hall : Γ ⊢[PRAAx] .all (le (Syn.shift k) (var 0) ⟶
      ordered (Syn.shift r) (iterate F (Syn.shift k) (Syn.shift r) (Syn.shift x))
        (iterate F (var 0) (Syn.shift r) (Syn.shift x))) := by
    ipra_qfind (⟨le_QF _ _, trivial⟩) [subst_le, subst_ordered, subst_iterate]
    · refine .impI ?_
      have kZero : (le k zero :: Γ) ⊢[PRAAx] k ≐ zero := (monus_zero _).eqSymm.eqTrans Prf.hyp0
      exact ordered_congr (.eqRefl _) (iterate_congr kZero).eqSymm (.eqRefl _) (ordered_refl _ _)
    · refine .impI ?_
      let Δ := le (Syn.shift k) (succ (var 0)) ::
        (le (Syn.shift k) (var 0) ⟶
          ordered (Syn.shift r) (iterate F (Syn.shift k) (Syn.shift r) (Syn.shift x))
            (iterate F (var 0) (Syn.shift r) (Syn.shift x))) :: Γ.map Fm.shift
      have hs : Δ ⊢[PRAAx] le (Syn.shift k) (succ (var 0)) := Prf.hyp0
      refine .orE (lt_or_eq_of_le hs) ?_ ?_
      · have hsmall : (lt (Syn.shift k) (succ (var 0)) :: Δ) ⊢[PRAAx] le (Syn.shift k) (var 0) :=
          Order.le_of_lt_succ Prf.hyp0
        exact ordered_trans (Prf.impE Prf.hyp1.wk hsmall) (iterate_increasing F _ _ _)
      · exact ordered_congr (.eqRefl _) (iterate_congr Prf.hyp0).eqSymm (.eqRefl _)
          (ordered_refl _ _)
  have h := Prf.allE l hall
  simp only [Fm.subst_imp, subst_le, subst_ordered, subst_iterate, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at h
  exact Prf.impE h hkl

/-- A prefixed point reached by the orbit remains prefixed at every later stage. -/
theorem prefixed_later {F : PTm 2} {r caps x k l : PTm n}
    (hMaps : Γ ⊢[PRAAx] mapsInto F r caps x) (hMono : Γ ⊢[PRAAx] monotoneOn F r caps x)
    (hkl : Γ ⊢[PRAAx] le k l) (hk : Γ ⊢[PRAAx] prefixed F r (iterate F k r x) x) :
    Γ ⊢[PRAAx] prefixed F r (iterate F l r x) x := by
  have hlow := iterate_bounded_at hMaps k
  have hhigh := iterate_bounded_at hMaps l
  have backwards := iterate_le_prefixed_at hMaps hMono hlow hk l
  exact ordered_trans (ordered_trans (monotoneOn_at hMono hhigh hlow backwards) hk)
    (iterate_ordered hkl)

/-- Each update either strictly raises the potential or has reached a prefixed point. -/
theorem rank_step_or_prefixed (F : PTm 2) (k r x : PTm n) :
    Γ ⊢[PRAAx] lt (rank r (iterate F k r x)) (rank r (iterate F (succ k) r x)) ⋎
      prefixed F r (iterate F k r x) x := by
  refine .orE (lt_or_eq_of_le (rank_mono (iterate_increasing F k r x))) (.orI₁ Prf.hyp0) ?_
  apply Prf.orI₂
  apply join_rank_flat
  exact Prf.hyp0.eqTrans (congrAp2 (sumF coordinateBody) (.eqRefl _) (iterate_succ F k r x))

/-- If stage `L` is not prefixed, every stage through `L+1` has rank at least its index. -/
theorem nonprefixed_growth {F : PTm 2} {r caps x L : PTm n}
    (hMaps : Γ ⊢[PRAAx] mapsInto F r caps x) (hMono : Γ ⊢[PRAAx] monotoneOn F r caps x)
    (hNot : Γ ⊢[PRAAx] neg (prefixed F r (iterate F L r x) x)) :
    Γ ⊢[PRAAx] .all (le (var 0) (succ (Syn.shift L)) ⟶
      le (var 0) (rank (Syn.shift r) (iterate F (var 0) (Syn.shift r) (Syn.shift x)))) := by
  have shiftBound : Syn.shift (succ L) = succ (Syn.shift L) := by simp [Syn.shift]
  rw [← shiftBound]
  refine qfIndAllUpTo (succ L) (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_rank, subst_iterate, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    exact zero_le _
  · simp only [subst_le, subst_rank, subst_iterate, Syn.subst_var, Syn.repl_zero, subst_repl_shift, shiftBound]
    refine .impI ?_
    let Δ := lt (var 0) (succ (Syn.shift L)) ::
      le (var 0) (rank (Syn.shift r) (iterate F (var 0) (Syn.shift r) (Syn.shift x))) :: Γ.map Fm.shift
    have hm : Δ ⊢[PRAAx] mapsInto F (Syn.shift r) (Syn.shift caps) (Syn.shift x) := by
      simpa only [Δ, Fm.shift, subst_mapsInto, Syn.shift] using hMaps.shift.wk.wk
    have hn : Δ ⊢[PRAAx] monotoneOn F (Syn.shift r) (Syn.shift caps) (Syn.shift x) := by
      simpa only [Δ, Fm.shift, subst_monotoneOn, Syn.shift] using hMono.shift.wk.wk
    have hno : Δ ⊢[PRAAx] neg
        (prefixed F (Syn.shift r) (iterate F (Syn.shift L) (Syn.shift r) (Syn.shift x)) (Syn.shift x)) := by
      simpa only [Δ, Fm.shift, subst_neg, subst_prefixed, subst_iterate, Syn.shift] using hNot.shift.wk.wk
    have hindex : Δ ⊢[PRAAx] le (var 0) (Syn.shift L) :=
      Order.le_of_lt_succ Prf.hyp0
    have ih : Δ ⊢[PRAAx] le (var 0) (rank (Syn.shift r) (iterate F (var 0) (Syn.shift r) (Syn.shift x))) :=
      Prf.hyp1
    refine .orE (rank_step_or_prefixed F (var 0) (Syn.shift r) (Syn.shift x)) ?_ ?_
    · exact le_trans (Order.succ_le_succ ih.wk) Prf.hyp0
    · exact .botE _ (.impE hno.wk (prefixed_later hm.wk hn.wk hindex.wk Prf.hyp0))

/-- Stabilization occurs by the sum of all coordinate caps. -/
theorem closure_prefixed {F : PTm 2} {r caps x : PTm n}
    (hMaps : Γ ⊢[PRAAx] mapsInto F r caps x) (hMono : Γ ⊢[PRAAx] monotoneOn F r caps x) :
    Γ ⊢[PRAAx] prefixed F r (iterate F (rank r caps) r x) x := by
  let K := rank r caps
  refine .orE (eq_or_ne
    (allB orderBody r (pairT (inst2 F (iterate F K r x) x) (iterate F K r x))) one) Prf.hyp0 ?_
  let Δ := neg (prefixed F r (iterate F K r x) x) :: Γ
  have growth := nonprefixed_growth (Γ := Δ) hMaps.wk hMono.wk Prf.hyp0
  have hg := Prf.allE (succ K) growth
  simp only [Fm.subst_imp, subst_le, subst_rank, subst_iterate, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ] at hg
  have lower : Δ ⊢[PRAAx] le (succ K) (rank r (iterate F (succ K) r x)) :=
    Prf.impE hg (le_refl _)
  have upper := rank_mono (iterate_bounded_at (Γ := Δ) hMaps.wk (succ K))
  exact not_succ_le_self K _ (le_trans lower upper)

/-- Equality in the finite product is equality at every in-range coordinate. -/
def coordinatesEQ (r a b : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift r) ⟶
    entry (Syn.shift a) (var 0) ≐ entry (Syn.shift b) (var 0))

/-- The sum-of-caps stage and its successor are the same finite vector. -/
theorem closure_stable {F : PTm 2} {r caps x : PTm n}
    (hMaps : Γ ⊢[PRAAx] mapsInto F r caps x) (hMono : Γ ⊢[PRAAx] monotoneOn F r caps x) :
    Γ ⊢[PRAAx] coordinatesEQ r (iterate F (rank r caps) r x)
      (iterate F (succ (rank r caps)) r x) := by
  have backward : Γ ⊢[PRAAx] ordered r (iterate F (succ (rank r caps)) r x)
      (iterate F (rank r caps) r x) :=
    ordered_congr (.eqRefl _) (iterate_succ F _ _ _).eqSymm (.eqRefl _)
      (join_le (ordered_refl _ _) (closure_prefixed hMaps hMono))
  have forward := iterate_increasing (Γ := Γ) F (rank r caps) r x
  refine .allI (.impI ?_)
  exact le_antisymm (Prf.impE (ordered_reflect forward).allOpen.wk Prf.hyp0)
    (Prf.impE (ordered_reflect backward).allOpen.wk Prf.hyp0)

/-- Cappedness, stabilization, prefixedness and leastness of the explicit orbit endpoint. -/
def closureConclusion (F : PTm 2) (r caps x : PTm n) : Fm PTm n :=
  ordered r (iterate F (rank r caps) r x) caps ⋏
  coordinatesEQ r (iterate F (rank r caps) r x) (iterate F (succ (rank r caps)) r x) ⋏
  prefixed F r (iterate F (rank r caps) r x) x ⋏
  .all (ordered (Syn.shift r) (var 0) (Syn.shift caps) ⟶
    prefixed F (Syn.shift r) (var 0) (Syn.shift x) ⟶
    ordered (Syn.shift r)
      (iterate F (rank (Syn.shift r) (Syn.shift caps)) (Syn.shift r) (Syn.shift x)) (var 0))

/-- The full finite demand-closure theorem, with all vector quantification internal. -/
theorem demand_closure {F : PTm 2} {r caps x : PTm n}
    (hMaps : Γ ⊢[PRAAx] mapsInto F r caps x) (hMono : Γ ⊢[PRAAx] monotoneOn F r caps x) :
    Γ ⊢[PRAAx] closureConclusion F r caps x := by
  refine .andI (iterate_bounded_at hMaps _) (.andI (closure_stable hMaps hMono)
    (.andI (closure_prefixed hMaps hMono) ?_))
  refine .allI (.impI (.impI ?_))
  let Δ := prefixed F (Syn.shift r) (var 0) (Syn.shift x) ::
    ordered (Syn.shift r) (var 0) (Syn.shift caps) :: Γ.map Fm.shift
  have hm : Δ ⊢[PRAAx] mapsInto F (Syn.shift r) (Syn.shift caps) (Syn.shift x) := by
    simpa only [Δ, Fm.shift, subst_mapsInto, Syn.shift] using hMaps.shift.wk.wk
  have hn : Δ ⊢[PRAAx] monotoneOn F (Syn.shift r) (Syn.shift caps) (Syn.shift x) := by
    simpa only [Δ, Fm.shift, subst_monotoneOn, Syn.shift] using hMono.shift.wk.wk
  exact iterate_le_prefixed_at hm hn Prf.hyp1 Prf.hyp0 _

/-- Closed source sentence for `thm:demand-closure`, with variables `r`, caps, data. -/
theorem demand_closure_closed (F : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (mapsInto F (var 0) (var 1) (var 2) ⟶
      monotoneOn F (var 0) (var 1) (var 2) ⟶ closureConclusion F (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (demand_closure Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Foundations.DemandClosure

export_ipra Foundations.DemandClosure (maximum_le)
