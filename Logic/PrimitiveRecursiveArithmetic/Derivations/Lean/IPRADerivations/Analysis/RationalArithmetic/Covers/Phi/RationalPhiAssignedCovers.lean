import IPRADerivations.Analysis.RationalArithmetic.Covers.Phi.RationalPhiCoverBound
import IPRADerivations.Foundations.FiniteCoverGroupBudgets

/-!
# Cover counts for finitely many original point conditions

The actual bounded first-match assignment separates the original points
by a fixed numerical condition reader. Each group retains the original
raw points and satisfies its selected condition. The local cover for
condition i is tested with the stored budget at i. Applying the source
curve bound and summing the actual partition gives m times the sum of
the stored budgets.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPhiAssignedCovers

open_ipra
open RationalPhiCoverAssignment (sourceCoverBit)
open RationalPhiSectionNonzero (curveInput)
open RationalCurvePointsGaussianEmbedding (distinct distinctFrom distinct_at)
open RationalSuperellipticNormDegree (pointPowers point_power_at)
open GaussianRationalFiberGrouping (abscissa ordinate)
open RationalArgmin (rationalEq rationalEq_congr)
open LeanProofs.IPRA.Foundations.FiniteCoverAssignment
  (cover group group_lookup group_length index_bound indices indices_increasing group_test)
open LeanProofs.IPRA.Foundations.FiniteCoverGroupBudgets (budgetSum groupBudgets)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem group_power_at (t : PTm 3) (f r P K p g i : PTm n) (h : Γ ⊢[PRAAx] pointPowers f r P)
    (hi : Γ ⊢[PRAAx] lt i (length (group t P K p g))) : Γ ⊢[PRAAx]
    rationalEq (RationalScalarPowerGaussianEmbedding.power (ordinate (group t P K p g) i) r)
      (RationalPolynomialGaussianEmbedding.evaluate f (abscissa (group t P K p g) i)) := by
  have atSize := lt_congr (.eqRefl i) (group_length t P K p g) hi
  have kept := group_lookup t P K p g i atSize
  have original := point_power_at f r P _ h (index_bound t P K p g i atSize)
  have y := congrAp2 RationalScalarPowerGaussianEmbedding.powerF (.eqRefl r) (congrSnd kept)
  have x := congrAp3 RationalPolynomialGaussianEmbedding.hornerF (.eqRefl (length f)) (.eqRefl f) (congrFst kept)
  exact rationalEq_congr y.eqSymm x.eqSymm original

theorem group_powers (t : PTm 3) (f r P K p g : PTm n) (h : Γ ⊢[PRAAx] pointPowers f r P) :
    Γ ⊢[PRAAx] pointPowers f r (group t P K p g) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointPowers (Syn.shift f) (Syn.shift r) (Syn.shift P) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa [Syn.shift] using group_power_at t (Syn.shift f) (Syn.shift r) (Syn.shift P)
    (Syn.shift K) (Syn.shift p) (Syn.shift g) (var 0) hs.wk Prf.hyp0

private theorem group_distinct_at (t : PTm 3) (P K p g i j : PTm n) (h : Γ ⊢[PRAAx] distinct P)
    (hi : Γ ⊢[PRAAx] lt i (length (group t P K p g))) (hj : Γ ⊢[PRAAx] lt j (length (group t P K p g)))
    (hij : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx]
    neg (rationalEq (abscissa (group t P K p g) j) (abscissa (group t P K p g) i) ⋏
      rationalEq (ordinate (group t P K p g) j) (ordinate (group t P K p g) i)) := by
  let I := indices t P K p g
  have size := group_length (Γ := Γ) t P K p g
  have bi := lt_congr (.eqRefl i) size hi
  have bj := lt_congr (.eqRefl j) size hj
  have ei := group_lookup t P K p g i bi
  have ej := group_lookup t P K p g j bj
  have original := distinct_at P (entry I i) (entry I j) h
    (index_bound t P K p g i bi) (index_bound t P K p g j bj)
    (indices_increasing t P K p g i j hij bj)
  exact .impI (.impE original.wk (.andI
    (rationalEq_congr (congrFst ej.wk) (congrFst ei.wk) (.andE₁ Prf.hyp0))
    (rationalEq_congr (congrSnd ej.wk) (congrSnd ei.wk) (.andE₂ Prf.hyp0))))

theorem group_distinct (t : PTm 3) (P K p g : PTm n) (h : Γ ⊢[PRAAx] distinct P) :
    Γ ⊢[PRAAx] distinct (group t P K p g) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift P) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let G := group t (Syn.shift P) (Syn.shift K) (Syn.shift p) (Syn.shift g)
  let Δ := lt (var 0) (length G) :: Γ.map Fm.shift
  have hg : Δ ⊢[PRAAx] lt (var 0) (length G) := Prf.hyp0
  have inner : Δ ⊢[PRAAx] distinctFrom G (var 0) := by
    refine .allI (.impI (.impI ?_))
    let i := Syn.shift (var 0 : PTm (n+1))
    let G' := group t (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift K)) (Syn.shift (Syn.shift p)) (Syn.shift (Syn.shift g))
    have hgs : Δ.map Fm.shift ⊢[PRAAx] lt i (length G') := by
      simpa [i,G,G',Fm.shift,Syn.shift] using hg.shift
    have hDs : Δ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift (Syn.shift P)) := by
      simpa only [Fm.shift,RationalCurvePointsGaussianEmbedding.subst_distinct,Syn.shift] using
        (hs.wk : Δ ⊢[PRAAx] distinct (Syn.shift P)).shift
    simpa [i,G,G',Syn.shift] using group_distinct_at t (Syn.shift (Syn.shift P))
      (Syn.shift (Syn.shift K)) (Syn.shift (Syn.shift p)) (Syn.shift (Syn.shift g))
        i (var 0) hDs.wk.wk hgs.wk.wk Prf.hyp1 Prf.hyp0
  simpa [Δ,G,Syn.shift] using inner

def satisfies (t : PTm 3) (Q g p : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift Q)) ⟶
    neg (inst3 t (Syn.shift g) (entry (Syn.shift Q) (var 0)) (Syn.shift p) ≐ zero))

ipra_subst satisfies [Syn.subst_shift, Syn.shift_subst]

theorem group_satisfies (t : PTm 3) (P K p g : PTm n) (h : Γ ⊢[PRAAx] cover t P K p) :
    Γ ⊢[PRAAx] satisfies t (group t P K p g) g p := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] cover t (Syn.shift P) (Syn.shift K) (Syn.shift p) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let G := group t (Syn.shift P) (Syn.shift K) (Syn.shift p) (Syn.shift g)
  let Δ := lt (var 0) (length G) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (length G) := Prf.hyp0
  have ht := group_test t (Syn.shift P) (Syn.shift K) (Syn.shift p) (Syn.shift g) (var 0) hs.wk
    (lt_congr (.eqRefl _) (group_length _ _ _ _ _) hi)
  simpa [Δ,G,Syn.shift] using ht

def budgetCovers (t : PTm 3) (s P K p B : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift K) ⟶ sourceCoverBit (Syn.shift s)
    (group t (Syn.shift P) (Syn.shift K) (Syn.shift p) (var 0)) (entry (Syn.shift B) (var 0)) ≐ one)

ipra_subst budgetCovers [Syn.subst_shift, Syn.shift_subst, one]

theorem budget_cover_at (t : PTm 3) (s P K p B g : PTm n) (h : Γ ⊢[PRAAx] budgetCovers t s P K p B)
    (hg : Γ ⊢[PRAAx] lt g K) :
    Γ ⊢[PRAAx] sourceCoverBit s (group t P K p g) (entry B g) ≐ one := by
  have rule : Γ ⊢[PRAAx] lt g K ⟶ sourceCoverBit s (group t P K p g) (entry B g) ≐ one := by
    simpa [budgetCovers,one] using h.allE g
  exact .impE rule hg

theorem group_bounds (t : PTm 3) (f s r m P K p B : PTm n)
    (hf : Γ ⊢[PRAAx] curveInput f s r m) (hd : Γ ⊢[PRAAx] distinct P) (hp : Γ ⊢[PRAAx] pointPowers f r P)
    (hb : Γ ⊢[PRAAx] budgetCovers t s P K p B) : Γ ⊢[PRAAx] groupBudgets t P K p B m := by
  have input : Γ.map Fm.shift ⊢[PRAAx] curveInput (Syn.shift f) (Syn.shift s) (Syn.shift r) (Syn.shift m) := by
    simpa [Fm.shift,Syn.shift] using hf.shift
  have dist : Γ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift P) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have powers : Γ.map Fm.shift ⊢[PRAAx] pointPowers (Syn.shift f) (Syn.shift r) (Syn.shift P) := by
    simpa [Fm.shift,Syn.shift] using hp.shift
  have budgets : Γ.map Fm.shift ⊢[PRAAx] budgetCovers t (Syn.shift s) (Syn.shift P)
      (Syn.shift K) (Syn.shift p) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hb.shift
  refine .allI (.impI ?_)
  exact RationalPhiCoverBound.cover_bit_bound (Syn.shift f) (Syn.shift s) (Syn.shift r) (Syn.shift m)
    (group t (Syn.shift P) (Syn.shift K) (Syn.shift p) (var 0)) (entry (Syn.shift B) (var 0)) input.wk
    (group_distinct _ _ _ _ _ dist.wk) (group_powers _ _ _ _ _ _ _ powers.wk)
    (budget_cover_at _ _ _ _ _ _ _ budgets.wk Prf.hyp0)

theorem assigned_bound (t : PTm 3) (f s r m P K p B : PTm n)
    (hf : Γ ⊢[PRAAx] curveInput f s r m) (hd : Γ ⊢[PRAAx] distinct P) (hp : Γ ⊢[PRAAx] pointPowers f r P)
    (ht : Γ ⊢[PRAAx] cover t P K p) (hb : Γ ⊢[PRAAx] budgetCovers t s P K p B) :
    Γ ⊢[PRAAx] le (length P) (m * budgetSum K B) :=
  LeanProofs.IPRA.Foundations.FiniteCoverGroupBudgets.cover_count t P K p B m ht
    (group_bounds t f s r m P K p B hf hd hp hb)

/-- A fixed first-order property of each original raw point and a parameter. -/
def allPoints (φ : Fm PTm 2) (P x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift P)) ⟶ φ.subst ![entry (Syn.shift P) (var 0), Syn.shift x])

@[simp] theorem subst_allPoints {k : ℕ} (σ : Fin n → PTm k) (φ : Fm PTm 2) (P x : PTm n) :
    (allPoints φ P x).subst σ = allPoints φ (Syn.subst σ P) (Syn.subst σ x) := by
  simp only [allPoints,Fm.subst_all,Fm.subst_imp,subst_lt,Foundations.SequenceComposition.subst_length,
    Fm.subst_subst,Syn.subst_var,Syn.up_zero,Syn.subst_shift,Syn.shift_subst]
  congr 2
  congr 1
  funext i
  fin_cases i <;> simp [Syn.subst_shift]

theorem group_all_points (φ : Fm PTm 2) (t : PTm 3) (P K p g x : PTm n) (h : Γ ⊢[PRAAx] allPoints φ P x) :
    Γ ⊢[PRAAx] allPoints φ (group t P K p g) x := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] allPoints φ (Syn.shift P) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,Foundations.FiniteCoverAssignment.subst_group] using
    Foundations.FiniteCoverAssignment.group_property_at φ t (Syn.shift P) (Syn.shift K) (Syn.shift p)
      (Syn.shift g) (var 0) (Syn.shift x) hs.wk (lt_congr (.eqRefl _) (group_length _ _ _ _ _) Prf.hyp0)

/-- The cover assertion for one condition concerns each original tuple in it. -/
def groupCoverRule (φ : Fm PTm 2) (t : PTm 3) (f s r M g p x : PTm n) : Fm PTm n :=
  .all (distinct (var 0) ⟶ pointPowers (Syn.shift f) (Syn.shift r) (var 0) ⟶
    satisfies t (var 0) (Syn.shift g) (Syn.shift p) ⟶ allPoints φ (var 0) (Syn.shift x) ⟶
    sourceCoverBit (Syn.shift s) (var 0) (Syn.shift M) ≐ one)

ipra_subst groupCoverRule [Syn.subst_shift, Syn.shift_subst, one]

/-- Each condition uses the budget stored at its own index. -/
def conditionCovers (φ : Fm PTm 2) (t : PTm 3) (f s r K p B x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift K) ⟶ groupCoverRule φ t (Syn.shift f) (Syn.shift s) (Syn.shift r)
    (entry (Syn.shift B) (var 0)) (var 0) (Syn.shift p) (Syn.shift x))

ipra_subst conditionCovers [Syn.subst_shift, Syn.shift_subst]

theorem condition_cover_at (φ : Fm PTm 2) (t : PTm 3) (f s r K p B g Q x : PTm n)
    (h : Γ ⊢[PRAAx] conditionCovers φ t f s r K p B x)
    (hg : Γ ⊢[PRAAx] lt g K) (hd : Γ ⊢[PRAAx] distinct Q) (hp : Γ ⊢[PRAAx] pointPowers f r Q)
    (ht : Γ ⊢[PRAAx] satisfies t Q g p) (hx : Γ ⊢[PRAAx] allPoints φ Q x) :
    Γ ⊢[PRAAx] sourceCoverBit s Q (entry B g) ≐ one := by
  have atCondition : Γ ⊢[PRAAx] lt g K ⟶ groupCoverRule φ t f s r (entry B g) g p x := by
    simpa [conditionCovers] using h.allE g
  have atTuple : Γ ⊢[PRAAx] distinct Q ⟶ pointPowers f r Q ⟶ satisfies t Q g p ⟶ allPoints φ Q x ⟶
      sourceCoverBit s Q (entry B g) ≐ one := by
    simpa [groupCoverRule,one] using (Prf.impE atCondition hg).allE Q
  exact .impE (.impE (.impE (.impE atTuple hd) hp) ht) hx

theorem budget_covers_of_conditions (φ : Fm PTm 2) (t : PTm 3) (f s r P K p B x : PTm n) (hd : Γ ⊢[PRAAx] distinct P)
    (hp : Γ ⊢[PRAAx] pointPowers f r P) (ht : Γ ⊢[PRAAx] cover t P K p)
    (hx : Γ ⊢[PRAAx] allPoints φ P x) (hc : Γ ⊢[PRAAx] conditionCovers φ t f s r K p B x) :
    Γ ⊢[PRAAx] budgetCovers t s P K p B := by
  have ds : Γ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift P) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have ps : Γ.map Fm.shift ⊢[PRAAx] pointPowers (Syn.shift f) (Syn.shift r) (Syn.shift P) := by
    simpa [Fm.shift,Syn.shift] using hp.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] cover t (Syn.shift P) (Syn.shift K) (Syn.shift p) := by
    simpa [Fm.shift,Syn.shift] using ht.shift
  have xs : Γ.map Fm.shift ⊢[PRAAx] allPoints φ (Syn.shift P) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using hx.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] conditionCovers φ t (Syn.shift f) (Syn.shift s) (Syn.shift r)
      (Syn.shift K) (Syn.shift p) (Syn.shift B) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using hc.shift
  refine .allI (.impI ?_)
  exact condition_cover_at φ t _ _ _ _ _ _ (var 0) _ _ cs.wk Prf.hyp0
    (group_distinct _ _ _ _ _ ds.wk) (group_powers _ _ _ _ _ _ _ ps.wk) (group_satisfies _ _ _ _ _ ts.wk)
    (group_all_points _ _ _ _ _ _ _ xs.wk)

theorem condition_cover_bound (φ : Fm PTm 2) (t : PTm 3) (f s r m P K p B x : PTm n)
    (hf : Γ ⊢[PRAAx] curveInput f s r m) (hd : Γ ⊢[PRAAx] distinct P) (hp : Γ ⊢[PRAAx] pointPowers f r P)
    (ht : Γ ⊢[PRAAx] cover t P K p) (hx : Γ ⊢[PRAAx] allPoints φ P x)
    (hc : Γ ⊢[PRAAx] conditionCovers φ t f s r K p B x) :
    Γ ⊢[PRAAx] le (length P) (m * budgetSum K B) :=
  assigned_bound t f s r m P K p B hf hd hp ht (budget_covers_of_conditions φ t f s r P K p B x hd hp ht hx hc)

theorem actual_condition_group_bound_closed (t : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (curveInput (var 0) (var 1) (var 2) (var 3) ⟶ distinct (var 4) ⟶ pointPowers (var 0) (var 2) (var 4) ⟶
      cover t (var 4) (var 5) (var 6) ⟶ budgetCovers t (var 1) (var 4) (var 5) (var 6) (var 7) ⟶
      le (length (var 4)) (var 3 * budgetSum (var 5) (var 7))) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI (assigned_bound t
    (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))))

theorem actual_original_condition_cover_closed (φ : Fm PTm 2) (t : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (curveInput (var 0) (var 1) (var 2) (var 3) ⟶ distinct (var 4) ⟶ pointPowers (var 0) (var 2) (var 4) ⟶
      cover t (var 4) (length (var 6)) (var 5) ⟶ allPoints φ (var 4) (var 7) ⟶
      conditionCovers φ t (var 0) (var 1) (var 2) (length (var 6)) (var 5) (var 6) (var 7) ⟶
      le (length (var 4)) (var 3 * budgetSum (length (var 6)) (var 6))) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI (.impI (condition_cover_bound φ t
    (var 0) (var 1) (var 2) (var 3) (var 4) (length (var 6)) (var 5) (var 6) (var 7)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.RationalPhiAssignedCovers
