import IPRADerivations.Foundations.FiniteHausdorffOperations

/-!
# Weighted Hausdorff image bounds from finite-pair laws

Finite-demand packet, `lem:aggregate-calculus`, clause 4. The Lipschitz
premises concern only actual pairs from the supplied source lists, in each
direction. The image lists, nearest indices, minima and maxima are the actual
checked primitive recursive constructions. Their correctness is derived,
not a client premise.

The weights `A,B` are arbitrary internal naturals, including zero. For
positive `B`, their ratio represents a rational Lipschitz constant. Independent
positive source/target common rational scales are accommodated by replacing
`A,B` by `A*targetScale,B*sourceScale`. No global Lipschitz law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.FiniteHausdorffImage

open_ipra exports
open LeanProofs.IPRA.Foundations.FiniteHausdorff
open LeanProofs.IPRA.Foundations.FiniteHausdorffOperations
  (mapList map_length map_lookup subst_mapList)
open LeanProofs.IPRA.Foundations.FiniteQueryDemand
  (finiteMaximum finiteMaximum_zero finiteMaximum_succ subst_finiteMaximum)
open LeanProofs.IPRA.Foundations.DemandClosure
  (maximum subst_maximum maximum_left maximum_right maximum_le)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem maximum_eq_right {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] maximum a b ≐ b := (eq_add_of_le h).eqSymm

private theorem maximum_eq_left {a b : PTm n} (h : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] maximum a b ≐ a :=
  (congrAdd (.eqRefl _) h).eqTrans (add_zero _)

/-- Homogeneity of the actual maximum term, including multiplier zero. -/
theorem scale_maximum (c a b : PTm n) :
    Γ ⊢[PRAAx] c*maximum a b ≐ maximum (c*a) (c*b) := by
  refine .orE (le_total a b) ?_ ?_
  · exact (congrMul (.eqRefl _) (maximum_eq_right Prf.hyp0)).eqTrans
      (maximum_eq_right (le_mul_mono (le_refl c) Prf.hyp0)).eqSymm
  · exact (congrMul (.eqRefl _) (maximum_eq_left Prf.hyp0)).eqTrans
      (maximum_eq_left (le_mul_mono (le_refl c) Prf.hyp0)).eqSymm

/-- A weighted bound for an actual maximum fold, proved by QF induction. -/
theorem scaled_maximum_bound (body : PTm 2) (N x B R : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift B*inst2 body (var 0) (Syn.shift x)) (Syn.shift R))) :
    Γ ⊢[PRAAx] le (B*finiteMaximum body N x) R := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      le (Syn.shift B*finiteMaximum body (var 0) (Syn.shift x)) (Syn.shift R)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, PTm.subst_mul, subst_finiteMaximum,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact .impI (le_congr ((congrMul (.eqRefl _) (finiteMaximum_zero body x)).eqTrans (mul_zero B)).eqSymm
        (.eqRefl _) (zero_le R))
    · simp only [Fm.subst_imp, subst_le, PTm.subst_mul, subst_finiteMaximum,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      let Δ : List (Fm PTm (n+1)) := le (succ (var 0)) (Syn.shift N) ::
        (le (var 0) (Syn.shift N) ⟶
          le (Syn.shift B*finiteMaximum body (var 0) (Syn.shift x)) (Syn.shift R)) :: Γ.map Fm.shift
      have old : Δ ⊢[PRAAx] le (Syn.shift B*finiteMaximum body (var 0) (Syn.shift x)) (Syn.shift R) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have next : Δ ⊢[PRAAx] le (Syn.shift B*inst2 body (var 0) (Syn.shift x)) (Syn.shift R) :=
        .impE h.allOpen.wk.wk Prf.hyp0
      exact le_congr
        ((congrMul (.eqRefl _) (finiteMaximum_succ body _ _)).eqTrans (scale_maximum _ _ _)).eqSymm
        (.eqRefl _) (maximum_le old next)
  have contract : Γ ⊢[PRAAx] le N N ⟶ le (B*finiteMaximum body N x) R := by
    simpa only [Fm.subst_imp, subst_le, PTm.subst_mul, subst_finiteMaximum,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE N all
  exact .impE contract (le_refl N)

/-- Weighted directed distance follows from the actual weighted point minima. -/
theorem weighted_directed_bound (d : PR 3) (S T B R p : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (length (Syn.shift S)) ⟶
      le (Syn.shift B*distanceTo d (entry (Syn.shift S) (var 0)) (Syn.shift T) (Syn.shift p)) (Syn.shift R))) :
    Γ ⊢[PRAAx] le (B*directed d S T p) R := by
  apply scaled_maximum_bound
  refine .allI (.impI ?_)
  have point := Prf.impE h.allOpen.wk Prf.hyp0
  have eq := directedBody_at (Γ := lt (var 0) (length (Syn.shift S)) :: Γ.map Fm.shift)
    d (Syn.shift S) (Syn.shift T) (Syn.shift p) (var 0)
  simpa only [Syn.shift, subst_pointData, subst_length] using
    le_congr (congrMul (.eqRefl (Syn.shift B)) eq.eqSymm) (.eqRefl _) point

/-- The only needed mathematical law: finite, oriented source-list pairs. -/
def finiteLaw (d e : PR 3) (f : PR 2) (S T A B p : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift S)) ⟶
    .all (lt (var 0) (length (Syn.shift (Syn.shift T))) ⟶
      le (Syn.shift (Syn.shift B)*distance e
        (ap2 f (entry (Syn.shift (Syn.shift S)) (var 1)) (Syn.shift (Syn.shift p)))
        (ap2 f (entry (Syn.shift (Syn.shift T)) (var 0)) (Syn.shift (Syn.shift p)))
        (Syn.shift (Syn.shift p)))
        (Syn.shift (Syn.shift A)*distance d (entry (Syn.shift (Syn.shift S)) (var 1))
          (entry (Syn.shift (Syn.shift T)) (var 0)) (Syn.shift (Syn.shift p)))))

@[simp] theorem subst_finiteLaw {m : ℕ} (σ : Fin n → PTm m)
    (d e : PR 3) (f : PR 2) (S T A B p : PTm n) :
    (finiteLaw d e f S T A B p).subst σ =
      finiteLaw d e f (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ p) := by
  simp only [finiteLaw, Fm.subst_all, Fm.subst_imp, subst_lt, subst_le, PTm.subst_mul,
    subst_distance, subst_ap2, subst_entry, subst_length, Syn.subst_var,
    Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.subst_shift, Syn.shift_subst,
    Syn.shift_var, Fin.succ_zero_eq_one]

/-- Instantiate a finite local law only at actually in-range supplied entries. -/
theorem finiteLaw_at (d e : PR 3) (f : PR 2) {S T A B p : PTm n}
    (h : Γ ⊢[PRAAx] finiteLaw d e f S T A B p) (i j : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length S)) (hj : Γ ⊢[PRAAx] lt j (length T)) :
    Γ ⊢[PRAAx] le (B*distance e (ap2 f (entry S i) p) (ap2 f (entry T j) p) p)
      (A*distance d (entry S i) (entry T j) p) := by
  have first : Γ ⊢[PRAAx] lt i (length S) ⟶
      .all (lt (var 0) (length (Syn.shift T)) ⟶
        le (Syn.shift B*distance e (ap2 f (entry (Syn.shift S) (Syn.shift i)) (Syn.shift p))
          (ap2 f (entry (Syn.shift T) (var 0)) (Syn.shift p)) (Syn.shift p))
          (Syn.shift A*distance d (entry (Syn.shift S) (Syn.shift i))
            (entry (Syn.shift T) (var 0)) (Syn.shift p))) := by
    simpa only [finiteLaw, Fm.subst_all, Fm.subst_imp, subst_lt, subst_le, PTm.subst_mul,
      subst_distance, subst_ap2, subst_entry, subst_length, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.subst_inst_shift,
      BoundedFormulas.subst_up_shift'] using Prf.allE i h
  have second := Prf.allE j (Prf.impE first hi)
  have contract : Γ ⊢[PRAAx] lt j (length T) ⟶
      le (B*distance e (ap2 f (entry S i) p) (ap2 f (entry T j) p) p)
        (A*distance d (entry S i) (entry T j) p) := by
    simpa only [Fm.subst_imp, subst_lt, subst_le, PTm.subst_mul, subst_distance, subst_ap2,
      subst_entry, subst_length, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using second
  exact Prf.impE contract hj

/-- The actual nearest source neighbor suffices for one weighted image minimum. -/
theorem image_point_bound (d e : PR 3) (f : PR 2) (S T A B p i : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length T))
    (hf : Γ ⊢[PRAAx] finiteLaw d e f S T A B p) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] le (B*distanceTo e (entry (mapList f S p) i) (mapList f T p) p)
      (A*directed d S T p) := by
  let j := nearest d (entry S i) T p
  have hj : Γ ⊢[PRAAx] lt j (length T) := .andE₁ (nearest_spec d (entry S i) T p hT)
  have hm : Γ ⊢[PRAAx] lt j (length (mapList f T p)) :=
    lt_congr (.eqRefl _) (map_length f T p).eqSymm hj
  have law := finiteLaw_at d e f hf i j hi hj
  have mapped : Γ ⊢[PRAAx] le
      (B*distance e (entry (mapList f S p) i) (entry (mapList f T p) j) p)
      (A*distance d (entry S i) (entry T j) p) :=
    le_congr (congrMul (.eqRefl _)
      (congrAp3 e (map_lookup f S p i hi) (map_lookup f T p j hj) (.eqRefl _))).eqSymm (.eqRefl _) law
  exact le_trans (le_mul_mono (le_refl B) (distanceTo_le e _ _ p j hm))
    (le_trans mapped (le_mul_mono (le_refl A) (nearest_error d S T p i hT hi)))

/-- The directed weighted image estimate needs only the forward finite-pair law. -/
theorem directed_image_local (d e : PR 3) (f : PR 2) (S T A B p : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length T)) (hf : Γ ⊢[PRAAx] finiteLaw d e f S T A B p) :
    Γ ⊢[PRAAx] le (B*directed e (mapList f S p) (mapList f T p) p) (A*directed d S T p) := by
  apply weighted_directed_bound
  refine .allI (.impI ?_)
  let Δ : List (Fm PTm (n+1)) := lt (var 0) (length (Syn.shift (mapList f S p))) :: Γ.map Fm.shift
  have sourceLength : Δ ⊢[PRAAx] length (Syn.shift (mapList f S p)) ≐ length (Syn.shift S) := by
    simpa only [Fm.shift, Fm.subst_eq, subst_length, Syn.shift] using (map_length (Γ := Γ) f S p).shift.wk
  have hi : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift S)) := lt_congr (.eqRefl _) sourceLength Prf.hyp0
  have t : Δ ⊢[PRAAx] le one (length (Syn.shift T)) := by
    simpa only [Fm.shift, subst_le, subst_length, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero, Syn.shift] using hT.shift.wk
  have law : Δ ⊢[PRAAx] finiteLaw d e f (Syn.shift S) (Syn.shift T)
      (Syn.shift A) (Syn.shift B) (Syn.shift p) := by
    simpa only [Fm.shift, subst_finiteLaw, Syn.shift] using hf.shift.wk
  simpa only [Δ, Syn.shift, subst_mapList, PTm.subst_mul, subst_directed] using
    image_point_bound d e f (Syn.shift S) (Syn.shift T) (Syn.shift A) (Syn.shift B) (Syn.shift p) (var 0) t law hi

/-- Full finite-pair image clause, with rational weights and no global law. -/
theorem hausdorff_image_local (d e : PR 3) (f : PR 2) (S T A B p : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (forward : Γ ⊢[PRAAx] finiteLaw d e f S T A B p)
    (backward : Γ ⊢[PRAAx] finiteLaw d e f T S A B p) :
    Γ ⊢[PRAAx] le (B*hausdorff e (mapList f S p) (mapList f T p) p) (A*hausdorff d S T p) :=
  le_congr (scale_maximum B _ _).eqSymm (.eqRefl _)
    (maximum_le (le_trans (directed_image_local d e f S T A B p hT forward)
      (le_mul_mono (le_refl A) (maximum_left _ _)))
      (le_trans (directed_image_local d e f T S A B p hS backward)
        (le_mul_mono (le_refl A) (maximum_right _ _))))

/-- Variables are the two lists, multiplier numerator/denominator, and persistent data. -/
def imageFormula (d e : PR 3) (f : PR 2) : Fm PTm 5 :=
  le one (length (var 0)) ⟶ le one (length (var 1)) ⟶
    finiteLaw d e f (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
    finiteLaw d e f (var 1) (var 0) (var 2) (var 3) (var 4) ⟶
    le (var 3*hausdorff e (mapList f (var 0) (var 4)) (mapList f (var 1) (var 4)) (var 4))
      (var 2*hausdorff d (var 0) (var 1) (var 4))

theorem local_image_closed (d e : PR 3) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 (imageFormula d e f) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (hausdorff_image_local d e f
    (var 0) (var 1) (var 2) (var 3) (var 4) Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

/-- Distinct rational source/target scales are retained as exact internal weights.
For positive `B,Ds,Dt`, this is `H_e/Dt ≤ (A/B)*(H_d/Ds)`. -/
theorem rational_scaled_image (d e : PR 3) (f : PR 2) (S T A B Ds Dt p : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (forward : Γ ⊢[PRAAx] finiteLaw d e f S T (A*Dt) (B*Ds) p)
    (backward : Γ ⊢[PRAAx] finiteLaw d e f T S (A*Dt) (B*Ds) p) :
    Γ ⊢[PRAAx] le ((B*Ds)*hausdorff e (mapList f S p) (mapList f T p) p)
      ((A*Dt)*hausdorff d S T p) :=
  hausdorff_image_local d e f S T (A*Dt) (B*Ds) p hS hT forward backward

/-- All scale and multiplier data are internal; positivity is unnecessary for
this denominator-cleared inequality and can be imposed by rational clients. -/
theorem rational_scaled_image_closed (d e : PR 3) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶
        finiteLaw d e f (var 0) (var 1) (var 2*var 5) (var 3*var 4) (var 6) ⟶
        finiteLaw d e f (var 1) (var 0) (var 2*var 5) (var 3*var 4) (var 6) ⟶
        le ((var 3*var 4)*hausdorff e (mapList f (var 0) (var 6)) (mapList f (var 1) (var 6)) (var 6))
          ((var 2*var 5)*hausdorff d (var 0) (var 1) (var 6))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (rational_scaled_image d e f
    (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
      Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

#print axioms scale_maximum
#print axioms scaled_maximum_bound
#print axioms weighted_directed_bound
#print axioms finiteLaw_at
#print axioms image_point_bound
#print axioms directed_image_local
#print axioms hausdorff_image_local
#print axioms local_image_closed
#print axioms rational_scaled_image_closed

end LeanProofs.IPRA.Foundations.FiniteHausdorffImage
