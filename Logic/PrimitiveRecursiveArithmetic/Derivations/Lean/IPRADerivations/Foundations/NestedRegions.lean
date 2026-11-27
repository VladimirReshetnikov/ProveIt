import IPRADerivations.Core.MultiSums
import IPRADerivations.Core.Gcd
import IPRADerivations.Core.Header

/-!
# Nested rational balls and their regular center name

Packet `foundations/ipra_finite_use_framework_2026-11-15_v2`, Theorem
`thm:nested-name`. Encoded points have a primitive recursive rational
nonnegative distance. Each radius and distance is its natural numerator and
positive denominator. Ball membership is the exact denominator-cleared
comparison. The proof derives transitive inclusion by quantifier-free
induction on the interval length.

Agreement with a solution has an explicit compatibility hypothesis asserting
membership in every isolating ball. This is the region-membership hypothesis
needed by the source's uniqueness argument.
-/

namespace LeanProofs.IPRA.Foundations.NestedRegions

open_ipra exports

variable {n m : ℕ} {Γ : List (Fm PTm n)}

/-- Fixed programs presenting rational balls on a domain of encoded points. -/
structure BallCodes where
  domain : PR 2
  center : PR 2
  radiusNum : PR 2
  radiusDen : PR 2
  distanceNum : PR 3
  distanceDen : PR 3

/-- The natural numerator of the distance of two encoded points. -/
abbrev dn (B : BallCodes) (u v x : PTm n) : PTm n := ap3 B.distanceNum u v x
/-- The positive denominator of that distance. -/
abbrev dd (B : BallCodes) (u v x : PTm n) : PTm n := ap3 B.distanceDen u v x
/-- The center at precision `k` and runtime parameter `x`. -/
abbrev center (B : BallCodes) (k x : PTm n) : PTm n := ap2 B.center k x

/-- Membership in the exact rational closed ball at precision `k`. -/
def ball (B : BallCodes) (k z x : PTm n) : Fm PTm n :=
  (ap2 B.domain z x ≐ one) ⋏
    le (dn B z (center B k x) x * ap2 B.radiusDen k x)
      (ap2 B.radiusNum k x * dd B z (center B k x) x)

@[simp] theorem subst_ball (B : BallCodes) (k z x : PTm n) (σ : Fin n → PTm m) :
    (ball B k z x).subst σ =
      ball B (Syn.subst σ k) (Syn.subst σ z) (Syn.subst σ x) := by
  ipra_ind_simp [ball, subst_le, subst_ap2, subst_ap3]

theorem ball_QF (B : BallCodes) (k z x : PTm n) : (ball B k z x).QF := ⟨trivial, le_QF _ _⟩

/-- Every immediately later ball is contained in its predecessor. -/
def nesting (B : BallCodes) (x : PTm n) : Fm PTm n :=
  .all (.all (ball B (succ (var 1)) (var 0) (Syn.shift (Syn.shift x)) ⟶
    ball B (var 1) (var 0) (Syn.shift (Syn.shift x))))

@[simp] theorem subst_nesting (B : BallCodes) (x : PTm n) (σ : Fin n → PTm m) :
    (nesting B x).subst σ = nesting B (Syn.subst σ x) := by
  ipra_ind_simp [nesting, Fm.subst_all, subst_ball, Syn.up_zero, Syn.up_succ, Syn.up_one, Syn.shift_var,
    Fin.succ_zero_eq_one, Syn.subst_shift, Syn.shift_subst]

theorem nesting_at (B : BallCodes) (k z x : PTm n)
    (h : Γ ⊢[PRAAx] nesting B x) :
    Γ ⊢[PRAAx] ball B (succ k) z x ⟶ ball B k z x := by
  have result := Prf.allE z (Prf.allE k h)
  simpa only [nesting, Fm.subst_all, Fm.subst_imp, subst_ball, Syn.subst_var,
    Syn.up_zero, Syn.up_succ, Syn.up_one, Syn.inst_zero, Syn.inst_one, Syn.inst_succ,
    Syn.subst_shift, Syn.subst_inst_shift, Syn.subst_subst, Syn.subst_id,
    ConciseIPRA.PTm.subst_succ] using result

/-- Change the ball index by an object-theory equality. -/
theorem ball_congr_index (B : BallCodes) {k l z x : PTm n}
    (eq : Γ ⊢[PRAAx] k ≐ l) (member : Γ ⊢[PRAAx] ball B k z x) :
    Γ ⊢[PRAAx] ball B l z x := by
  have c := congrAp2 B.center eq (.eqRefl x)
  exact .andI (.andE₁ member) (le_congr
    (congrMul (congrAp3 B.distanceNum (.eqRefl z) c (.eqRefl x))
      (congrAp2 B.radiusDen eq (.eqRefl x)))
    (congrMul (congrAp2 B.radiusNum eq (.eqRefl x))
      (congrAp3 B.distanceDen (.eqRefl z) c (.eqRefl x))) (.andE₂ member))

/-- The inclusion between arbitrary internal indices is derived from adjacent inclusion. -/
theorem nested_interval (B : BallCodes) (N r z x : PTm n)
    (h : Γ ⊢[PRAAx] nesting B x) :
    Γ ⊢[PRAAx] ball B (N + r) z x ⟶ ball B N z x := by
  have all : Γ ⊢[PRAAx] .all
      (ball B (Syn.shift N + var 0) (Syn.shift z) (Syn.shift x) ⟶
        ball B (Syn.shift N) (Syn.shift z) (Syn.shift x)) := by
    ipra_qfind (⟨ball_QF _ _ _ _, ball_QF _ _ _ _⟩) [subst_ball]
    · exact .impI (ball_congr_index B (add_zero N) Prf.hyp0)
    · apply Prf.impI
      have shifted : Γ.map Fm.shift ⊢[PRAAx] nesting B (Syn.shift x) := by
        simpa only [Fm.shift, subst_nesting, Syn.shift] using h.shift
      exact .impE Prf.hyp1 (.impE
        (nesting_at B (Syn.shift N + var 0) (Syn.shift z) (Syn.shift x) shifted.wk.wk)
        (ball_congr_index B (add_succ (Syn.shift N) (var 0)) Prf.hyp0))
  simpa only [Fm.subst_imp, subst_ball, PTm.subst_add, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE r all

/-- The source endpoint form of transitive ball inclusion. -/
theorem nested_between (B : BallCodes) {N M z x : PTm n}
    (h : Γ ⊢[PRAAx] nesting B x) (order : Γ ⊢[PRAAx] le N M)
    (member : Γ ⊢[PRAAx] ball B M z x) :
    Γ ⊢[PRAAx] ball B N z x :=
  .impE (nested_interval B N (PTm.monus M N) z x h)
    (ball_congr_index B (eq_add_of_le order) member)

/-- Centers belong to the encoded domain and have zero self-distance. -/
def centersValid (B : BallCodes) (x : PTm n) : Fm PTm n :=
  .all ((ap2 B.domain (center B (var 0) (Syn.shift x)) (Syn.shift x) ≐ one) ⋏
    (dn B (center B (var 0) (Syn.shift x)) (center B (var 0) (Syn.shift x))
      (Syn.shift x) ≐ zero))

/-- Distance denominators are positive on the encoded domain. -/
def distancesPositive (B : BallCodes) (x : PTm n) : Fm PTm n :=
  .all (.all (((ap2 B.domain (var 1) (Syn.shift (Syn.shift x)) ≐ one) ⋏
      (ap2 B.domain (var 0) (Syn.shift (Syn.shift x)) ≐ one)) ⟶
    lt zero (dd B (var 1) (var 0) (Syn.shift (Syn.shift x)))))

/-- Radius denominators are positive and radii decay at the stated dyadic rate. -/
def radiiDecay (B : BallCodes) (s x : PTm n) : Fm PTm n :=
  .all (lt zero (ap2 B.radiusDen (var 0) (Syn.shift x)) ⋏
    le (pw two (var 0 + Syn.shift s) * ap2 B.radiusNum (var 0) (Syn.shift x))
      (ap2 B.radiusDen (var 0) (Syn.shift x)))

theorem center_valid_at (B : BallCodes) (k x : PTm n)
    (h : Γ ⊢[PRAAx] centersValid B x) :
    Γ ⊢[PRAAx] (ap2 B.domain (center B k x) x ≐ one) ⋏
      (dn B (center B k x) (center B k x) x ≐ zero) := by
  simpa only [centersValid, Fm.subst_and, Fm.subst_eq, subst_ap2, subst_ap3,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using Prf.allE k h

theorem distance_positive_at (B : BallCodes) (u v x : PTm n)
    (h : Γ ⊢[PRAAx] distancesPositive B x)
    (hu : Γ ⊢[PRAAx] ap2 B.domain u x ≐ one)
    (hv : Γ ⊢[PRAAx] ap2 B.domain v x ≐ one) :
    Γ ⊢[PRAAx] lt zero (dd B u v x) := by
  have result := Prf.allE v (Prf.allE u h)
  apply Prf.impE ?_ (.andI hu hv)
  simpa only [distancesPositive, Fm.subst_all, Fm.subst_imp, Fm.subst_and,
    Fm.subst_eq, subst_lt, subst_ap2, subst_ap3, Syn.subst_var,
    Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.inst_zero, Syn.inst_one,
    Syn.inst_succ, Syn.subst_shift, Syn.subst_inst_shift, Syn.subst_subst,
    Syn.subst_id, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using result

theorem radius_at (B : BallCodes) (k s x : PTm n)
    (h : Γ ⊢[PRAAx] radiiDecay B s x) :
    Γ ⊢[PRAAx] lt zero (ap2 B.radiusDen k x) ⋏
      le (pw two (k + s) * ap2 B.radiusNum k x) (ap2 B.radiusDen k x) := by
  simpa only [radiiDecay, Fm.subst_and, subst_lt, subst_le, PTm.subst_mul,
    PTm.subst_add, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using Prf.allE k h

/-- Reflexivity of distance and a valid center put that center in its own ball. -/
theorem center_member (B : BallCodes) (k x : PTm n)
    (h : Γ ⊢[PRAAx] centersValid B x) : Γ ⊢[PRAAx] ball B k (center B k x) x := by
  have valid := center_valid_at B k x h
  exact .andI (.andE₁ valid)
    (le_congr ((congrMul (.andE₂ valid) (.eqRefl _)).eqTrans (zero_mul _)).eqSymm
      (.eqRefl _) (zero_le _))

/-- Cancel a radius denominator in an exact rational bound. -/
theorem scaled_rational_bound {a b c d P : PTm n}
    (positive : Γ ⊢[PRAAx] lt zero d)
    (distance : Γ ⊢[PRAAx] le (a * d) (b * c))
    (radius : Γ ⊢[PRAAx] le (P * b) d) : Γ ⊢[PRAAx] le (P * a) c := by
  have h₁ := mul_le_mul_right P distance
  have h₂ := mul_le_mul_right c radius
  have multiplied : Γ ⊢[PRAAx] le (d * (P * a)) (d * c) :=
    le_trans (le_congr (by ipra_ring) (by ipra_ring) h₁) h₂
  have canonical : Γ ⊢[PRAAx] d ≐ succ (pred d) :=
    .orE (zero_or_succ d)
      (lt_irrefl zero _ (lt_congr (.eqRefl _) Prf.hyp0 positive.wk)) Prf.hyp0
  exact mul_le_cancel_at canonical multiplied

/-- The exact rational center discrepancy after clearing its positive denominator. -/
def regularBound (B : BallCodes) (N M s x : PTm n) : Fm PTm n :=
  lt zero (dd B (center B M x) (center B N x) x) ⋏
    le (pw two (N + s) * dn B (center B M x) (center B N x) x)
      (dd B (center B M x) (center B N x) x)

/-- Centers form a regular name from adjacent nesting and shrinking radii. -/
theorem center_cauchy (B : BallCodes) (N M s x : PTm n)
    (valid : Γ ⊢[PRAAx] centersValid B x)
    (positive : Γ ⊢[PRAAx] distancesPositive B x)
    (radii : Γ ⊢[PRAAx] radiiDecay B s x)
    (nested : Γ ⊢[PRAAx] nesting B x)
    (order : Γ ⊢[PRAAx] le N M) : Γ ⊢[PRAAx] regularBound B N M s x := by
  have member := nested_between B nested order (center_member B M x valid)
  have radius := radius_at B N s x radii
  exact .andI
    (distance_positive_at B (center B M x) (center B N x) x positive
      (.andE₁ (center_valid_at B M x valid)) (.andE₁ (center_valid_at B N x valid)))
    (scaled_rational_bound (.andE₁ radius) (.andE₂ member) (.andE₂ radius))

/-- A point is compatible with the particular nested-ball certificate. -/
def compatible (B : BallCodes) (y x : PTm n) : Fm PTm n :=
  .all (ball B (var 0) (Syn.shift y) (Syn.shift x))

/-- A compatible solution has the advertised rate of agreement with the centers. -/
theorem compatible_agreement (B : BallCodes) (N y s x : PTm n)
    (valid : Γ ⊢[PRAAx] centersValid B x)
    (positive : Γ ⊢[PRAAx] distancesPositive B x)
    (radii : Γ ⊢[PRAAx] radiiDecay B s x)
    (member : Γ ⊢[PRAAx] compatible B y x) :
    Γ ⊢[PRAAx] lt zero (dd B y (center B N x) x) ⋏
      le (pw two (N + s) * dn B y (center B N x) x) (dd B y (center B N x) x) := by
  have atN : Γ ⊢[PRAAx] ball B N y x := by
    simpa only [compatible, subst_ball, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift] using Prf.allE N member
  have radius := radius_at B N s x radii
  exact .andI
    (distance_positive_at B y (center B N x) x positive (.andE₁ atN)
      (.andE₁ (center_valid_at B N x valid)))
    (scaled_rational_bound (.andE₁ radius) (.andE₂ atN) (.andE₂ radius))

/-- Variables are `N`, `M`, the precision shift and the input parameter. -/
abbrev nestedNameFormula (B : BallCodes) : Fm PTm 4 :=
  centersValid B (var 3) ⟶ distancesPositive B (var 3) ⟶ radiiDecay B (var 2) (var 3) ⟶
    nesting B (var 3) ⟶ le (var 0) (var 1) ⟶ regularBound B (var 0) (var 1) (var 2) (var 3)

/-- The universally closed corrected regular-name endpoint. -/
theorem nested_name (B : BallCodes) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (nestedNameFormula B) := by
  apply closeUniv 4
  refine .impI (.impI (.impI (.impI (.impI ?_))))
  exact center_cauchy B _ _ _ _ Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk
    Prf.hyp1.wk Prf.hyp1 Prf.hyp0

/-- Variables are the index, the compatible solution, the shift and the input parameter. -/
abbrev compatibleNameFormula (B : BallCodes) : Fm PTm 4 :=
  centersValid B (var 3) ⟶ distancesPositive B (var 3) ⟶ radiiDecay B (var 2) (var 3) ⟶
    compatible B (var 1) (var 3) ⟶
      (lt zero (dd B (var 1) (center B (var 0) (var 3)) (var 3)) ⋏
        le (pw two (var 0 + var 2) * dn B (var 1) (center B (var 0) (var 3)) (var 3))
          (dd B (var 1) (center B (var 0) (var 3)) (var 3)))

theorem compatible_name (B : BallCodes) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (compatibleNameFormula B) := by
  apply closeUniv 4
  refine .impI (.impI (.impI (.impI ?_)))
  exact compatible_agreement B _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0

#print axioms nested_name
#print axioms compatible_name

end LeanProofs.IPRA.Foundations.NestedRegions
