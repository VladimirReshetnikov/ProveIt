import IPRADerivations.Analysis.Names.GaussianNameEquivalence

/-!
# Independent value normalizers preserve a vanishing observation discrepancy

Two actual PR streams have independent persistent data and regularity moduli.
Their same-precision discrepancy is at most K/2^m. For fixed raw queries r,s,
three finite distances have base radius L/2^r+M/2^s and slack
(L+M+K)/2^m. The proved rational integer-gap slack-removal theorem eliminates
that slack at an actual finite query. No limit or quantified induction is used.

The two separate generic normalizers then give cross-equivalent actual names.
Their original moduli, data, recodes and query exponents are retained. There
is no order or positivity assumption on L,M,K; in particular all may be zero.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianValueNormalizerExtensionality

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (distanceBounded qsub)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder
  (distance_congr distance_radius_mono distance_triangle_same)
open LeanProofs.IPRA.Analysis.GaussianFastValueCut (regular)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The actual diagonal raw-observation envelope, with arbitrary natural K. -/
def rawDiagonal (f g : PR 2) (x y K : PTm n) : Fm PTm n := .all
  (distanceBounded (ap2 f (var 0) (Syn.shift x)) (ap2 g (var 0) (Syn.shift y))
    (Syn.shift K) (unit (var 0)))

def input (f g : PR 2) (L M x y K : PTm n) : Fm PTm n :=
  regular f L x ⋏ (regular g M y ⋏ rawDiagonal f g x y K)

@[simp] theorem subst_rawDiagonal {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2) (x y K : PTm n) :
    (rawDiagonal f g x y K).subst σ =
      rawDiagonal f g (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ K) := by
  simp [rawDiagonal,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2) (L M x y K : PTm n) :
    (input f g L M x y K).subst σ = input f g (Syn.subst σ L) (Syn.subst σ M)
      (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ K) := by simp [input]

theorem raw_diagonal_at (f g : PR 2) (x y K m : PTm n)
    (h : Γ ⊢[PRAAx] rawDiagonal f g x y K) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f m x) (ap2 g m y) K (unit m) := by
  simpa [rawDiagonal] using h.allE m

/-- All three actual distances are put over the same positive denominator.
The numerator identity gives the exact independent-modulus slack. -/
theorem raw_cross_slack (f g : PR 2) (L M x y K r s m : PTm n)
    (hF : Γ ⊢[PRAAx] regular f L x) (hG : Γ ⊢[PRAAx] regular g M y)
    (hDiag : Γ ⊢[PRAAx] rawDiagonal f g x y K) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 f r x) (ap2 g s y))
      (L*unit s+M*unit r) (unit r*unit s) (L+M+K) m := by
  have rm := positive_product (Γ := Γ) _ _ (unit_positive r) (unit_positive m)
  have ms := positive_product (Γ := Γ) _ _ (unit_positive m) (unit_positive s)
  have rs := positive_product (Γ := Γ) _ _ (unit_positive r) (unit_positive s)
  have common := positive_product (Γ := Γ) _ _ rs (unit_positive m)
  have first := distance_radius_mono _ _ _ _
    (L*unit s*(unit r+unit m)) ((unit r*unit s)*unit m) rm common
    (le_of_eq_add (d := zero) (by ipra_ring))
    (GaussianFastValueCut.regular_at f L x r m hF)
  have middle := distance_radius_mono _ _ K (unit m)
    (K*unit r*unit s) ((unit r*unit s)*unit m) (unit_positive m) common
    (le_of_eq_add (d := zero) (by ipra_ring)) (raw_diagonal_at f g x y K m hDiag)
  have last := distance_radius_mono _ _ _ _
    (M*unit r*(unit m+unit s)) ((unit r*unit s)*unit m) ms common
    (le_of_eq_add (d := zero) (by ipra_ring))
    (GaussianFastValueCut.regular_at g M y m s hG)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold unit; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ common
      (distance_triangle_same _ _ _ _ _ _ common first middle) last)

/-- The auxiliary precision is quantified only to feed the already proved
finite integer-gap query. Neither a limit nor a comparison of L,M,K is assumed. -/
theorem raw_cross_bound (f g : PR 2) (L M x y K r s : PTm n)
    (hF : Γ ⊢[PRAAx] regular f L x) (hG : Γ ⊢[PRAAx] regular g M y)
    (hDiag : Γ ⊢[PRAAx] rawDiagonal f g x y K) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f r x) (ap2 g s y) (L*unit s+M*unit r) (unit r*unit s) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (L+M+K)
    (positive_product _ _ (unit_positive r) (unit_positive s))
  refine .allI ?_
  have hf : Γ.map Fm.shift ⊢[PRAAx] regular f (Syn.shift L) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianFastValueCut.subst_regular,Syn.shift] using hF.shift
  have hg : Γ.map Fm.shift ⊢[PRAAx] regular g (Syn.shift M) (Syn.shift y) := by
    simpa only [Fm.shift,GaussianFastValueCut.subst_regular,Syn.shift] using hG.shift
  have hd : Γ.map Fm.shift ⊢[PRAAx] rawDiagonal f g (Syn.shift x) (Syn.shift y) (Syn.shift K) := by
    simpa only [Fm.shift,subst_rawDiagonal,Syn.shift] using hDiag.shift
  simpa only [Syn.shift,subst_ap2,GaussianRationalMetric.subst_qsub,subst_unit,
    PTm.subst_add,PTm.subst_mul] using
    raw_cross_slack f g (Syn.shift L) (Syn.shift M) (Syn.shift x) (Syn.shift y) (Syn.shift K)
      (Syn.shift r) (Syn.shift s) (var 0) hf hg hd

/-- Two actual independent query budgets, with no common normalization shift. -/
theorem independent_query_budget (L M k ell : PTm n) : Γ ⊢[PRAAx]
    le ((L*unit (GaussianFastValueCut.exponent M ell)+M*unit (GaussianFastValueCut.exponent L k))*
        (unit k*unit ell))
      ((unit k+unit ell)*(unit (GaussianFastValueCut.exponent L k)*unit (GaussianFastValueCut.exponent M ell))) := by
  have left := mul_le_mul_right (unit (GaussianFastValueCut.exponent M ell)*unit ell)
    (GaussianFastValueCut.query_budget (Γ := Γ) L k)
  have right := mul_le_mul_right (unit (GaussianFastValueCut.exponent L k)*unit k)
    (GaussianFastValueCut.query_budget (Γ := Γ) M ell)
  exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ left right)

theorem normalized_value_bound (f g : PR 2) (L M x y K k ell : PTm n)
    (hF : Γ ⊢[PRAAx] regular f L x) (hG : Γ ⊢[PRAAx] regular g M y)
    (hDiag : Γ ⊢[PRAAx] rawDiagonal f g x y K) : Γ ⊢[PRAAx]
    distanceBounded (GaussianFastValueCut.value f L x k) (GaussianFastValueCut.value g M y ell)
      (unit k+unit ell) (unit k*unit ell) := by
  have positive := positive_product (Γ := Γ) _ _
    (unit_positive (GaussianFastValueCut.exponent L k))
    (unit_positive (GaussianFastValueCut.exponent M ell))
  exact distance_radius_mono _ _ _ _ _ _ positive
    (positive_product _ _ (unit_positive k) (unit_positive ell)) (independent_query_budget L M k ell)
    (GaussianFastValueCut.recode_distance_bound _ _ _ _ positive
      (raw_cross_bound f g L M x y K (GaussianFastValueCut.exponent L k)
        (GaussianFastValueCut.exponent M ell) hF hG hDiag))

theorem normalized_program_bound (f g : PR 2) (L M x y K k ell : PTm n)
    (hF : Γ ⊢[PRAAx] regular f L x) (hG : Γ ⊢[PRAAx] regular g M y)
    (hDiag : Γ ⊢[PRAAx] rawDiagonal f g x y K) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 (GaussianFastValueCut.nameF f) k (GaussianFastValueCut.nameData L x))
      (ap2 (GaussianFastValueCut.nameF g) ell (GaussianFastValueCut.nameData M y))
      (unit k+unit ell) (unit k*unit ell) :=
  distance_congr (GaussianFastValueCut.name_at f L x k).eqSymm
    (GaussianFastValueCut.name_at g M y ell).eqSymm (.eqRefl _) (.eqRefl _)
    (normalized_value_bound f g L M x y K k ell hF hG hDiag)

/-- Actual separately normalized PR2 programs are cross-equivalent. -/
theorem normalized_names_equivalent (f g : PR 2) (L M x y K : PTm n)
    (hF : Γ ⊢[PRAAx] regular f L x) (hG : Γ ⊢[PRAAx] regular g M y)
    (hDiag : Γ ⊢[PRAAx] rawDiagonal f g x y K) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent (GaussianFastValueCut.nameF f) (GaussianFastValueCut.nameF g)
      (GaussianFastValueCut.nameData L x) (GaussianFastValueCut.nameData M y) := by
  refine .allI (.allI ?_)
  have hf : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      regular f (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianFastValueCut.subst_regular,Syn.shift] using hF.shift.shift
  have hg : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      regular g (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift y)) := by
    simpa only [Fm.shift,GaussianFastValueCut.subst_regular,Syn.shift] using hG.shift.shift
  have hd : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      rawDiagonal f g (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (Syn.shift (Syn.shift K)) := by
    simpa only [Fm.shift,subst_rawDiagonal,Syn.shift] using hDiag.shift.shift
  simpa only [Syn.shift,GaussianFastValueCut.subst_nameData] using
    normalized_program_bound f g (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift M))
      (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (Syn.shift (Syn.shift K)) (var 1) (var 0) hf hg hd

theorem independent_normalizer_query_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (((var 0)*unit (GaussianFastValueCut.exponent (var 1) (var 3))+
          (var 1)*unit (GaussianFastValueCut.exponent (var 0) (var 2)))*(unit (var 2)*unit (var 3)))
      ((unit (var 2)+unit (var 3))*(unit (GaussianFastValueCut.exponent (var 0) (var 2))*
        unit (GaussianFastValueCut.exponent (var 1) (var 3))))) :=
  closeUniv 4 (independent_query_budget _ _ _ _)

/-- Variables L,M,x,y,K,r,s. The discrepancy K disappears from the fixed-query bound. -/
theorem raw_observation_cross_bound_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input f g (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      distanceBounded (ap2 f (var 5) (var 2)) (ap2 g (var 6) (var 3))
        ((var 0)*unit (var 6)+(var 1)*unit (var 5)) (unit (var 5)*unit (var 6))) :=
  closeUniv 7 (.impI (raw_cross_bound f g _ _ _ _ _ _ _ (.andE₁ Prf.hyp0)
    (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0))))

/-- Variables L,M,x,y,K. All numerical moduli and data remain internal. -/
theorem independently_normalized_names_equivalent_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (input f g (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        GaussianNameEquivalence.crossEquivalent (GaussianFastValueCut.nameF f) (GaussianFastValueCut.nameF g)
          (GaussianFastValueCut.nameData (var 0) (var 2)) (GaussianFastValueCut.nameData (var 1) (var 3))) :=
  closeUniv 5 (.impI (normalized_names_equivalent f g _ _ _ _ _ (.andE₁ Prf.hyp0)
    (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0))))

theorem independent_normalized_program_queries_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (input f g (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        distanceBounded
          (ap2 (GaussianFastValueCut.nameF f) (var 5) (GaussianFastValueCut.nameData (var 0) (var 2)))
          (ap2 (GaussianFastValueCut.nameF g) (var 6) (GaussianFastValueCut.nameData (var 1) (var 3)))
          (unit (var 5)+unit (var 6)) (unit (var 5)*unit (var 6))) :=
  closeUniv 7 (.impI (normalized_program_bound f g _ _ _ _ _ _ _ (.andE₁ Prf.hyp0)
    (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianValueNormalizerExtensionality
