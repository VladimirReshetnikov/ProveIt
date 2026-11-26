import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.GaussianBarnesCanonicalThirdLogarithmCauchy

/-!
# Cofinal name for the actual positive Barnes cubic logarithm series

At every precision p, the program returns the original prefix through
the zero-based index 4*2^p. The first row supplies a common positive
lower bound; for x≥1 the bound 2/x²+2/x holds at every clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdLogarithmCofinal

open_ipra
open LeanProofs.IPRA.Common (mul_le_mul)
open GaussianBarnesCanonicalThirdLogarithmCauchy (gain ordered_prefix_error)
open GaussianBarnesCanonicalThirdLogarithmRows (row)
open GaussianBarnesCanonicalThirdLogarithmSeries (decayNumerator value)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianPositiveRealArithmetic (positive positive_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalReciprocal (bound_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (A B : PTm n) : Fm PTm n := le one A ⋏ le one B

def data (A B : PTm n) : PTm n := pairT A B

def cutoff (p : PTm n) : PTm n := gain*unit p

def sample (p A B : PTm n) : PTm n := value A B (succ (cutoff p))

def nameF : PR 2 := PTm.toPR (sample (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    (source A B).subst σ = source (Syn.subst σ A) (Syn.subst σ B) := by simp [source,one]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (data A B) = data (Syn.subst σ A) (Syn.subst σ B) := by simp [data]

@[simp] theorem subst_cutoff {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (cutoff p) = cutoff (Syn.subst σ p) := by simp [cutoff]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p A B : PTm n) :
    Syn.subst σ (sample p A B) = sample (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by simp [sample]

theorem sample_at (p A B : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data A B) ≐ sample p A B := by
  let d := data A B
  have raw : Γ ⊢[PRAAx] ap2 nameF p d ≐ sample p (fstT d) (sndT d) := by
    simpa [nameF,ap2] using toPR_eq (Γ := Γ)
      (sample (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,d]
  have decode : Γ ⊢[PRAAx] sample p (fstT d) (sndT d) ≐ sample p A B := by
    dsimp only [d,data]
    ipra_congr (sample (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl _, fst_pair A B, snd_pair A B]
  exact raw.eqTrans decode

theorem cutoff_positive (p : PTm n) : Γ ⊢[PRAAx] le one (cutoff p) :=
  positive_product gain (unit p) (positive_product two two (le_succ_self one) (le_succ_self one)) (unit_positive p)

theorem late_prefix_error (p A B r : PTm n) (h : Γ ⊢[PRAAx] source A B)
    (hr : Γ ⊢[PRAAx] le (cutoff p) r) :
    Γ ⊢[PRAAx] distanceBounded (value A B (succ r)) (ap2 nameF p (data A B)) one (unit p) := by
  have fit : Γ ⊢[PRAAx] le (gain*unit p) (one*cutoff p) :=
    le_congr (.eqRefl _) (one_mul _).eqSymm (le_refl _)
  exact distance_congr (.eqRefl _) (sample_at p A B).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (cutoff_positive p) (unit_positive p) fit
      (ordered_prefix_error A B (cutoff p) r h.andE₁ h.andE₂ (cutoff_positive p) hr))

theorem observations (p q A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B)) (ap2 nameF q (data A B))
      (unit p+unit q) (unit p*unit q) := by
  let U := unit p
  let V := unit q
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have hv : Γ ⊢[PRAAx] le one V := unit_positive q
  have hD := positive_product U V hu hv
  refine (le_total p q).orE ?_ ?_
  · let Δ := le p q :: Γ
    have pq : Δ ⊢[PRAAx] le p q := Prf.hyp0
    have fit : Δ ⊢[PRAAx] le (cutoff p) (cutoff q) :=
      mul_le_mul (le_refl gain) (GaussianExponentialReference.unit_monotone pq)
    have raw := late_prefix_error p A B (cutoff q) h.wk fit
    have d := distance_congr (sample_at (Γ := Δ) q A B).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) raw
    have budget : Δ ⊢[PRAAx] le (one*(U*V)) ((U+V)*U) := le_of_eq_add (d := U*U) (by ipra_ring)
    exact distance_radius_mono _ _ _ _ _ _ hu.wk hD.wk budget (distance_symmetric _ _ _ _ hu.wk d)
  · let Δ := le q p :: Γ
    have qp : Δ ⊢[PRAAx] le q p := Prf.hyp0
    have fit : Δ ⊢[PRAAx] le (cutoff q) (cutoff p) :=
      mul_le_mul (le_refl gain) (GaussianExponentialReference.unit_monotone qp)
    have raw := late_prefix_error q A B (cutoff p) h.wk fit
    have d := distance_congr (sample_at (Γ := Δ) p A B).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) raw
    have budget : Δ ⊢[PRAAx] le (one*(U*V)) ((U+V)*V) := le_of_eq_add (d := V*V) (by ipra_ring)
    exact distance_radius_mono _ _ _ _ _ _ hv.wk hD.wk budget d

theorem regular (A B : PTm n) (h : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx] pointCN nameF (data A B) := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have h' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh A) (sh B) := by
    simpa only [Fm.shift,Syn.shift,sh,subst_source] using h.shift.shift
  simpa only [pointCN,Syn.shift,sh,subst_data,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit] using
    observations (var 1) (var 0) (sh A) (sh B) h'

theorem positive_sample (p A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] positive (ap2 nameF p (data A B)) :=
  positive_congr (sample_at p A B).eqSymm
    (GaussianBarnesCanonicalThirdLogarithmSeries.interval_positive A B _ _ h.andE₁ h.andE₂)

theorem first_floor (p A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT (row A B ConciseIPRA.PTm.zero)) (fstT (ap2 nameF p (data A B))) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (congrFst (sample_at p A B)).eqSymm
    (GaussianBarnesCanonicalThirdLogarithmSeries.first_floor A B (cutoff p) h.andE₁ h.andE₂)

theorem decay_bound (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hBA : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data A B)) (decayNumerator A B) (A*A) :=
  bound_congr (sample_at p A B).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianBarnesCanonicalThirdLogarithmSeries.decay_bound A B (cutoff p) hB hBA)

theorem actual_Barnes_cubic_logarithm_cofinal_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (source (var 0) (var 1) ⟶ pointCN nameF (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (regular _ _ Prf.hyp0))

theorem actual_Barnes_cubic_logarithm_cofinal_decay_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let p := var 0
       let A := var 1
       let B := var 2
       (le one B ⋏ le B A) ⟶ bounded (ap2 nameF p (data A B)) (decayNumerator A B) (A*A)) :=
  closeUniv 3 (.impI (decay_bound _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdLogarithmCofinal
