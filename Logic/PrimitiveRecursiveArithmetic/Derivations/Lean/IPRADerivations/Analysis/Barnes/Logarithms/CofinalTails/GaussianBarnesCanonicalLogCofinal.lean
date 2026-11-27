import IPRADerivations.Analysis.Barnes.Logarithms.CofinalTails.GaussianBarnesCanonicalLogRoundedTail
import IPRADerivations.Analysis.Barnes.Logarithms.CofinalTails.GaussianBarnesCanonicalLogSchedule

/-!
# The cofinal name of the original Barnes logarithmic tail

The retained rounded rows run from the fixed head boundary through the
corrected Barnes cutoff. At later cutoff and query, the common rows
pay only the original rounding/readback error; the remaining rows
satisfy the sharp Barnes tail bound. This yields a regular PR name.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogCofinal

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalLogRoundedTail (value rounding_error)
open GaussianBarnesCanonicalLogSchedule (initial endpoint length gain clock initial_length)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qadd)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianReconstructionRoots (norm_from_distance distance_zero_iff)
open DyadicComplexLogarithm (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "tailSource" => GaussianBarnesCanonicalLogTail.source
local notation "dyadic" => GaussianCoefficientNameBounds.unit
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk Γ t)

def source (z R B : PTm n) : Fm PTm n := le one B ⋏ ComplexLogarithmRemainder.bounded z (R*B)

def data (z R B : PTm n) : PTm n := pairT z (pairT R B)

def sample (p z R B : PTm n) : PTm n := value (clock p R) z R B (initial R) (length p R)

def nameF : PR 2 := PTm.toPR
  (sample (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    (source z R B).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [source,one]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (data z R B) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [data]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p z R B : PTm n) :
    Syn.subst σ (sample p z R B) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [sample]

theorem sample_at (p z R B : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R B) ≐ sample p z R B := by
  simpa [nameF, data, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 2) (sample (var 0) (var 1) (var 2) (var 3)) p ![z, R, B])

private theorem initial_source (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] tailSource z R B (initial R) :=
  .andI h.andE₁ (.andI (GaussianBarnesCanonicalLogSchedule.initial_positive R)
    (.andI h.andE₂ (GaussianBarnesCanonicalLogSchedule.initial_radius R)))

private theorem suffix_source (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] tailSource z R B (endpoint p R) :=
  .andI h.andE₁ (.andI (GaussianBarnesCanonicalLogSchedule.endpoint_positive p R)
    (.andI h.andE₂ (le_trans (GaussianBarnesCanonicalLogSchedule.initial_radius R)
      (GaussianBarnesCanonicalLogSchedule.initial_le_endpoint p R))))

private theorem pay_clock {x y A : PTm n} (p q R : PTm n)
    (hpq : Γ ⊢[PRAAx] le p q) (hA : Γ ⊢[PRAAx] le A (gain q R))
    (h : Γ ⊢[PRAAx] distanceBounded x y A (unit (clock q R))) :
    Γ ⊢[PRAAx] distanceBounded x y one (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive _) (GaussianLocalLogarithmName.unit_positive _)
    (le_trans (le_mul_mono hA (GaussianExponentialReference.unit_monotone (add_le_add_right (num 4) hpq)))
      (le_congr (.eqRefl _) (one_mul _).eqSymm (GaussianBarnesCanonicalLogSchedule.clock_budget q R))) h

private theorem row_budget (m r E : PTm n) (h : Γ ⊢[PRAAx] m+r ≐ E) :
    Γ ⊢[PRAAx] le (r*(num 5*(m+r))) (num 5*E*E) := by
  have bound : Γ ⊢[PRAAx] le r E := le_congr (.eqRefl _) h (le_add_left r m)
  have first : Γ ⊢[PRAAx] le (num 5*r) (num 5*E) :=
    mul_le_mul_left (num 5) bound
  have e : Γ ⊢[PRAAx] (num 5*r)*E ≐ r*(num 5*(m+r)) :=
    (congrMul (.eqRefl _) h.eqSymm).eqTrans (by ipra_ring)
  exact le_congr e (.eqRefl _) (mul_le_mul_right E first)

theorem ordered_observations (p q z R B : PTm n) (hs : Γ ⊢[PRAAx] source z R B) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (sample q z R B) (sample p z R B) (num 3) (unit p) := by
  let n₀ := initial R
  let a := length p R
  let b := length q R
  let r := monus b a
  let N := endpoint p R
  let M := endpoint q R
  let u := clock p R
  let v := clock q R
  let U := unit p
  let x := value v z R B n₀ a
  let y := value v z R B N r
  let t := GaussianBarnesCanonicalLogTail.value z B N r (DyadicComplexLogarithm.precision v)
  have hU : Γ ⊢[PRAAx] le one U := GaussianLocalLogarithmName.unit_positive p
  have h₂ := initial_length (Γ := Γ) p R
  have h₃ := initial_length (Γ := Γ) q R
  have len := GaussianBarnesCanonicalLogSchedule.length_monotone p q R hpq
  have read : Γ ⊢[PRAAx] a+r ≐ b := (eq_add_of_le len).eqSymm
  have mount : Γ ⊢[PRAAx] N+r ≐ M :=
    (congrAdd h₂.eqSymm (.eqRefl r)).eqTrans
      ((add_assoc _ _ _).eqTrans ((congrAdd (.eqRefl n₀) read).eqTrans h₃))
  have regular := GaussianBarnesCanonicalLogRoundedTail.ordered_distance u v z R B n₀ a
    (initial_source z R B hs) (GaussianBarnesCanonicalLogSchedule.clock_monotone p q R hpq)
  have common : Γ ⊢[PRAAx] distanceBounded x (sample p z R B) one U :=
    pay_clock p p R (le_refl p) (row_budget n₀ a N h₂) regular
  have hRows : Γ ⊢[PRAAx] le (r*(two*(N+r))) (gain q R) :=
    le_trans (le_mul_mono (le_refl r) (mul_le_mul_right (N+r)
      (le_of_eq_add (d := num 3) (by ipra_ring)))) (row_budget N r M mount)
  have hTail := suffix_source p z R B hs
  have discrepancy : Γ ⊢[PRAAx] distanceBounded y t one U :=
    pay_clock p q R hpq hRows (rounding_error v z R B N r hTail)
  have hat := GaussianBarnesCanonicalLogTail.tail_bound z R B N r (DyadicComplexLogarithm.precision v) hTail
  have d := GaussianBarnesCanonicalLogTail.tail_denominator_positive N hTail.andE₂.andE₁
  have exactBound : Γ ⊢[PRAAx] bounded t one U :=
    bounded_radius_mono _ _ _ _ _ d hU (GaussianBarnesCanonicalLogSchedule.suffix_budget p R) hat
  have combined := norm_from_distance y t one U one U hU hU discrepancy exactBound
  have radius : Γ ⊢[PRAAx] bounded y two U :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hU hU) hU
      (le_of_eq_add (d := zero) (by ipra_ring)) combined
  have newQuery : Γ ⊢[PRAAx] sample q z R B ≐ qadd x y := by
    have e : Γ ⊢[PRAAx] value v z R B n₀ b ≐ value v z R B n₀ (a+r) := by
      ipra_congr (value (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
        [.eqRefl _, .eqRefl _, .eqRefl _, .eqRefl _, .eqRefl _, read.eqSymm]
    have w : Γ ⊢[PRAAx] value v z R B (n₀+a) r ≐ y := by
      ipra_congr (value (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
        [.eqRefl _, .eqRefl _, .eqRefl _, .eqRefl _, h₂, .eqRefl _]
    exact e.eqTrans ((GaussianBarnesCanonicalLogRoundedTail.split v z R B n₀ a r).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl x) w))
  have canY := GaussianRationalFiniteSum.sum_canonical (Γ := Γ) GaussianBarnesCanonicalLogRoundedTail.body r
    (GaussianBarnesCanonicalLogRoundedTail.data v z R B N)
  have gained : Γ ⊢[PRAAx] distanceBounded (sample q z R B) x two U :=
    bound_congr ((GaussianRationalSyntheticDivision.qsub_congr newQuery (.eqRefl x)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_sub_cancel x y canY)).eqSymm (.eqRefl _) (.eqRefl _) radius
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU gained common)

theorem observations (p q z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B) (sample q z R B) (dyadic p+dyadic q) (dyadic p*dyadic q) := by
  let P := dyadic p
  let Q := dyadic q
  have hD := positive_product P Q (GaussianCoefficientNameBounds.unit_positive (Γ := Γ) p)
    (GaussianCoefficientNameBounds.unit_positive q)
  have cap₁ : Γ ⊢[PRAAx] le (num 3*(P*Q)) ((P+Q)*unit p) := by
    apply le_congr (.eqRefl _) (congrMul (.eqRefl _) (GaussianLocalLogarithmName.unit_factor p)).eqSymm
    dsimp only [P,Q]
    ipra_le 16*𝔞(dyadic p)^2+13*𝔞(dyadic p)*𝔞(dyadic q)
  have cap₂ : Γ ⊢[PRAAx] le (num 3*(P*Q)) ((P+Q)*unit q) := by
    apply le_congr (.eqRefl _) (congrMul (.eqRefl _) (GaussianLocalLogarithmName.unit_factor q)).eqSymm
    dsimp only [P,Q]
    ipra_le 16*𝔞(dyadic q)^2+13*𝔞(dyadic p)*𝔞(dyadic q)
  refine (le_total p q).orE ?_ ?_
  · have u := GaussianLocalLogarithmName.unit_positive (Γ := le p q :: Γ) p
    exact distance_radius_mono _ _ _ _ _ _ u hD.wk cap₁.wk
      (distance_symmetric _ _ _ _ u (ordered_observations p q z R B h.wk Prf.hyp0))
  · exact distance_radius_mono _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive q) hD.wk cap₂.wk
      (ordered_observations q p z R B h.wk Prf.hyp0)

theorem regular (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN nameF (data z R B) := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have h' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  simpa only [pointCN, Syn.shift, sh, subst_data, GaussianEuclideanPointDistance.unit, GaussianCoefficientNameBounds.unit] using
    distance_congr (sample_at (var 1) (sh z) (sh R) (sh B)).eqSymm
      (sample_at (var 0) (sh z) (sh R) (sh B)).eqSymm (.eqRefl _) (.eqRefl _)
      (observations (var 1) (var 0) (sh z) (sh R) (sh B) h')

theorem actual_cofinal_Barnes_logarithm_tail_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 0) (var 1) (var 2) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (regular _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogCofinal
