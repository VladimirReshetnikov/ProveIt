import IPRADerivations.Analysis.Trigonometry.Sinc.GaussianNamedSincSamples

/-!
# A primitive-recursive name for sinc

At precision (p), the raw approximation uses the literal factorial
polynomial at precision (2(p+1)) of the original sine approximation.
The extra precision pays for cancellation away from zero. Near zero
the finite polynomial has a quadratic bound around one.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedSinc

open_ipra
open GaussianNamedSincSamples
open GaussianNamedSineTaylor (rawData subst_rawData)
open GaussianRadiusExponentialName (input)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianRationalReciprocal (qone reciprocal)
open GaussianRationalLowerBounds (lower inverse_bound)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianExponentialReference (dyadic_weaken)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def modulus (f : PR 2) (R x : PTm n) : PTm n :=
  two*sineBudget f R x+two*sampleSize f R x+num 6

ipra_subst modulus

theorem sample_near (f : PR 2) (R x p A B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B)
    (hz : Γ ⊢[PRAAx] bounded (argument f R x p) A B) :
    Γ ⊢[PRAAx] distanceBounded (value f R x p) qone (A*A) (two*(B*B)) :=
  distance_congr (value_nonempty f R x p).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianScalarSincTaylorBounds.small_argument_bound _ _ _ (pred (cutoff R p)) hB hAB hz)

private theorem near_pair (f : PR 2) (R x p q : PTm n) (h : Γ ⊢[PRAAx] input f R x)
    (hpq : Γ ⊢[PRAAx] le p q) (hp : Γ ⊢[PRAAx] bounded (argument f R x p) one (unit (succ p))) :
    Γ ⊢[PRAAx] distanceBounded (value f R x p) (value f R x q) (modulus f R x) (unit (succ p)) := by
  let U := unit (succ p)
  let V := unit (clock p)
  let D := two*(U*U)
  let a := argument f R x p
  let b := argument f R x q
  have hU := unit_positive (Γ := Γ) (succ p)
  have hV := unit_positive (Γ := Γ) (clock p)
  have h2U := next_unit_lower (Γ := Γ) p
  have hUU := positive_product U U hU hU
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (le_succ_self one) hUU
  have hgap : Γ ⊢[PRAAx] distanceBounded a b one U :=
    distance_radius_mono a b two V one U hV hU
      (le_congr (.eqRefl _) ((clock_unit p).eqSymm.eqTrans (one_mul V).eqSymm)
        (le_mul_mono h2U (le_refl U))) (argument_pair_error f R x p q h hpq)
  have hbRaw := GaussianReconstructionRoots.norm_from_distance b a one U one U hU hU
    (distance_symmetric a b one U hU hgap) hp
  have hb : Γ ⊢[PRAAx] bounded b two U :=
    bounded_radius_mono b _ _ two U hUU hU (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) hbRaw
  have comparison : Γ ⊢[PRAAx] le ((two*two)*U) (two*D) := by
    dsimp only [D]
    ipra_le 4*𝔞 U*sl hU
  have left := distance_radius_mono _ _ (one*one) D two U hD hU
    (le_trans (by ipra_le 3*𝔞 U) comparison) (sample_near f R x p one U hU hU hp)
  have right := distance_radius_mono _ _ (two*two) D two U hD hU comparison
    (sample_near f R x q two U hU h2U hb)
  exact distance_radius_mono _ _ (two+two) U (modulus f R x) U hU hU
    (by unfold modulus; ipra_le (2*𝔞 (sineBudget f R x)+2*𝔞 (sampleSize f R x)+2)*𝔞 U)
    (distance_triangle_same _ _ _ _ _ _ hU left (distance_symmetric _ _ _ _ hU right))

private theorem away_pair (f : PR 2) (R x p q : PTm n) (h : Γ ⊢[PRAAx] input f R x)
    (hpq : Γ ⊢[PRAAx] le p q) (hp : Γ ⊢[PRAAx] lower (argument f R x p) one (unit (succ p))) :
    Γ ⊢[PRAAx] distanceBounded (value f R x p) (value f R x q) (modulus f R x) (unit (succ p)) := by
  let U := unit (succ p)
  let V := unit (clock p)
  let a := argument f R x p
  let b := argument f R x q
  let sp := value f R x p
  let sq := value f R x q
  let M := sampleSize f R x
  let E := two*sineBudget f R x+two
  let K := E+M*two
  have hU := unit_positive (Γ := Γ) (succ p)
  have hV := unit_positive (Γ := Γ) (clock p)
  have hs : Γ ⊢[PRAAx] distanceBounded (qmul a sp) (qmul b sq) E V :=
    distance_congr (product_at f R x p).eqSymm (product_at f R x q).eqSymm (.eqRefl _) (.eqRefl _)
      (sine_pair_error f R x p q h hpq)
  have hb : Γ ⊢[PRAAx] distanceBounded (qmul b sq) (qmul a sq) (M*two) V :=
    distance_congr (qmul_commutative sq b) (qmul_commutative sq a) (.eqRefl _) (.eqRefl _)
      (multiply_distance sq b a M two V hV (sample_bound f R x q h)
        (distance_symmetric a b two V hV (argument_pair_error f R x p q h hpq)))
  have hab := distance_triangle_same _ _ _ _ _ _ hV hs hb
  have hi := inverse_bound a one U (le_refl one) hU hp
  have hv : Γ ⊢[PRAAx] distanceBounded sp sq (U*K) V :=
    distance_congr (cancel_factor a sp U hU hp (value_canonical f R x p))
      (cancel_factor a sq U hU hp (value_canonical f R x q)) (.eqRefl _) (.eqRefl _)
      (multiply_distance (reciprocal a) (qmul a sp) (qmul a sq) U K V hV hi hab)
  have hKC : Γ ⊢[PRAAx] le K (modulus f R x) := by
    unfold modulus
    dsimp only [K,E,M]
    ipra_le 4
  exact distance_radius_mono _ _ (U*K) V (modulus f R x) U hV hU
    (le_congr (by ipra_ring) (congrMul (.eqRefl _) (clock_unit p).eqSymm)
      (le_mul_mono hKC (le_refl (U*U)))) hv

private theorem sample_pair_le (f : PR 2) (R x p q : PTm n) (h : Γ ⊢[PRAAx] input f R x)
    (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (value f R x p) (value f R x q) (modulus f R x) (unit p) := by
  apply dyadic_weaken _ _ _ p (succ p) (le_succ_self p)
  exact .orE (norm_cases (argument f R x p) one (unit (succ p)))
    (near_pair f R x p q h.wk hpq.wk Prf.hyp0) (away_pair f R x p q h.wk hpq.wk Prf.hyp0)

private theorem sample_pair_ordered (f : PR 2) (R x p q : PTm n)
    (h : Γ ⊢[PRAAx] input f R x) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (value f R x p) (value f R x q)
      (modulus f R x*(unit p+unit q)) (unit p*unit q) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive p) (positive_product _ _ (unit_positive p) (unit_positive q))
    (le_of_eq_add (d := modulus f R x*(unit p*unit p)) (by ipra_ring)) (sample_pair_le f R x p q h hpq)

theorem sample_pair (f : PR 2) (R x p q : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded (value f R x p) (value f R x q)
      (modulus f R x*(unit p+unit q)) (unit p*unit q) := by
  refine .orE (le_total p q) (sample_pair_ordered f R x p q h.wk Prf.hyp0) ?_
  exact distance_congr (.eqRefl _) (.eqRefl _) (congrMul (.eqRefl _) (add_comm _ _)) (mul_comm _ _)
    (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p))
      (sample_pair_ordered f R x q p h.wk Prf.hyp0))

def rawF (f : PR 2) : PR 2 := PTm.toPR
  (value f (fstT (var 1)) (sndT (var 1)) (var 0) : PTm 2)

theorem raw_at (f : PR 2) (R x p : PTm n) :
    Γ ⊢[PRAAx] ap2 (rawF f) p (rawData R x) ≐ value f R x p := by
  have e : Γ ⊢[PRAAx] ap2 (rawF f) p (rawData R x) ≐ value f (fstT (rawData R x)) (sndT (rawData R x)) p := by
    change Γ ⊢[PRAAx] PTm.app (rawF f) ![p,rawData R x] ≐ value f (fstT (rawData R x)) (sndT (rawData R x)) p
    simpa only [rawF, subst_value, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero,
      Matrix.cons_val_one] using toPR_eq (Γ := Γ) (value f (fstT (var 1)) (sndT (var 1)) (var 0) : PTm 2) ![p,rawData R x]
  have r : Γ ⊢[PRAAx] value f (fstT (rawData R x)) (sndT (rawData R x)) p ≐ value f R x p := by
    simpa only [subst_value, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (value f (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![fstT (rawData R x),sndT (rawData R x),p]) (σ' := ![R,x,p])
        (fun j => by fin_cases j; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl p)
  exact e.eqTrans r

theorem raw_regular (f : PR 2) (R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] GaussianFastValueCut.regular (rawF f) (modulus f R x) (rawData R x) := by
  refine .allI (.allI ?_)
  let C := (Γ.map Fm.shift).map Fm.shift
  let Rt := Syn.shift (Syn.shift R)
  let xt := Syn.shift (Syn.shift x)
  have h : C ⊢[PRAAx] input f Rt xt := by
    simpa only [Fm.shift, Syn.shift, GaussianRadiusExponentialName.subst_input, C, Rt, xt] using hf.shift.shift
  have hpair := distance_congr (raw_at f Rt xt (var 1)).eqSymm (raw_at f Rt xt (var 0)).eqSymm
    (.eqRefl _) (.eqRefl _) (sample_pair f Rt xt (var 1) (var 0) h)
  simpa only [Syn.shift, GaussianFastValueCut.regular, subst_rawData, subst_modulus, unit,
    GaussianEuclideanPointDistance.unit, C, Rt, xt] using hpair

def nameF (f : PR 2) : PR 2 := GaussianFastValueCut.nameF (rawF f)
def data (f : PR 2) (R x : PTm n) : PTm n :=
  GaussianFastValueCut.nameData (modulus f R x) (rawData R x)

ipra_subst data

theorem name_regular (f : PR 2) (R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data f R x) :=
  GaussianFastValueCut.name_fast _ _ _ (raw_regular f R x h)

theorem actual_original_named_sinc_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (input f (var 0) (var 1) ⟶ pointCN (nameF f) (data f (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedSinc
