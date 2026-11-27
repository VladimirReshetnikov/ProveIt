import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneSigned
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate

/-!
# Extend a locally Lipschitz rational name to the right half-plane

A certified margin and disk give a uniform local variation bound for the
rational evaluator. The extension samples the actual input at a computed
precision and evaluates at the resulting signed rational chart. Half of each
output error pays for the input, and half pays for the rational evaluation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianNamedRightHalfPlaneLift

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianNamedRightHalfPlane (precision radius threshold)
open GaussianNamedRightHalfPlaneSigned (certificate point point_distance)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

structure RationalMap where
  evaluator : PR 2
  rationalData : PR 1
  gain : PR 2
  variation : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (x y R K E D : PTm m),
    (Δ ⊢[PRAAx] certificate x R K) → (Δ ⊢[PRAAx] certificate y R K) →
    (Δ ⊢[PRAAx] le one D) → (Δ ⊢[PRAAx] le (ap2 gain R K * E) D) →
    (Δ ⊢[PRAAx] distanceBounded (point x) (point y) E D) →
    (Δ ⊢[PRAAx] independentRate evaluator evaluator (ap1 rationalData x) (ap1 rationalData y)
      (ap2 gain R K * E) D)

def source (f : PR 2) (x M R : PTm n) : Fm PTm n :=
  GaussianNamedRightHalfPlane.source f x M ⋏ le (radius f x) R

def clock (map : RationalMap) (p M R : PTm n) : PTm n :=
  precision (exponent (ap2 map.gain R (two*M)) (succ p)) M

def frozenData (map : RationalMap) (f : PR 2) (k x : PTm n) : PTm n :=
  ap1 map.rationalData (ap2 f k x)

def sample (map : RationalMap) (f : PR 2) (p x M R : PTm n) : PTm n :=
  ap2 map.evaluator (succ p) (frozenData map f (clock map p M R) x)

def data (x M R : PTm n) : PTm n := pairT x (pairT M R)

def nameF (map : RationalMap) (f : PR 2) : PR 2 := PTm.toPR
  (sample map f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

ipra_subst source [GaussianNamedRightHalfPlane.source, GaussianNamedRightHalfPlane.certificate, GaussianNamedRightHalfPlane.marginPoint, GaussianNamedRightHalfPlane.radius]

ipra_subst clock [GaussianNamedRightHalfPlane.precision, two]

@[simp] theorem subst_frozenData {m : ℕ} (σ : Fin n → PTm m) (map : RationalMap) (f : PR 2) (k x : PTm n) :
    Syn.subst σ (frozenData map f k x) = frozenData map f (Syn.subst σ k) (Syn.subst σ x) := by
  simp [frozenData, ap1]
  funext i
  fin_cases i
  rfl

ipra_subst sample

ipra_subst data

theorem sample_at (map : RationalMap) (f : PR 2) (p x M R : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF map f) p (data x M R) ≐ sample map f p x M R := by
  let X := data x M R
  have raw : Γ ⊢[PRAAx] ap2 (nameF map f) p X ≐ sample map f p (fstT X) (fstT (sndT X)) (sndT (sndT X)) := by
    simpa [nameF, ap2] using
      toPR_eq (Γ := Γ) (sample map f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,X]
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (sample map f (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![p,fstT X,fstT (sndT X),sndT (sndT X)]) (σ' := ![p,x,M,R])
    (fun i => by
      fin_cases i
      exact .eqRefl _
      exact fst_pair _ _
      exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
  exact raw.eqTrans (by simpa using fields)

theorem clock_margin (map : RationalMap) (p M R : PTm n) :
    Γ ⊢[PRAAx] le (threshold M) (clock map p M R) := by
  exact le_congr (zero_add _).eqSymm (.eqRefl _) (le_add_left _ _)

private theorem unit_step (p : PTm n) : Γ ⊢[PRAAx] unit (succ p) ≐ two * unit p :=
  (pw_succ two p).eqTrans (mul_comm _ _)

theorem gain_clock_budget (L p M : PTm n) :
    Γ ⊢[PRAAx] le (two * L * unit p) (unit (precision (exponent L (succ p)) M)) := by
  have inputClock : Γ ⊢[PRAAx] le (exponent L (succ p)) (precision (exponent L (succ p)) M) :=
    le_add_right _ _
  have h := le_trans (query_budget (Γ := Γ) L (succ p)) (unit_monotone inputClock)
  exact le_congr (by
    apply deriveNat
    ipra_simps
    rw [natEq (unit_step (Γ := Γ) p)]
    ipra_simps
    ring) (.eqRefl _) h

theorem clock_budget (map : RationalMap) (p M R : PTm n) :
    Γ ⊢[PRAAx] le (two * ap2 map.gain R (two*M) * unit p) (unit (clock map p M R)) :=
  gain_clock_budget (ap2 map.gain R (two*M)) p M

theorem late_certificate (f : PR 2) (x k M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R)
    (hk : Γ ⊢[PRAAx] le (threshold M) k) :
    Γ ⊢[PRAAx] certificate (ap2 f k x) R (two*M) := by
  have hc := GaussianNamedRightHalfPlaneSigned.actual_late f x M k h.andE₁ hk
  have hr := le_mul_mono h.andE₂ (le_refl (GaussianNamedRightHalfPlaneSigned.denominator (ap2 f k x)))
  exact .andI (.andI hc.andE₁.andE₁ (le_trans hc.andE₁.andE₂ (le_mul_mono hr hr))) hc.andE₂

theorem variation_guard (L U V p q : PTm n)
    (hp : Γ ⊢[PRAAx] le (two*L*unit p) U) (hq : Γ ⊢[PRAAx] le (two*L*unit q) V) :
    Γ ⊢[PRAAx] le (L*(U+V)) (U*V) := by
  have hu : Γ ⊢[PRAAx] le (two*L) U :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (two*L)) (unit_positive p))) hp
  have hv : Γ ⊢[PRAAx] le (two*L) V :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (two*L)) (unit_positive q))) hq
  ipra_le sl hu * sl hv + 𝔞(L) * (sl hu + sl hv)

theorem precision_budget (L U V p q : PTm n)
    (hp : Γ ⊢[PRAAx] le (two*L*unit p) U) (hq : Γ ⊢[PRAAx] le (two*L*unit q) V) :
    Γ ⊢[PRAAx] le (rateNumerator (L*(U+V)) (U*V) (succ p) (succ q) * (unit p*unit q))
      ((unit p+unit q) * rateDenominator (U*V) (succ p) (succ q)) := by
  let P := unit p
  let Q := unit q
  have h : Γ ⊢[PRAAx] le ((L*(U+V)*(two*P)*(two*Q)+U*V*(two*P+two*Q))*(P*Q))
      ((P+Q)*(U*V*(two*P)*(two*Q))) := by
    change Γ ⊢[PRAAx] le (two*L*P) U at hp
    change Γ ⊢[PRAAx] le (two*L*Q) V at hq
    ipra_le 2*𝔞(P)*𝔞(Q)*(𝔞(V)*𝔞(Q)*sl hp+𝔞(U)*𝔞(P)*sl hq)
  have hp' := natEq (unit_step (Γ := Γ) p)
  have hq' := natEq (unit_step (Γ := Γ) q)
  apply le_congr ?_ ?_ h
  · dsimp only [P, Q, rateNumerator]
    apply deriveNat
    ipra_simps
    rw [hp', hq']
  · dsimp only [P, Q, rateDenominator]
    apply deriveNat
    ipra_simps
    rw [hp', hq']

private theorem late_input_rate (map : RationalMap) (f g : PR 2) (p q k l x y M R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hg : Γ ⊢[PRAAx] source g y M R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (clock map p M R) k) (hl : Γ ⊢[PRAAx] le (clock map q M R) l) :
    Γ ⊢[PRAAx] independentRate map.evaluator map.evaluator (frozenData map f k x) (frozenData map g l y)
      (ap2 map.gain R (two*M)*(unit k+unit l)) (unit k*unit l) := by
  let U := unit k
  let V := unit l
  let L := ap2 map.gain R (two*M)
  have cap₁ := le_trans (clock_budget (Γ := Γ) map p M R) (unit_monotone hk)
  have cap₂ := le_trans (clock_budget (Γ := Γ) map q M R) (unit_monotone hl)
  have h₁ := late_certificate f x k M R hf (le_trans (clock_margin map p M R) hk)
  have h₂ := late_certificate g y l M R hg (le_trans (clock_margin map q M R) hl)
  have hD : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ (unit_positive k) (unit_positive l)
  have hinput := point_distance _ _ _ _ h₁.andE₁.andE₁.andE₁.andE₁ h₂.andE₁.andE₁.andE₁.andE₁
    hD (cross_at f g x y k l he)
  exact map.variation _ _ R (two*M) (U+V) (U*V) h₁ h₂ hD (variation_guard L U V p q cap₁ cap₂) hinput

theorem late_observations (map : RationalMap) (f g : PR 2) (p q k l x y M R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hg : Γ ⊢[PRAAx] source g y M R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (clock map p M R) k) (hl : Γ ⊢[PRAAx] le (clock map q M R) l) :
    Γ ⊢[PRAAx] distanceBounded (ap2 map.evaluator (succ p) (frozenData map f k x))
      (ap2 map.evaluator (succ q) (frozenData map g l y)) (unit p+unit q) (unit p*unit q) := by
  let U := unit k
  let V := unit l
  let L := ap2 map.gain R (two*M)
  have cap₁ := le_trans (clock_budget (Γ := Γ) map p M R) (unit_monotone hk)
  have cap₂ := le_trans (clock_budget (Γ := Γ) map q M R) (unit_monotone hl)
  have hD : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ (unit_positive k) (unit_positive l)
  have hr := late_input_rate map f g p q k l x y M R hf hg he hk hl
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hD)
    (positive_product _ _ (unit_positive p) (unit_positive q)) (precision_budget L U V p q cap₁ cap₂)
    (rate_at map.evaluator map.evaluator (frozenData map f k x) (frozenData map g l y) _ _ (succ p) (succ q) hr)

theorem proper (map : RationalMap) (f g : PR 2) (x y M R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hg : Γ ⊢[PRAAx] source g y M R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF map f) (nameF map g) (data x M R) (data y M R) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hs : Δ ⊢[PRAAx] source f (sh x) (sh M) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have ht : Δ ⊢[PRAAx] source g (sh y) (sh M) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift.shift
  have hei : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  have h := late_observations map f g p q (clock map p (sh M) (sh R)) (clock map q (sh M) (sh R))
    (sh x) (sh y) (sh M) (sh R) hs ht hei (le_refl _) (le_refl _)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh,p,q,Δ] using
    distance_congr (sample_at map f p (sh x) (sh M) (sh R)).eqSymm
      (sample_at map g q (sh y) (sh M) (sh R)).eqSymm (.eqRefl _) (.eqRefl _) h

theorem name_regular (map : RationalMap) (f : PR 2) (x M R : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R) : Γ ⊢[PRAAx] pointCN (nameF map f) (data x M R) :=
  proper map f f x x M R h h (cross_refl f x h.andE₁.andE₁)

theorem frozen_budget (L U V p q s : PTm n)
    (hp : Γ ⊢[PRAAx] le (two*L*unit p) U) (hs : Γ ⊢[PRAAx] le (two*L*unit s) V) :
    Γ ⊢[PRAAx] le (rateNumerator (L*(U+V)) (U*V) (succ p) q * rateDenominator (unit s) p q)
      (rateNumerator one (unit s) p q * rateDenominator (U*V) (succ p) q) := by
  let P := unit p
  let Q := unit q
  let S := unit s
  have h : Γ ⊢[PRAAx] le ((L*(U+V)*(two*P)*Q+U*V*(two*P+Q))*(S*P*Q))
      ((one*P*Q+S*(P+Q))*(U*V*(two*P)*Q)) := by
    change Γ ⊢[PRAAx] le (two*L*P) U at hp
    change Γ ⊢[PRAAx] le (two*L*S) V at hs
    ipra_le 𝔞(P)*𝔞(Q)^2*(𝔞(V)*𝔞(S)*sl hp+𝔞(U)*𝔞(P)*sl hs+𝔞(U)*𝔞(V)*𝔞(P))
  have hp' := natEq (unit_step (Γ := Γ) p)
  apply le_congr ?_ ?_ h
  · dsimp only [P, Q, S, rateNumerator, rateDenominator]
    apply deriveNat
    ipra_simps
    rw [hp']
  · dsimp only [P, Q, S, rateNumerator, rateDenominator]
    apply deriveNat
    ipra_simps
    rw [hp']

theorem frozen_observations (map : RationalMap) (f : PR 2) (p q s k x M R : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R) (hk : Γ ⊢[PRAAx] le (clock map s M R) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF map f) p (data x M R))
      (ap2 map.evaluator q (frozenData map f k x))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  let t := clock map p M R
  let u := frozenData map f t x
  let v := frozenData map f k x
  let U := unit t
  let V := unit k
  let L := ap2 map.gain R (two*M)
  have cap₁ := clock_budget (Γ := Γ) map p M R
  have cap₂ := le_trans (clock_budget (Γ := Γ) map s M R) (unit_monotone hk)
  have hr := late_input_rate map f f p s t k x x M R h h (cross_refl f x h.andE₁.andE₁) (le_refl _) hk
  have hD : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ (unit_positive t) (unit_positive k)
  have near := distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hD)
    (denominator_positive _ _ _ (unit_positive s)) (frozen_budget L U V p q s cap₁ cap₂)
    (rate_at map.evaluator map.evaluator u v _ _ (succ p) q hr)
  exact distance_congr (sample_at map f p x M R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) near

theorem frozen_rate (map : RationalMap) (f : PR 2) (s k x M R : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R) (hk : Γ ⊢[PRAAx] le (clock map s M R) k) :
    Γ ⊢[PRAAx] independentRate (nameF map f) map.evaluator
      (data x M R) (frozenData map f k x) one (unit s) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have hs : Δ ⊢[PRAAx] source f (sh x) (sh M) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.shift
  have hks : Δ ⊢[PRAAx] le (clock map (sh s) (sh M) (sh R)) (sh k) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hk.shift.shift
  simpa only [independentRate, subst_data, subst_frozenData, GaussianCoefficientNameBounds.subst_unit, one,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift, sh, Δ] using
    frozen_observations map f (var 1) (var 0) (sh s) (sh k) (sh x) (sh M) (sh R) hs hks

theorem actual_named_right_half_plane_rational_lift_closed (map : RationalMap) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶ pointCN (nameF map f) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular map f _ _ _ Prf.hyp0))

theorem actual_named_right_half_plane_frozen_rate_closed (map : RationalMap) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f (var 0) (var 1) (var 2) ⟶ le (clock map (var 3) (var 1) (var 2)) (var 4) ⟶
        independentRate (nameF map f) map.evaluator (data (var 0) (var 1) (var 2))
          (frozenData map f (var 4) (var 0)) one (unit (var 3))) :=
  closeUniv 5 (.impI (.impI (frozen_rate map f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedRightHalfPlaneLift
