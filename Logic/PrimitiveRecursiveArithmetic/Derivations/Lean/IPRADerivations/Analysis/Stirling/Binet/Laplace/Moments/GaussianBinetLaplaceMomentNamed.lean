import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentSignedVariation
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneLift

/-!
# Original improper Binet moments on regular names with positive real part

The internal natural order is part of the name data. At a precision
computed from the order and the positive margin, project an actual
input observation to its exact real rational part and evaluate the
original improper moment there. The same construction gives independent
readback against every sufficiently late rational observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentNamed

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceMomentSignedVariation (pointData signed_rate)
open GaussianBinetLaplaceMomentVariation (gain gain_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianNamedRightHalfPlane (source precision radius threshold)
open GaussianNamedRightHalfPlaneSigned (point_distance)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk Γ t)
local notation "J" => GaussianBinetLaplaceMomentImproper.nameF

def clock (p M j : PTm n) : PTm n := precision (exponent (gain j (two*M)) (succ p)) M

def frozenData (f : PR 2) (k x j : PTm n) : PTm n := pointData j (ap2 f k x)

def sample (f : PR 2) (p x M j : PTm n) : PTm n := ap2 J (succ p) (frozenData f (clock p M j) x j)

def data (x M j : PTm n) : PTm n := pairT x (pairT M j)

def nameF (f : PR 2) : PR 2 := PTm.toPR
  (sample f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

ipra_subst clock [two]

ipra_subst frozenData

ipra_subst sample

ipra_subst data

theorem sample_at (f : PR 2) (p x M j : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data x M j) ≐ sample f p x M j := by
  let X := data x M j
  have raw : Γ ⊢[PRAAx] ap2 (nameF f) p X ≐ sample f p (fstT X) (fstT (sndT X)) (sndT (sndT X)) := by
    simpa [nameF,ap2] using
      toPR_eq (Γ := Γ) (sample f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,X]
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (sample f (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![p,fstT X,fstT (sndT X),sndT (sndT X)]) (σ' := ![p,x,M,j])
    (fun i => by
      fin_cases i
      exact .eqRefl _
      exact fst_pair _ _
      exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
  exact raw.eqTrans (by simpa using fields)

theorem clock_margin (p M j : PTm n) : Γ ⊢[PRAAx] le (threshold M) (clock p M j) :=
  le_congr (zero_add _).eqSymm (.eqRefl _) (le_add_left _ _)

private theorem unit_step (p : PTm n) : Γ ⊢[PRAAx] unit (succ p) ≐ two * unit p :=
  (pw_succ two p).eqTrans (mul_comm _ _)

theorem clock_budget (p M j : PTm n) : Γ ⊢[PRAAx] le (two*gain j (two*M)*unit p) (unit (clock p M j)) := by
  have hc : Γ ⊢[PRAAx] le (exponent (gain j (two*M)) (succ p)) (clock p M j) := le_add_right _ _
  have h := le_trans (query_budget (Γ := Γ) (gain j (two*M)) (succ p)) (unit_monotone hc)
  exact le_congr (by
    apply deriveNat
    ipra_simps
    rw [natEq (unit_step (Γ := Γ) p)]
    ipra_simps
    ring) (.eqRefl _) h

private theorem variation_guard (L U V p q : PTm n)
    (hp : Γ ⊢[PRAAx] le (two*L*unit p) U) (hq : Γ ⊢[PRAAx] le (two*L*unit q) V) :
    Γ ⊢[PRAAx] le (L*(U+V)) (U*V) := by
  have hu : Γ ⊢[PRAAx] le (two*L) U :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (two*L)) (unit_positive p))) hp
  have hv : Γ ⊢[PRAAx] le (two*L) V :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (two*L)) (unit_positive q))) hq
  ipra_le sl hu * sl hv + 𝔞(L) * (sl hu + sl hv)

private theorem precision_budget (L U V p q : PTm n)
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

private theorem late_input_rate (f g : PR 2) (p q k l x y M j : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M) (hg : Γ ⊢[PRAAx] source g y M)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (clock p M j) k) (hl : Γ ⊢[PRAAx] le (clock q M j) l) :
    Γ ⊢[PRAAx] independentRate J J (frozenData f k x j) (frozenData g l y j)
      (gain j (two*M)*(unit k+unit l)) (unit k*unit l) := by
  let U := unit k
  let V := unit l
  let L := gain j (two*M)
  let R := radius f x+radius g y
  have cap₁ := le_trans (clock_budget (Γ := Γ) p M j) (unit_monotone hk)
  have cap₂ := le_trans (clock_budget (Γ := Γ) q M j) (unit_monotone hl)
  have h₁ := GaussianNamedRightHalfPlaneLift.late_certificate f x k M R (.andI hf (le_add_right _ _))
    (le_trans (clock_margin p M j) hk)
  have h₂ := GaussianNamedRightHalfPlaneLift.late_certificate g y l M R (.andI hg (le_add_left _ _))
    (le_trans (clock_margin q M j) hl)
  have hK := positive_product _ _ (le_succ_self one) hf.andE₂.andE₁
  have hD : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ (unit_positive k) (unit_positive l)
  have guard : Γ ⊢[PRAAx] le (U+V) (U*V) :=
    le_trans (le_congr (one_mul _) (.eqRefl _) (le_mul_mono (gain_positive j (two*M)) (le_refl _)))
      (variation_guard L U V p q cap₁ cap₂)
  have hinput := point_distance _ _ _ _ h₁.andE₁.andE₁.andE₁.andE₁ h₂.andE₁.andE₁.andE₁.andE₁
    hD (cross_at f g x y k l he)
  exact signed_rate j _ _ R (two*M) (U+V) (U*V) h₁ h₂ hK hD guard hinput

theorem late_observations (f g : PR 2) (p q k l x y M j : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M) (hg : Γ ⊢[PRAAx] source g y M)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (clock p M j) k) (hl : Γ ⊢[PRAAx] le (clock q M j) l) :
    Γ ⊢[PRAAx] distanceBounded (ap2 J (succ p) (frozenData f k x j))
      (ap2 J (succ q) (frozenData g l y j)) (unit p+unit q) (unit p*unit q) := by
  let U := unit k
  let V := unit l
  let L := gain j (two*M)
  have cap₁ := le_trans (clock_budget (Γ := Γ) p M j) (unit_monotone hk)
  have cap₂ := le_trans (clock_budget (Γ := Γ) q M j) (unit_monotone hl)
  have hD : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ (unit_positive k) (unit_positive l)
  have hr := late_input_rate f g p q k l x y M j hf hg he hk hl
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hD)
    (positive_product _ _ (unit_positive p) (unit_positive q)) (precision_budget L U V p q cap₁ cap₂)
    (rate_at J J (frozenData f k x j) (frozenData g l y j) _ _ (succ p) (succ q) hr)

theorem proper (f g : PR 2) (x y M j : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M) (hg : Γ ⊢[PRAAx] source g y M)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x M j) (data y M j) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hs : Δ ⊢[PRAAx] source f (sh x) (sh M) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have ht : Δ ⊢[PRAAx] source g (sh y) (sh M) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift.shift
  have hei : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  have h := late_observations f g p q (clock p (sh M) (sh j)) (clock q (sh M) (sh j))
    (sh x) (sh y) (sh M) (sh j) hs ht hei (le_refl _) (le_refl _)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh,p,q,Δ] using
    distance_congr (sample_at f p (sh x) (sh M) (sh j)).eqSymm
      (sample_at g q (sh y) (sh M) (sh j)).eqSymm (.eqRefl _) (.eqRefl _) h

theorem name_regular (f : PR 2) (x M j : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x M j) :=
  proper f f x x M j h h (cross_refl f x h.andE₁)

private theorem frozen_budget (L U V p q s : PTm n)
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

theorem frozen_observations (f : PR 2) (p q s k x M j : PTm n)
    (h : Γ ⊢[PRAAx] source f x M) (hk : Γ ⊢[PRAAx] le (clock s M j) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x M j)) (ap2 J q (frozenData f k x j))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  let t := clock p M j
  let u := frozenData f t x j
  let v := frozenData f k x j
  let U := unit t
  let V := unit k
  let L := gain j (two*M)
  have cap₁ := clock_budget (Γ := Γ) p M j
  have cap₂ := le_trans (clock_budget (Γ := Γ) s M j) (unit_monotone hk)
  have hr := late_input_rate f f p s t k x x M j h h (cross_refl f x h.andE₁) (le_refl _) hk
  have hD : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ (unit_positive t) (unit_positive k)
  have near := distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hD)
    (denominator_positive _ _ _ (unit_positive s)) (frozen_budget L U V p q s cap₁ cap₂)
    (rate_at J J u v _ _ (succ p) q hr)
  exact distance_congr (sample_at f p x M j).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) near

theorem frozen_rate (f : PR 2) (s k x M j : PTm n)
    (h : Γ ⊢[PRAAx] source f x M) (hk : Γ ⊢[PRAAx] le (clock s M j) k) :
    Γ ⊢[PRAAx] independentRate (nameF f) J (data x M j) (frozenData f k x j) one (unit s) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have hs : Δ ⊢[PRAAx] source f (sh x) (sh M) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.shift
  have hks : Δ ⊢[PRAAx] le (clock (sh s) (sh M) (sh j)) (sh k) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hk.shift.shift
  simpa only [independentRate,subst_data,subst_frozenData,GaussianCoefficientNameBounds.subst_unit,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,sh,Δ] using
    frozen_observations f (var 1) (var 0) (sh s) (sh k) (sh x) (sh M) (sh j) hs hks

theorem actual_named_Binet_moment_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source f (var 0) (var 1) ⟶ pointCN (nameF f) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular f _ _ _ Prf.hyp0))

theorem actual_named_Binet_moment_frozen_rate_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source f (var 0) (var 1) ⟶ le (clock (var 3) (var 1) (var 2)) (var 4) ⟶
      independentRate (nameF f) J (data (var 0) (var 1) (var 2)) (frozenData f (var 4) (var 0) (var 2))
        one (unit (var 3))) :=
  closeUniv 5 (.impI (.impI (frozen_rate f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentNamed
