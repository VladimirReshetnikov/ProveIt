import IPRADerivations.Analysis.Stirling.AllOrders.FirstPanel.NamedLimits.GaussianStirlingAllOrderFirstPanelNamed

/-!
# A regular first-panel name from the literal grid

The original panel observations are retimed by the certified dyadic
radius coefficient. The resulting primitive-recursive name is fast
Cauchy and cross-equivalent to the original named Stirling difference.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelName

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianStirlingAllOrderFirstPanelReadback (halfPanel)
open GaussianStirlingAllOrderFirstPanelNamed (mesh radiusCoefficient observation_distance)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder
  (distance_congr distance_symmetric distance_radius_mono distance_triangle_same distance_through_product_denominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "dF" => GaussianStirlingDifference.nameF
local notation "dData" => GaussianStirlingDifference.data

def clock (A B k p : PTm n) : PTm n := exponent (succ (radiusCoefficient (A+B*k) B)) p
def body (A B k p : PTm n) : PTm n := halfPanel A B (mesh (A+B*k) B (clock A B k p)) k
def data (A B k : PTm n) : PTm n := pairT A (pairT B k)

def nameF : PR 2 :=
  PTm.toPR (body (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0))

ipra_subst clock [radiusCoefficient]

ipra_subst body [halfPanel, mesh, GaussianStirlingAllOrderFirstPanelNamed.logClock, GaussianHarmonicLogarithmName.clock, GammaEulerConstantName.mesh, GammaEulerConstantName.unit, GaussianNamedBoundedProductObservation.clock]

ipra_subst data

theorem name_at (A B k p : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data A B k) ≐ body A B k p := by
  simpa [nameF, data, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 2)
      (body (var 1) (var 2) (var 3) (var 0)) p ![A, B, k])

theorem point_cross (A B k p q : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B k)) (ap2 dF q (dData (A+B*k) B))
      (unit p+unit q) (unit p*unit q) := by
  let U := A+B*k
  let t := clock A B k p
  let N := radiusCoefficient U B
  let D := unit t*unit q
  let x := dData U B
  have hU := le_trans hA (le_add_right A (B*k))
  have hD := positive_product _ _ (unit_positive (Γ := Γ) t) (unit_positive q)
  have hP := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive q)
  have h := observation_distance A B k t hA hB
  have first := distance_radius_mono _ _ _ _ (N*unit q) D (unit_positive t) hD (by unfold D; ipra_le 0) h
  have second := point_at dF x t q (GaussianStirlingDifference.name_regular U B hU hB)
  have ht : Γ ⊢[PRAAx] le (succ N*unit p) (unit t) := query_budget (succ N) p
  have cost : Γ ⊢[PRAAx] le ((N*unit q+(unit t+unit q))*(unit p*unit q)) ((unit p+unit q)*D) := by
    unfold D
    ipra_le 𝔞(unit q)*𝔞(unit q)*sl ht
  exact distance_congr (name_at A B k p).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hD hP cost (distance_triangle_same _ _ _ _ _ _ hD first second))

theorem name_cross (A B k : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent nameF dF (data A B k) (dData (A+B*k) B) := by
  refine .allI (.allI ?_)
  let sa := Syn.shift (Syn.shift A)
  let sb := Syn.shift (Syn.shift B)
  let sk := Syn.shift (Syn.shift k)
  have ha : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one sa := by simpa [sa,Fm.shift,Syn.shift] using hA.shift.shift
  have hb : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one sb := by simpa [sb,Fm.shift,Syn.shift] using hB.shift.shift
  simpa [crossEquivalent,sa,sb,sk,Syn.shift,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    point_cross sa sb sk (var 1) (var 0) ha hb

theorem point_regular (A B k p q : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B k)) (ap2 nameF q (data A B k))
      (unit p+unit q) (unit p*unit q) := by
  let U := A+B*k
  let t := clock A B k p
  let v := clock A B k q
  let N := radiusCoefficient U B
  let D := unit t*unit v
  let x := dData U B
  have hD := positive_product _ _ (unit_positive (Γ := Γ) t) (unit_positive v)
  have hP := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive q)
  have hU := le_trans hA (le_add_right A (B*k))
  have mid := point_at dF x t v (GaussianStirlingDifference.name_regular U B hU hB)
  have joined := distance_through_product_denominator (unit_positive t) (unit_positive v)
    (observation_distance A B k t hA hB) mid
    (distance_symmetric _ _ _ _ (unit_positive v) (observation_distance A B k v hA hB))
  have ht : Γ ⊢[PRAAx] le (succ N*unit p) (unit t) := query_budget (succ N) p
  have hv : Γ ⊢[PRAAx] le (succ N*unit q) (unit v) := query_budget (succ N) q
  have cost : Γ ⊢[PRAAx] le (((N*unit v+(unit t+unit v))+N*unit t)*(unit p*unit q)) ((unit p+unit q)*D) := by
    unfold D
    ipra_le 𝔞(unit v)*𝔞(unit q)*sl ht+𝔞(unit t)*𝔞(unit p)*sl hv
  exact distance_congr (name_at A B k p).eqSymm (name_at A B k q).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hD hP cost joined)

theorem name_regular (A B k : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN nameF (data A B k) := by
  refine .allI (.allI ?_)
  let sa := Syn.shift (Syn.shift A)
  let sb := Syn.shift (Syn.shift B)
  let sk := Syn.shift (Syn.shift k)
  have ha : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one sa := by simpa [sa,Fm.shift,Syn.shift] using hA.shift.shift
  have hb : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one sb := by simpa [sb,Fm.shift,Syn.shift] using hB.shift.shift
  simpa [pointCN,sa,sb,sk,Syn.shift,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    point_regular sa sb sk (var 1) (var 0) ha hb

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelName
