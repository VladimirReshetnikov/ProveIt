import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderPanelPartsOuterFold

/-!
# Cofinal mesh and cutoff for the full Bernoulli recurrence

An explicit primitive-recursive clock keeps the outer integration
cutoff and the actual subdivisions synchronized. The bounded loss
vanishes at the original dyadic rate.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsCofinal

open_ipra
open GaussianStirlingAllOrderPanelPartsOuter (finite_outer_recurrence)
open GaussianStirlingAllOrderPanelPartsOuterFold (fold_identity massPrefix panelPrefix)
open GaussianStirlingAllOrderPanelPartsRecurrence (errorCoefficient)
open GaussianStirlingAllOrderPanelPartsDensities (lowScalar highScalar)
open GaussianStirlingAllOrderPanelDerivative (signedMean)
open GaussianStirlingAllOrderDiscreteParts (sub)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open RationalArithmetic (multiply)
open RationalGaussianEmbedding (embed)
open RationalGaussianRealPart (embed_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def count (p : PTm n) : PTm n := unit p
def coefficient (m e : ℕ) (A B p : PTm n) : PTm n :=
  count p*errorCoefficient m e (A+B*count p) B
def quotientMesh (m e : ℕ) (A B p : PTm n) : PTm n := unit p*succ (coefficient m e A B p)
def mesh (m e : ℕ) (A B p : PTm n) : PTm n := B*quotientMesh m e A B p

theorem quotient_mesh_large (m e : ℕ) (A B p : PTm n) : Γ ⊢[PRAAx]
    le (unit p) (quotientMesh m e A B p) := by
  unfold quotientMesh
  ipra_le 𝔞 (unit p)*𝔞 (coefficient m e A B p)

theorem mesh_positive (m e : ℕ) (A B p : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    le one (mesh m e A B p) :=
  positive_product _ _ hB (le_trans (unit_positive _) (quotient_mesh_large m e A B p))

def leftValue (m e : ℕ) (A B p : PTm n) : PTm n :=
  let M := mesh m e A B p
  let L := count p
  multiply (lowScalar m)
    (sub (multiply (signedMean m) (massPrefix e A B M L)) (panelPrefix (m-1) (e-1) A B M L))

def rightValue (m e : ℕ) (A B p : PTm n) : PTm n :=
  multiply (highScalar e) (panelPrefix m (e+1) A B (mesh m e A B p) (count p))

theorem cofinal_outer_recurrence (m e : ℕ) (hm : 0<m) (he : 2≤e) (A B p : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    bounded (embed (sub (leftValue m e A B p) (rightValue m e A B p))) one (unit p) := by
  let M := mesh m e A B p
  let L := count p
  let R := coefficient m e A B p
  have hM := mesh_positive m e A B p hB
  have h := finite_outer_recurrence m e hm he A B M L hA hM
  have hR : Γ ⊢[PRAAx] le (R*unit p) (one*M) := by
    unfold M mesh quotientMesh
    ipra_le 𝔞 (unit p)*𝔞 (succ R)*sl hB+𝔞 (unit p)
  exact bound_congr (embed_congr (fold_identity m e A B M L)) (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ hM (unit_positive p) hR h)

theorem actual_cofinal_outer_recurrence_closed (m e : ℕ) (hm : 0<m) (he : 2≤e) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((le one (var 0) ⋏ le one (var 1)) ⟶
        bounded (embed (sub (leftValue m e (var 0) (var 1) (var 2))
          (rightValue m e (var 0) (var 1) (var 2)))) one (unit (var 2))) :=
  closeUniv 3 (.impI (cofinal_outer_recurrence m e hm he _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsCofinal
