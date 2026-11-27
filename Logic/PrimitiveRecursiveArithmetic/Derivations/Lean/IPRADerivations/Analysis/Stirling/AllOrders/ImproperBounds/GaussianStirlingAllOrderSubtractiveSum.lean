import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderDiscreteParts
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalSumAdditivity
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalSumLinearity

/-!
# Exact subtraction of two finite rational sums

The body of pointwise differences is itself a primitive recursive
row program. Its normalized sum is the difference of the original
two normalized sums.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSubtractiveSum

open_ipra
open GaussianStirlingAllOrderDiscreteParts (sub)
open RationalAlgebra (minusOne negative_minus_multiply add_congr)
open RationalSumLinearity (scaledBody scaled_term sum_homogeneous)
open RationalSumAdditivity (addedBody added_term sum_additive)
open RationalFiniteSum (term)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "rsum" => RationalFiniteSum.sum

def body (f g : PTm 2) : PTm 2 := addedBody f (scaledBody g)
def data (x y : PTm n) : PTm n := pairT x (pairT minusOne y)

ipra_subst data [minusOne]

theorem term_at (f g : PTm 2) (i x y : PTm n) :
    Γ ⊢[PRAAx] term (body f g) i (data x y) ≐ sub (term f i x) (term g i y) :=
  (added_term f (scaledBody g) i x (pairT minusOne y)).eqTrans
    (add_congr (.eqRefl _) ((scaled_term g i minusOne y).eqTrans (negative_minus_multiply _).eqSymm))

theorem sum_at (f g : PTm 2) (N x y : PTm n) :
    Γ ⊢[PRAAx] rsum (body f g) N (data x y) ≐ sub (rsum f N x) (rsum g N y) :=
  (sum_additive f (scaledBody g) N x (pairT minusOne y)).eqTrans
    (add_congr (.eqRefl _) ((sum_homogeneous g N minusOne y).eqTrans (negative_minus_multiply _).eqSymm))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSubtractiveSum
