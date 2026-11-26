import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaAdjacentCutoff
import IPRADerivations.Analysis.Gamma.GaussianGammaReciprocalInverse

/-!
# Regrouping the named Euler factors in the finite Gauss identity

Separate the four rational heads from the exponential factors on
each side. The ratio power occurs only in the exponential comparison.
Each product retains the precision clock of its given name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerProductAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaReciprocalInverse (named_product_exchange)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem swap_first (w a b : PR 2) (W A B : PTm n)
    (hw : Γ ⊢[PRAAx] pointCN w W) (ha : Γ ⊢[PRAAx] pointCN a A) (hb : Γ ⊢[PRAAx] pointCN b B) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF w (multiplyF a b)) (multiplyF a (multiplyF w b))
      (multiplyData w (multiplyF a b) W (multiplyData a b A B))
      (multiplyData a (multiplyF w b) A (multiplyData w b W B)) := by
  have s := multiply_cross (multiplyF w a) (multiplyF a w) b b
    (multiplyData w a W A) (multiplyData a w A W) B B
    (multiply_fast _ _ _ _ hw ha) (multiply_fast _ _ _ _ ha hw) hb hb
    (multiply_commutative w a W A hw ha) (cross_refl b B hb)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative w a b W A B hw ha hb))
    (cross_trans _ _ _ _ _ _ s (multiply_associative a w b A W B ha hw hb))

theorem regroup_ratio (a b c d w : PR 2) (A B C D W : PTm n)
    (ha : Γ ⊢[PRAAx] pointCN a A) (hb : Γ ⊢[PRAAx] pointCN b B)
    (hc : Γ ⊢[PRAAx] pointCN c C) (hd : Γ ⊢[PRAAx] pointCN d D) (hw : Γ ⊢[PRAAx] pointCN w W) :
    Γ ⊢[PRAAx] crossEquivalent
      (multiplyF (multiplyF w (multiplyF a b)) (multiplyF c d))
      (multiplyF (multiplyF a c) (multiplyF (multiplyF w b) d))
      (multiplyData (multiplyF w (multiplyF a b)) (multiplyF c d)
        (multiplyData w (multiplyF a b) W (multiplyData a b A B)) (multiplyData c d C D))
      (multiplyData (multiplyF a c) (multiplyF (multiplyF w b) d)
        (multiplyData a c A C) (multiplyData (multiplyF w b) d (multiplyData w b W B) D)) := by
  have hab := multiply_fast a b A B ha hb
  have hwb := multiply_fast w b W B hw hb
  have hcd := multiply_fast c d C D hc hd
  have lift := multiply_cross (multiplyF w (multiplyF a b)) (multiplyF a (multiplyF w b))
    (multiplyF c d) (multiplyF c d) _ _ _ _ (multiply_fast _ _ _ _ hw hab) (multiply_fast _ _ _ _ ha hwb)
    hcd hcd (swap_first w a b W A B hw ha hb) (cross_refl _ _ hcd)
  exact cross_trans _ _ _ _ _ _ lift (named_product_exchange a (multiplyF w b) c d
    A (multiplyData w b W B) C D ha hwb hc hd)

theorem combine_head_and_exponent (a b c d e f g h w : PR 2) (A B C D E F G H W : PTm n)
    (ha : Γ ⊢[PRAAx] pointCN a A) (hb : Γ ⊢[PRAAx] pointCN b B)
    (hc : Γ ⊢[PRAAx] pointCN c C) (hd : Γ ⊢[PRAAx] pointCN d D)
    (he : Γ ⊢[PRAAx] pointCN e E) (hf : Γ ⊢[PRAAx] pointCN f F)
    (hg : Γ ⊢[PRAAx] pointCN g G) (hh : Γ ⊢[PRAAx] pointCN h H) (hw : Γ ⊢[PRAAx] pointCN w W)
    (head : Γ ⊢[PRAAx] crossEquivalent (multiplyF a c) (multiplyF e g)
      (multiplyData a c A C) (multiplyData e g E G))
    (exponent : Γ ⊢[PRAAx] crossEquivalent (multiplyF b d) (multiplyF (multiplyF w f) h)
      (multiplyData b d B D) (multiplyData (multiplyF w f) h (multiplyData w f W F) H)) :
    Γ ⊢[PRAAx] crossEquivalent
      (multiplyF (multiplyF a b) (multiplyF c d))
      (multiplyF (multiplyF w (multiplyF e f)) (multiplyF g h))
      (multiplyData (multiplyF a b) (multiplyF c d) (multiplyData a b A B) (multiplyData c d C D))
      (multiplyData (multiplyF w (multiplyF e f)) (multiplyF g h)
        (multiplyData w (multiplyF e f) W (multiplyData e f E F)) (multiplyData g h G H)) := by
  have entry := named_product_exchange a b c d A B C D ha hb hc hd
  have right := regroup_ratio e f g h w E F G H W he hf hg hh hw
  have combined := multiply_cross _ _ _ _ _ _ _ _
    (multiply_fast a c A C ha hc) (multiply_fast e g E G he hg)
    (multiply_fast b d B D hb hd)
    (multiply_fast (multiplyF w f) h (multiplyData w f W F) H (multiply_fast w f W F hw hf) hh)
    head exponent
  exact cross_trans _ _ _ _ _ _ entry (cross_trans _ _ _ _ _ _ combined (cross_symm _ _ _ _ right))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerProductAlgebra
