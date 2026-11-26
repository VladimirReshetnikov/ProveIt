import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveGridUnscale

/-!
# Finite beta telescope with an independent upper observation

The primitive telescope spends a grid error and the discarded lower
endpoint. The upper observation can be any certified sample of the
finite beta endpoint. The proof has no separation condition on the
degree relative to the disk radius.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaFiniteEndpointTelescope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (positive_product qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianBetaPrimitiveGridUnscale (quadrature scaledEndpoint demand)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem discard_lower (u v B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] GaussianRationalHorner.canonical u)
    (hv : Γ ⊢[PRAAx] GaussianRationalHorner.canonical v)
    (h : Γ ⊢[PRAAx] bounded v one B) : Γ ⊢[PRAAx] distanceBounded (qsub u v) u one B := by
  have undo : Γ ⊢[PRAAx] qsub u (qsub u v) ≐ v :=
    (qsub_congr (GaussianRationalLinearProduct.add_sub_right v u hu).eqSymm (.eqRefl _)).eqTrans
      (GaussianReciprocalHorner.qsub_add_cancel v (qsub u v) hv)
  exact distance_symmetric _ _ _ _ hB
    (GaussianRationalReciprocal.bound_congr undo.eqSymm (.eqRefl _) (.eqRefl _) h)

theorem grid_to_certified_endpoint (t p q z R B A a C E N M Y : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBetaPrimitiveCompactGridAccuracy.source z R B A a C E N N)
    (hm : Γ ⊢[PRAAx] le (GaussianBetaPrimitiveCompactGridAccuracy.cells (demand (succ (succ t)) N) z R B C E N N) M)
    (hp : Γ ⊢[PRAAx] le (GaussianBetaPrimitiveCompactGridAccuracy.precisionAt (demand (succ (succ t)) N) z B N M) p)
    (hl : Γ ⊢[PRAAx] bounded (scaledEndpoint zero p z B a C E M N) one (unit (succ (succ t))))
    (hu : Γ ⊢[PRAAx] distanceBounded (scaledEndpoint M p z B a C E M N) Y
      (unit (succ (succ t))+unit q) (unit (succ (succ t))*unit q)) :
    Γ ⊢[PRAAx] distanceBounded (quadrature p z B a C E M N) Y (unit t+unit q) (unit t*unit q) := by
  let k := succ (succ t)
  let v := unit k
  let w := unit q
  let D := v*w
  let L := scaledEndpoint zero p z B a C E M N
  let U := scaledEndpoint M p z B a C E M N
  let Q := quadrature p z B a C E M N
  have hV := unit_positive (Γ := Γ) k
  have hW := unit_positive (Γ := Γ) q
  have hD := positive_product v w hV hW
  have integral : Γ ⊢[PRAAx] distanceBounded Q (qsub U L) one v :=
    distance_symmetric _ _ _ _ hV (GaussianBetaPrimitiveGridUnscale.original_dyadic_accuracy k p z R B A a C E N M N h hm hp)
  have small := discard_lower U L v hV (qmul_canonical _ _) (qmul_canonical _ _) hl
  have enlarge : Γ ⊢[PRAAx] le (one*D) (w*v) :=
    le_congr (by dsimp only [D]; ipra_ring) (.eqRefl _) (le_refl _)
  have intScaled := distance_radius_mono _ _ _ _ _ _ hV hD enlarge integral
  have lowerScaled := distance_radius_mono _ _ _ _ _ _ hV hD enlarge small
  have combined := distance_triangle_same Q (qsub U L) Y w (w+(v+w)) D hD intScaled
    (distance_triangle_same (qsub U L) U Y w (v+w) D hD lowerScaled hu)
  have quad : Γ ⊢[PRAAx] v ≐ (num 4)*unit t := by
    change Γ ⊢[PRAAx] pw two (succ (succ t)) ≐ (num 4)*pw two t
    exact (pw_succ two (succ t)).eqTrans ((congrMul (pw_succ two t) (.eqRefl _)).eqTrans (by ipra_ring))
  have comparison : Γ ⊢[PRAAx] le ((w+(w+(v+w)))*(unit t*w)) ((unit t+w)*D) := by
    let V := num 4*unit t
    have lhs : Γ ⊢[PRAAx] (w+(w+(v+w)))*(unit t*w) ≐ (w+(w+(V+w)))*(unit t*w) :=
      congrMul (congrAdd (.eqRefl _) (congrAdd (.eqRefl _) (congrAdd quad (.eqRefl _)))) (.eqRefl _)
    have rhs : Γ ⊢[PRAAx] (unit t+w)*D ≐ (unit t+w)*(V*w) :=
      congrMul (.eqRefl _) (congrMul quad (.eqRefl _))
    have reduced : Γ ⊢[PRAAx] le ((w+(w+(V+w)))*(unit t*w)) ((unit t+w)*(V*w)) :=
      le_of_eq_add (d := unit t*w*w) (by dsimp only [V]; ipra_ring)
    exact le_congr lhs.eqSymm rhs.eqSymm reduced
  exact distance_radius_mono _ _ _ _ _ _ hD (positive_product _ _ (unit_positive t) hW) comparison combined

end LeanProofs.IPRA.Analysis.GaussianBetaFiniteEndpointTelescope
