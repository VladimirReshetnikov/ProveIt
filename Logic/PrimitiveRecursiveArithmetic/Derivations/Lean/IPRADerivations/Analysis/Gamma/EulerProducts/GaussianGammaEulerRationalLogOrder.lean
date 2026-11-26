import IPRADerivations.Analysis.Names.Rates.GaussianNamedRealOrderTransport
import IPRADerivations.Analysis.Stirling.GaussianStirlingTailComparison
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianNamedGammaHalfShift

/-!
# Summing and rearranging independent-clock named orders

The actual addition name queries both summands at a cofinal clock.
That clock pays for the two independent order errors and gives the
original named real-order formula on the sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 1350000

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLogOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative add_commutative)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianRationalHorner (qadd qadd_canonical positive_product)
open GaussianStirlingTailComparison (point_add_upper_same)
open RationalValueBounds (upper upper_congr upper_mono upper_of_radius)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem order_refl (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] realOrder f f x x := by
  refine .allI (.allI ?_)
  let X := Syn.shift (Syn.shift x)
  let Delta := (Γ.map Fm.shift).map Fm.shift
  have h : Delta ⊢[PRAAx] pointCN f X := by simpa [Fm.shift,Syn.shift,X,Delta] using hf.shift.shift
  exact upper_of_radius _ _ _ _
    (scalar_coordinate_distance _ _ _ _ (positive_product _ _ (unit_positive _) (unit_positive _))
      (GaussianNameEquivalence.point_at f X (var 1) (var 0) h))

private theorem fst_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] fstT a ≐ fstT b := by
  simpa using Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (fstT (var 0) : PTm 1)
    (σ := ![a]) (σ' := ![b]) (fun i => by fin_cases i; exact h)

theorem add_order_at (f g h k : PR 2) (x y u v p q : PTm n)
    (left : Γ ⊢[PRAAx] realOrder f g x y) (right : Γ ⊢[PRAAx] realOrder h k u v) :
    Γ ⊢[PRAAx] upper (fstT (ap2 (addF f h) p (addData x u))) (fstT (ap2 (addF g k) q (addData y v)))
      (unit p+unit q) (unit p*unit q) := by
  let s := GaussianFastValueCut.exponent two p
  let t := GaussianFastValueCut.exponent two q
  let U := unit p
  let V := unit q
  let S := unit s
  let T := unit t
  have leS : Γ ⊢[PRAAx] le (two*U) S := GaussianFastValueCut.query_budget two p
  have leT : Γ ⊢[PRAAx] le (two*V) T := GaussianFastValueCut.query_budget two q
  have pos := positive_product (Γ := Γ) S T (unit_positive s) (unit_positive t)
  have e := point_add_upper_same (ap2 f s x) (ap2 g t y) (ap2 h s u) (ap2 k t v)
    (S+T) (S+T) (S*T) pos (real_order_at f g x y s t left) (real_order_at h k u v s t right)
  have comparison : Γ ⊢[PRAAx] le (((S+T)+(S+T))*(U*V)) ((U+V)*(S*T)) := by
    let 𝔞 := fun z : PTm n => Groth.ι (IPRA.Q.mk Γ z)
    ipra_le 𝔞 U*𝔞 S*sl leT+𝔞 V*𝔞 T*sl leS
  have first := (GaussianNameArithmetic.add_at (Γ := Γ) f h x u p).eqTrans
    (GaussianExponentialReference.recode_fixed (qadd (ap2 f s x) (ap2 h s u)) (qadd_canonical _ _))
  have last := (GaussianNameArithmetic.add_at (Γ := Γ) g k y v q).eqTrans
    (GaussianExponentialReference.recode_fixed (qadd (ap2 g t y) (ap2 k t v)) (qadd_canonical _ _))
  exact upper_congr (fst_congr first.eqSymm) (fst_congr last.eqSymm) (.eqRefl _) (.eqRefl _)
    (upper_mono _ _ _ _ _ _ pos e comparison)

theorem add_order (f g h k : PR 2) (x y u v : PTm n)
    (left : Γ ⊢[PRAAx] realOrder f g x y) (right : Γ ⊢[PRAAx] realOrder h k u v) :
    Γ ⊢[PRAAx] realOrder (addF f h) (addF g k) (addData x u) (addData y v) := by
  refine .allI (.allI ?_)
  let sh (z : PTm n) := Syn.shift (Syn.shift z)
  let Delta := (Γ.map Fm.shift).map Fm.shift
  have ls : Delta ⊢[PRAAx] realOrder f g (sh x) (sh y) := by simpa [Fm.shift,Syn.shift,sh,Delta] using left.shift.shift
  have rs : Delta ⊢[PRAAx] realOrder h k (sh u) (sh v) := by simpa [Fm.shift,Syn.shift,sh,Delta] using right.shift.shift
  simpa only [realOrder,Syn.shift,sh,GaussianNameArithmetic.subst_addData] using
    add_order_at f g h k (sh x) (sh y) (sh u) (sh v) (var 1) (var 0) ls rs

theorem add_interleave (f g h k : PR 2) (x y u v : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h u) (hk : Γ ⊢[PRAAx] pointCN k v) :
    Γ ⊢[PRAAx] crossEquivalent (addF (addF f g) (addF h k)) (addF (addF f h) (addF g k))
      (addData (addData x y) (addData u v)) (addData (addData x u) (addData y v)) := by
  have hf_g := add_fast f g x y hf hg
  have hh_k := add_fast h k u v hh hk
  have hg_h := add_fast g h y u hg hh
  have hh_g := add_fast h g u y hh hg
  have hf_h := add_fast f h x u hf hh
  have a := cross_symm _ _ _ _ (add_associative (addF f g) h k (addData x y) u v hf_g hh hk)
  have b := add_cross _ _ k k _ _ v v (add_fast (addF f g) h _ _ hf_g hh) (add_fast f (addF g h) _ _ hf hg_h)
    hk hk (add_associative f g h x y u hf hg hh) (cross_refl _ _ hk)
  have inner := add_cross f f (addF g h) (addF h g) x x (addData y u) (addData u y) hf hf hg_h hh_g
    (cross_refl _ _ hf) (add_commutative g h y u hg hh)
  have c := add_cross _ _ k k _ _ v v (add_fast f (addF g h) _ _ hf hg_h) (add_fast f (addF h g) _ _ hf hh_g)
    hk hk inner (cross_refl _ _ hk)
  have d := add_cross _ _ k k _ _ v v (add_fast f (addF h g) _ _ hf hh_g) (add_fast (addF f h) g _ _ hf_h hg)
    hk hk (cross_symm _ _ _ _ (add_associative f h g x u y hf hh hg)) (cross_refl _ _ hk)
  have e := add_associative (addF f h) g k (addData x u) y v hf_h hg hk
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ b
    (cross_trans _ _ _ _ _ _ c (cross_trans _ _ _ _ _ _ d e)))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLogOrder
