import IPRADerivations.Analysis.GaussianNamedDifference
import IPRADerivations.Analysis.GaussianRationalRoundedPower

/-!
# Exact identities for actual named differences

The named programs preserve the four-point difference exchange and
multiplication of a difference by an independent regular name.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianNamedDifferenceAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (equivalent_of_envelope through_identity multiply_sample_error product_right_error)
open GaussianNamedDifference (nameF data name_regular sample_error difference_distance)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (positive_product canonical_unique represents_congr qmul)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRationalMetric (distanceBounded qsub qsub_represents qsub_canonical)
open GaussianRootAlgebra (equal_of_values re_sub im_sub)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem rational_shuffle (a b c d : PTm n) :
    Γ ⊢[PRAAx] qsub (qsub a b) (qsub c d) ≐ qsub (qsub a c) (qsub b d) := by
  let E := rawDen a*rawDen b*rawDen c*rawDen d
  have p : Γ ⊢[PRAAx] le one E :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ (raw_den_positive a) (raw_den_positive b))
      (raw_den_positive c)) (raw_den_positive d)
  have a' := rescale_to a (rawGaussian a) (rawDen a) (rawDen b*rawDen c*rawDen d) E (raw_represents (Γ := Γ) a)
    (by dsimp only [E]; ipra_ring)
  have b' := rescale_to b (rawGaussian b) (rawDen b) (rawDen a*rawDen c*rawDen d) E (raw_represents (Γ := Γ) b)
    (by dsimp only [E]; ipra_ring)
  have c' := rescale_to c (rawGaussian c) (rawDen c) (rawDen a*rawDen b*rawDen d) E (raw_represents (Γ := Γ) c)
    (by dsimp only [E]; ipra_ring)
  have d' := rescale_to d (rawGaussian d) (rawDen d) (rawDen a*rawDen b*rawDen c) E (raw_represents (Γ := Γ) d)
    (by dsimp only [E]; ipra_ring)
  have l := qsub_represents _ _ _ _ _ p (qsub_represents _ _ _ _ _ p a' b') (qsub_represents _ _ _ _ _ p c' d')
  have r := qsub_represents _ _ _ _ _ p (qsub_represents _ _ _ _ _ p a' c') (qsub_represents _ _ _ _ _ p b' d')
  apply canonical_unique _ _ _ E (qsub_canonical _ _) (qsub_canonical _ _) p (hrv := r)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := l)
  apply equal_of_values <;> simp only [re_sub,im_sub] <;> ring

private theorem double_difference_at (f g h k : PR 2) (x y u v p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h u) (hk : Γ ⊢[PRAAx] pointCN k v) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF (nameF f g) (nameF h k)) p (data (data x y) (data u v)))
      (qsub (qsub (ap2 f p x) (ap2 g p y)) (qsub (ap2 h p u) (ap2 k p v))) (num 18) (unit p) := by
  have a := sample_error f g x y p hf hg
  have b := sample_error h k u v p hh hk
  have c := sample_error (nameF f g) (nameF h k) (data x y) (data u v) p
    (name_regular _ _ _ _ hf hg) (name_regular _ _ _ _ hh hk)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) c (difference_distance _ _ _ _ _ _ _ (unit_positive p) a b))

theorem shuffle (f g h k : PR 2) (x y u v : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h u) (hk : Γ ⊢[PRAAx] pointCN k v) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (nameF f g) (nameF h k)) (nameF (nameF f h) (nameF g k))
      (data (data x y) (data u v)) (data (data x u) (data y v)) := by
  apply equivalent_of_envelope _ _ _ _ (num 36)
    (name_regular _ _ _ _ (name_regular _ _ _ _ hf hg) (name_regular _ _ _ _ hh hk))
    (name_regular _ _ _ _ (name_regular _ _ _ _ hf hh) (name_regular _ _ _ _ hg hk))
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  let p : PTm (n+1) := var 0
  have fs : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift
  have gs : Δ ⊢[PRAAx] pointCN g (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift
  have hs : Δ ⊢[PRAAx] pointCN h (sh u) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hh.shift
  have ks : Δ ⊢[PRAAx] pointCN k (sh v) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hk.shift
  have e := through_identity _ _ _ _ _ _ _ (unit_positive p)
    (double_difference_at f g h k (sh x) (sh y) (sh u) (sh v) p fs gs hs ks)
    (double_difference_at f h g k (sh x) (sh u) (sh y) (sh v) p fs hs gs ks)
    (rational_shuffle (ap2 f p (sh x)) (ap2 g p (sh y)) (ap2 h p (sh u)) (ap2 k p (sh v)))
  simpa only [Δ,sh,p,Syn.shift,GaussianNamedDifference.subst_data,PTm.subst_num] using
    distance_congr (.eqRefl _) (.eqRefl _) (show Δ ⊢[PRAAx] num 18+num 18 ≐ num 36 by ipra_ring) (.eqRefl _) e

private def scaleBudget (f g h : PR 2) (x y z : PTm n) : PTm n :=
  (multiplyModulus f (nameF g h) x (data y z)+one+U f x*num 6)+
    (num 6+(multiplyModulus f g x y+one)+(multiplyModulus f h x z+one))

private theorem distribute_at (f g h : PR 2) (x y z p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h z) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (multiplyF f (nameF g h)) p (multiplyData f (nameF g h) x (data y z)))
      (ap2 (nameF (multiplyF f g) (multiplyF f h)) p (data (multiplyData f g x y) (multiplyData f h x z)))
      (scaleBudget f g h x y z) (unit p) := by
  let F := ap2 f p x
  let G := ap2 g p y
  let H := ap2 h p z
  have hd := name_regular g h y z hg hh
  have hpp := unit_positive (Γ := Γ) p
  have left₀ := multiply_sample_error f (nameF g h) x (data y z) p hf hd
  have left₁ := product_right_error F _ _ _ _ _ _ hpp (sample_error g h y z p hg hh)
    (sample_bound (nameF g h) (data y z) p hd) (sample_bound f x p hf)
  have left := distance_triangle_same _ _ _ _ _ _ hpp left₀ left₁
  have right₀ := sample_error (multiplyF f g) (multiplyF f h) (multiplyData f g x y) (multiplyData f h x z) p
    (multiply_fast _ _ _ _ hf hg) (multiply_fast _ _ _ _ hf hh)
  have right₁ := difference_distance _ _ _ _ _ _ _ hpp (multiply_sample_error f g x y p hf hg)
    (multiply_sample_error f h x z p hf hh)
  have right := distance_triangle_same _ _ _ _ _ _ hpp right₀ right₁
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [scaleBudget]; ipra_ring) (.eqRefl _)
    (through_identity _ _ _ _ _ _ _ hpp left right (GaussianRationalRoundedPower.multiplication_difference F G H).eqSymm)

theorem distribute (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h z) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f (nameF g h)) (nameF (multiplyF f g) (multiplyF f h))
      (multiplyData f (nameF g h) x (data y z)) (data (multiplyData f g x y) (multiplyData f h x z)) := by
  apply equivalent_of_envelope _ _ _ _ (scaleBudget f g h x y z)
    (multiply_fast _ _ _ _ hf (name_regular _ _ _ _ hg hh))
    (name_regular _ _ _ _ (multiply_fast _ _ _ _ hf hg) (multiply_fast _ _ _ _ hf hh))
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have fs : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift
  have gs : Δ ⊢[PRAAx] pointCN g (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift
  have hs : Δ ⊢[PRAAx] pointCN h (sh z) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hh.shift
  simpa only [Δ,sh,Syn.shift,scaleBudget,GaussianNamedDifference.subst_data,GaussianNameArithmetic.subst_multiplyData,
    GaussianNameArithmetic.subst_multiplyModulus,GaussianNameBounds.subst_U,PTm.subst_num,PTm.subst_add,PTm.subst_mul,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    distribute_at f g h (sh x) (sh y) (sh z) (var 0) fs gs hs

end LeanProofs.IPRA.Analysis.GaussianNamedDifferenceAlgebra
