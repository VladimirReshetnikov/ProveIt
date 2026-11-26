import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicExponentialGroup
import IPRADerivations.Analysis.Trigonometry.GaussianNamedSineFromExponential

/-!
# The half-angle sine on the full cyclic index range

For indices up to the modulus, evaluate the original cyclic angle at
twice that modulus. Its exponential square is the cyclic root, and
the associated sine is the original named sine at `πr/m`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 120000

namespace LeanProofs.IPRA.Analysis.GaussianCyclicFullHalfAngle

open_ipra
open ComplexLogarithmRemainder (scale oneCode)
open GaussianCyclicExponentialRoots
  (source coefficient angleF angleData angle_input rootF rootData root_regular sample)
open GaussianCyclicExponentialGroup (productF productData product_index_cross)
open GaussianArctangentExponentialPeriod (fullTurnData fullTurnRadius)
open GaussianRationalHorner (ofGaussian_canonical ofGaussian_represents represents_rescale
  canonical_unique represents_congr)
open GaussianRootAlgebra (equal_of_values re_scale im_scale re_one im_one)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_refl)
open GaussianNamedSineFromExponential (sineF)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sineData (r m x : PTm n) : PTm n :=
  GaussianNamedSineFromExponential.sineData angleF fullTurnRadius (angleData r (two*m) x)
def sineSample (p r m x : PTm n) : PTm n := ap2 (sineF angleF) p (sineData r m x)

ipra_subst sineData [fullTurnRadius, GaussianArctangentExponentialPeriod.twiceRadius, GaussianArctangentQuarterExponential.radius]

ipra_subst sineSample

private theorem modulus_le_doubled (m : PTm n) : Γ ⊢[PRAAx] le m (two*m) :=
  le_of_eq_add (d := m) (by ipra_ring)

theorem half_source (r m : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] source r (two*m) :=
  .andI (le_trans h.andE₁ (modulus_le_doubled m)) (le_trans h.andE₂ (modulus_le_doubled m))

theorem doubled_source (r m : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] source (two*r) (two*m) :=
  .andI (half_source r m h).andE₁ (le_mul_mono (le_refl two) h.andE₂)

theorem coefficient_double (r m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] coefficient (two*r) (two*m) ≐ coefficient r m := by
  have hD := le_trans hm (modulus_le_doubled m)
  have h := represents_rescale _ _ m two (ofGaussian_represents (scale r oneCode) m hm)
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (scale two (scale r oneCode)) (scale (two*r) oneCode) := by
    apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ (two*m) (ofGaussian_canonical _ _ hD) (ofGaussian_canonical _ _ hm)
    hD (ofGaussian_represents _ _ hD) (represents_congr (.eqRefl _) e (mul_comm _ _) h)

private theorem root_data_from_coefficient (r s m M x : PTm n)
    (h : Γ ⊢[PRAAx] coefficient r m ≐ coefficient s M) :
    Γ ⊢[PRAAx] rootData r m x ≐ rootData s M x :=
  congrPairT (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT h (.eqRefl _)))

private theorem cross_source_congr (f g : PR 2) (x x' y : PTm n)
    (e : Γ ⊢[PRAAx] x ≐ x') (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent f g x' y := by
  simpa only [GaussianNameEquivalence.subst_crossEquivalent,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (crossEquivalent f g (var 0) (var 1) : Fm PTm 2)
      (σ := ![x,y]) (σ' := ![x',y])
      (fun i => by fin_cases i; exact e; exact .eqRefl _) (by simpa only [GaussianNameEquivalence.subst_crossEquivalent, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h)

theorem exponential_square (r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] crossEquivalent productF rootF (productData r r (two*m) x) (rootData r m x) := by
  have h₁ := half_source r m h
  have h₂ := doubled_source r m h
  have e : Γ ⊢[PRAAx] r+r ≐ two*r := by ipra_ring
  have h₃ : Γ ⊢[PRAAx] source (r+r) (two*m) :=
    .andI h₂.andE₁ (le_congr e.eqSymm (.eqRefl _) h₂.andE₂)
  have base := product_index_cross r r (two*m) x h₁ h₁ h₃
  have cast := root_data_from_coefficient _ _ _ _ x
    ((GaussianCyclicExponentialGroup.coefficient_congr (two*m) e).eqTrans (coefficient_double r m h.andE₁))
  have refl := cross_refl rootF (rootData r m x) (root_regular r m x h)
  have castCross := cross_source_congr rootF rootF (rootData r m x) (rootData (r+r) (two*m) x)
    (rootData r m x) cast.eqSymm refl
  exact cross_trans productF rootF rootF _ _ _ base castCross

theorem sine_regular (r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN (sineF angleF) (sineData r m x) :=
  GaussianNamedSineFromExponential.sine_regular angleF fullTurnRadius _
    (angle_input r (two*m) x (half_source r m h))

theorem actual_full_cyclic_half_angle_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 2) (var 1) ⟶ crossEquivalent productF rootF
        (productData (var 2) (var 2) (two*var 1) (var 0)) (rootData (var 2) (var 1) (var 0))) :=
  closeUniv 3 (.impI (exponential_square _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCyclicFullHalfAngle
