import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.GaussianBarnesCanonicalHyperfactorialBarnesStep

/-!
# The unit recurrence of the original positive rational hyperfactorial

The numerator advances by `Gamma(z) exp(z Log z)` and the Barnes
denominator advances by the same Gamma name. The exact cleared
identities and the certified inverse of the shifted Barnes value give
`H(z+1) = H(z) exp(z Log z)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorialRecurrence

open_ipra
open GaussianBarnesCanonicalHyperfactorial
  (nameF data barnesData barnes_regular barnes_apart height regular cleared_relation powerF powerData power_regular)
open GaussianBarnesCanonicalHyperfactorialPowerStep
  (stepPowerF stepPowerData step_power_regular gammaPowerF gammaPowerData gamma_power_regular pairF pairData numerator_step)
open GaussianBarnesCanonicalHyperfactorialBarnesStep (denominatorF denominatorData denominator_step)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_commutative multiply_one)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "M" => multiplyF
local notation "Md" => multiplyData
local notation "G" => GaussianBarnesCanonicalValue.nameF
local notation "IF" => GaussianNameReciprocal.nameF
local notation "Id" => GaussianNameReciprocal.nameData

abbrev stepF : PR 2 := M nameF stepPowerF
def stepData (A B : PTm n) : PTm n := Md nameF stepPowerF (data A B) (stepPowerData A B)

private theorem rotate (f g h : PR 2) (x y z : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN g y)
    (hz : Γ ⊢[PRAAx] pointCN h z) :
    Γ ⊢[PRAAx] crossEquivalent (M f (M g h)) (M g (M h f))
      (Md f (M g h) x (Md g h y z)) (Md g (M h f) y (Md h f z x)) := by
  have a := cross_symm _ _ _ _ (multiply_associative f g h x y z hx hy hz)
  have b := multiply_cross (M f g) (M g f) h h (Md f g x y) (Md g f y x) z z
    (multiply_fast _ _ _ _ hx hy) (multiply_fast _ _ _ _ hy hx) hz hz
    (multiply_commutative f g x y hx hy) (cross_refl _ _ hz)
  have c := multiply_associative g f h y x z hy hx hz
  have d := multiply_cross g g (M f h) (M h f) y y (Md f h x z) (Md h f z x)
    hy hy (multiply_fast _ _ _ _ hx hz) (multiply_fast _ _ _ _ hz hx)
    (cross_refl _ _ hy) (multiply_commutative f h x z hx hz)
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ b (cross_trans _ _ _ _ _ _ c d))

theorem regroup (f g h k : PR 2) (x y u v : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN g y)
    (hu : Γ ⊢[PRAAx] pointCN h u) (hv : Γ ⊢[PRAAx] pointCN k v) :
    Γ ⊢[PRAAx] crossEquivalent (M (M f g) (M h k)) (M (M f h) (M k g))
      (Md (M f g) (M h k) (Md f g x y) (Md h k u v))
      (Md (M f h) (M k g) (Md f h x u) (Md k g v y)) := by
  have uv := multiply_fast h k u v hu hv
  have vy := multiply_fast k g v y hv hy
  have a := multiply_associative f g (M h k) x y (Md h k u v) hx hy uv
  have b := multiply_cross f f (M g (M h k)) (M h (M k g)) x x
    (Md g (M h k) y (Md h k u v)) (Md h (M k g) u (Md k g v y)) hx hx
    (multiply_fast _ _ _ _ hy uv) (multiply_fast _ _ _ _ hu vy) (cross_refl _ _ hx)
    (rotate g h k y u v hy hu hv)
  have c := cross_symm _ _ _ _ (multiply_associative f h (M k g) x u (Md k g v y) hx hu vy)
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ b c)

private theorem inverse_reduction (f g : PR 2) (x y s : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN g y)
    (hg : Γ ⊢[PRAAx] GaussianNameReciprocal.apart g s y) :
    Γ ⊢[PRAAx] crossEquivalent (M (M f g) (IF g)) f
      (Md (M f g) (IF g) (Md f g x y) (Id s y)) x := by
  let inv := IF g
  let w := Id s y
  have hw := GaussianNameReciprocal.name_fast g s y hy hg
  have identity := cross_trans _ _ _ _ _ _ (GaussianNameReciprocal.product_one g s y hy hg)
    (GaussianBoundedInverseApartness.ones_equivalent y x)
  have a := multiply_associative f g inv x y w hx hy hw
  have b := multiply_cross f f (M g inv) oneF x x (Md g inv y w) x hx hx
    (multiply_fast _ _ _ _ hy hw) (one_fast x) (cross_refl _ _ hx) identity
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ b (multiply_one f x hx))

theorem cancel_right (f g h : PR 2) (x y z s : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN g y)
    (hz : Γ ⊢[PRAAx] pointCN h z) (ha : Γ ⊢[PRAAx] GaussianNameReciprocal.apart h s z)
    (he : Γ ⊢[PRAAx] crossEquivalent (M f h) (M g h) (Md f h x z) (Md g h y z)) :
    Γ ⊢[PRAAx] crossEquivalent f g x y := by
  have hr := GaussianNameReciprocal.name_fast h s z hz ha
  have mul := multiply_cross (M f h) (M g h) (IF h) (IF h) (Md f h x z) (Md g h y z) (Id s z) (Id s z)
    (multiply_fast _ _ _ _ hx hz) (multiply_fast _ _ _ _ hy hz) hr hr he (cross_refl _ _ hr)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (inverse_reduction f h x z s hx hz ha))
    (cross_trans _ _ _ _ _ _ mul (inverse_reduction g h y z s hy hz ha))

theorem recurrence (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent nameF stepF (data (A+B) B) (stepData A B) := by
  let h := data A B
  let k := stepPowerData A B
  let g := barnesData A B
  let t := gammaPowerData A B
  let u := stepData A B
  have hNext := le_trans hA (le_add_right A B)
  have hh := regular A B hA hB
  have hk := step_power_regular A B hA hB
  have hg := barnes_regular A B hB
  have ht := gamma_power_regular A B hA hB
  have hu := multiply_fast nameF stepPowerF h k hh hk
  have hp := multiply_fast gammaPowerF stepPowerF t k ht hk
  have start := multiply_cross stepF stepF G denominatorF u u (barnesData (A+B) B) (denominatorData A B)
    hu hu (barnes_regular (A+B) B hB) (multiply_fast _ _ _ _ hg ht)
    (cross_refl _ _ hu) (denominator_step A B hA hB)
  have reorder := regroup nameF stepPowerF G gammaPowerF h k g t hh hk hg ht
  have toNumerator := multiply_cross (M nameF G) powerF pairF pairF (Md nameF G h g) (powerData A B)
    (pairData A B) (pairData A B) (multiply_fast _ _ _ _ hh hg) (power_regular A B hA hB)
    hp hp (cleared_relation A B hA hB) (cross_refl _ _ hp)
  have right := cross_trans _ _ _ _ _ _ start
    (cross_trans _ _ _ _ _ _ reorder
      (cross_trans _ _ _ _ _ _ toNumerator (cross_symm _ _ _ _ (numerator_step A B hA hB))))
  have left := cleared_relation (A+B) B hNext hB
  exact cancel_right nameF stepF G (data (A+B) B) u (barnesData (A+B) B) (height (A+B) B)
    (regular (A+B) B hNext hB) hu (barnes_regular (A+B) B hB) (barnes_apart (A+B) B hNext hB)
    (cross_trans _ _ _ _ _ _ left (cross_symm _ _ _ _ right))

theorem actual_original_Barnes_hyperfactorial_unit_recurrence_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (let A := var 0; let B := var 1
     le one A ⟶ le one B ⟶ crossEquivalent nameF stepF (data (A+B) B) (stepData A B)) :=
  closeUniv 2 (.impI (.impI (recurrence _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorialRecurrence
