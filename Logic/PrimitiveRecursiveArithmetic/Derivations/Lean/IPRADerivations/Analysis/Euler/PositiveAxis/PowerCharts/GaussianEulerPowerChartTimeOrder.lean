import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartOrder
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRealOrderTransport

/-!
# Transitivity of named order and monotonicity in physical time

The original real order retains its two endpoint allowances under
composition. Positive rational chart times can be compared on a common
compact domain computed from their numerators and denominators.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartTimeOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNamedRealOrderTransport (precision upperSlack remove_upper_slack)
open GaussianEulerPositivePowerChart (parameters nameF data)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper upper_triangle upper_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem order_trans_at (f g h : PR 2) (x y z p q : PTm n)
    (hf : Γ ⊢[PRAAx] realOrder f g x y) (hg : Γ ⊢[PRAAx] realOrder g h y z) :
    Γ ⊢[PRAAx] upper (fstT (ap2 f p x)) (fstT (ap2 h q z)) (unit p+unit q) (unit p*unit q) := by
  let a := fstT (ap2 f p x)
  let c := fstT (ap2 h q z)
  let t := precision a c (unit p*unit q) two
  have hL := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive t)
  have hR := positive_product _ _ (unit_positive (Γ := Γ) t) (unit_positive q)
  have left := real_order_at f g x y p t hf
  have right := real_order_at g h y z t q hg
  have joined := upper_triangle _ _ _ _ _ _ _ left right
  apply remove_upper_slack a c (unit p+unit q) (unit p*unit q) two
  unfold upperSlack
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ hL hR) joined
    (le_of_eq_add (d := zero) (by ipra_ring))

theorem order_trans (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] realOrder f g x y) (hg : Γ ⊢[PRAAx] realOrder g h y z) :
    Γ ⊢[PRAAx] realOrder f h x z := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have fs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] realOrder f g (sh x) (sh y) :=
    by simpa [Fm.shift,Syn.shift,sh] using hf.shift.shift
  have gs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] realOrder g h (sh y) (sh z) :=
    by simpa [Fm.shift,Syn.shift,sh] using hg.shift.shift
  simpa only [realOrder,Syn.shift,sh] using
    order_trans_at f g h (sh x) (sh y) (sh z) (var 1) (var 0) fs gs

private theorem common_source (e f d h Q S a b c v : PTm n)
    (hp : Γ ⊢[PRAAx] parameters e f d h Q S)
    (ha : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b)
    (hc : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source c v)
    (ho : Γ ⊢[PRAAx] le (a*v) (b*c)) :
    Γ ⊢[PRAAx] GaussianEulerPositivePowerChartOrder.source e f d h Q S (b*v) (a+c) a b c v := by
  have inverse := positive_product b v ha.andE₂ hc.andE₂
  have lb : Γ ⊢[PRAAx] le b ((b*v)*a) :=
    le_congr (one_mul b) (by ipra_ring)
      (mul_le_mul_right b (positive_product v a hc.andE₂ ha.andE₁))
  have lv : Γ ⊢[PRAAx] le v ((b*v)*c) :=
    le_congr (one_mul v) (by ipra_ring)
      (mul_le_mul_right v (positive_product b c ha.andE₂ hc.andE₁))
  have ua : Γ ⊢[PRAAx] le a ((a+c)*b) :=
    le_trans (le_add_right a c)
      (le_congr (one_mul (a+c)) (mul_comm _ _) (mul_le_mul_right (a+c) ha.andE₂))
  have uc : Γ ⊢[PRAAx] le c ((a+c)*v) :=
    le_trans (le_add_left c a)
      (le_congr (one_mul (a+c)) (mul_comm _ _) (mul_le_mul_right (a+c) hc.andE₂))
  exact .andI (.andI hp (.andI inverse (.andI ha (.andI lb ua))))
    (.andI (.andI hc (.andI lv uc)) ho)

theorem chart_time_order (e f d h Q S a b c v : PTm n)
    (hp : Γ ⊢[PRAAx] parameters e f d h Q S)
    (ha : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b)
    (hc : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source c v)
    (ho : Γ ⊢[PRAAx] le (a*v) (b*c)) :
    Γ ⊢[PRAAx] realOrder nameF nameF (data e f d h S a b) (data e f d h S c v) := by
  refine .allI (.allI ?_)
  let sh (w : PTm n) := Syn.shift (Syn.shift w)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      GaussianEulerPositivePowerChartOrder.source (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S)
        (sh b*sh v) (sh a+sh c) (sh a) (sh b) (sh c) (sh v) := by
    simpa [Fm.shift,Syn.shift,sh,GaussianEulerPositivePowerChartOrder.source,
      GaussianEulerPositivePowerChart.source,parameters,one] using
      (common_source e f d h Q S a b c v hp ha hc ho).shift.shift
  simpa only [realOrder,Syn.shift,sh,GaussianEulerPositivePowerChart.subst_data] using
    GaussianEulerPositivePowerChartOrder.original_observations (var 1) (var 0) (sh e) (sh f) (sh d) (sh h)
      (sh Q) (sh S) (sh b*sh v) (sh a+sh c) (sh a) (sh b) (sh c) (sh v) hs

theorem original_named_real_order_transitive_closed (f g h : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((realOrder f g (var 0) (var 1) ⋏ realOrder g h (var 1) (var 2)) ⟶ realOrder f h (var 0) (var 2)) :=
  closeUniv 3 (.impI (order_trans f g h _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_power_chart_time_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((parameters (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⋏
        (GaussianPositiveRationalLogarithm.source (var 6) (var 7) ⋏
          (GaussianPositiveRationalLogarithm.source (var 8) (var 9) ⋏ le (var 6*var 9) (var 7*var 8)))) ⟶
      realOrder nameF nameF (data (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) (var 7))
        (data (var 0) (var 1) (var 2) (var 3) (var 5) (var 8) (var 9))) :=
  closeUniv 10 (.impI (chart_time_order _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartTimeOrder
