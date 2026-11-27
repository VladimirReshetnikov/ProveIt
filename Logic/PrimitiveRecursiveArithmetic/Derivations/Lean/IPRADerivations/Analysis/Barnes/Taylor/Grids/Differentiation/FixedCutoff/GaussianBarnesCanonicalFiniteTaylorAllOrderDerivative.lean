import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.FixedCoefficients.GaussianBarnesCanonicalFixedTaylorDerivativeFirstSuccessor
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeOrderInvariance
import IPRADerivations.Analysis.Barnes.Taylor.Grids.Differentiation.FixedCutoff.GaussianBarnesCanonicalFiniteTaylorDerivativeSuccessor

/-!
# Every derivative order of a literal finite Barnes partial product

Order zero names the literal product. One modulus treats the first
transition and every positive successor using the same finite cutoff.
The source and target may retain different degrees if each name
retains its requested coefficient.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorAllOrderDerivative

open_ipra
open ComplexLogarithmRemainder (add bounded_mono normSq)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianL1 (norm1)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Q" => GaussianBarnesCanonicalFiniteTaylorNamedQuotient.nameF
local notation "qd" => GaussianBarnesCanonicalFiniteTaylorNamedQuotient.data
local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "V" => GaussianBarnesCanonicalValue.prefixF
local notation "vd" => GaussianBarnesCanonicalProduct.literalData
local notation "baseClock" => GaussianBarnesCanonicalFixedTaylorDerivativeFirstSuccessor.stepClock
local notation "higherClock" => GaussianBarnesCanonicalFiniteTaylorDerivativeSuccessor.stepClock

def stepClock (p R e : PTm n) : PTm n := baseClock p R+higherClock p R (pred e) e

private theorem widen (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] source z (R+one) B :=
  .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))

theorem zero_cross (z R B r J : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent F V (fd z (R+one) B r J zero) (vd z (R+one) B (initial (R+one)+r)) :=
  GaussianBarnesCanonicalFixedTaylorDerivativeZero.value_cross z (R+one) B r J (widen z R B hz)

theorem canonical_retention (e : PTm n) : Γ ⊢[PRAAx] le (succ e) (previous (pred e)) := by
  refine .orE (lt_or_le zero e) ?_ ?_
  · exact le_congr (congrSucc (Common.pos_of_one_le Prf.hyp0)).eqSymm (.eqRefl _) (le_refl _)
  · have ez : (le e zero :: Γ) ⊢[PRAAx] (zero : PTm n) ≐ e := le_antisymm (zero_le e) Prf.hyp0
    exact le_congr (congrSucc ez) (.eqRefl _) (zero_lt_succ (succ (pred e)))

private theorem retarget (p x z R B r J K e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hx : Γ ⊢[PRAAx] pointCN Q x)
    (hJ : Γ ⊢[PRAAx] le e (previous J)) (hK : Γ ⊢[PRAAx] le e (previous K))
    (h : Γ ⊢[PRAAx] independentRate Q F x (fd z R B r J e) one (unit p)) :
    Γ ⊢[PRAAx] independentRate Q F x (fd z R B r K e) one (unit p) :=
  GaussianNamedRateTransport.transport Q F Q F x (fd z R B r J e) x (fd z R B r K e) one (unit p)
    (unit_positive p) h (cross_refl _ _ hx)
    (GaussianBarnesCanonicalTaylorDerivativeOrderInvariance.fixed_cross z R B r K J e hz hK hJ)

@[simp] private theorem subst_fixed {m : ℕ} (σ : Fin n → PTm m) (z R B r J e : PTm n) :
    Syn.subst σ (fd z R B r J e) =
      fd (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ J) (Syn.subst σ e) := by
  simp [GaussianBarnesCanonicalFixedTaylorDerivativeName.data,GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientData,
    GaussianBarnesCanonicalFiniteCentralExponential.finiteData,GaussianBarnesCanonicalFiniteCentralExponential.prefixExpData,
    GaussianBarnesCanonicalSingleExponential.prefixData,GaussianBarnesCanonicalSingleExponential.prefactorExponentData,
    GaussianGammaFiniteApproximantName.exponentialInputData,LeanProofs.IPRA.Analysis.Products.fact]

@[simp] private theorem subst_quotient {m : ℕ} (σ : Fin n → PTm m) (z h R B r J e : PTm n) :
    Syn.subst σ (qd z h R B r J e) = qd (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ r) (Syn.subst σ J) (Syn.subst σ e) := by
  simp [GaussianBarnesCanonicalFiniteTaylorNamedQuotient.data,one]

private theorem order_congr (p z h R B r J K e i : PTm n)
    (he : Γ ⊢[PRAAx] e ≐ i)
    (hr : Γ ⊢[PRAAx] independentRate Q F (qd z h R B r J e) (fd z (R+one) B r K (succ e)) one (unit p)) :
    Γ ⊢[PRAAx] independentRate Q F (qd z h R B r J i) (fd z (R+one) B r K (succ i)) one (unit p) := by
  let sh (x : PTm n) := Syn.shift x
  let φ : Fm PTm (n+1) := independentRate Q F (qd (sh z) (sh h) (sh R) (sh B) (sh r) (sh J) (var 0))
    (fd (sh z) (sh (R+one)) (sh B) (sh r) (sh K) (succ (var 0))) one (sh (unit p))
  have start : Γ ⊢[PRAAx] φ.subst (Syn.inst e) := by simpa [φ,sh] using hr
  simpa [φ,sh] using Prf.eqSubst1 φ he start

theorem rate (p z h R B r J K e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (he : Γ ⊢[PRAAx] le e (previous J)) (hK : Γ ⊢[PRAAx] le (succ e) (previous K))
    (hs : Γ ⊢[PRAAx] le (norm1 h*unit (stepClock p R e)) B) : Γ ⊢[PRAAx]
    independentRate Q F (qd z h R B r J e) (fd z (R+one) B r K (succ e)) one (unit p) := by
  let a := baseClock p R
  let b := higherClock p R (pred e) e
  let H := norm1 h
  have h₀ : Γ ⊢[PRAAx] le (H*unit a) B :=
    le_trans (Common.mul_le_mul (le_refl H) (unit_monotone (le_add_right a b))) hs
  have h₁ : Γ ⊢[PRAAx] le (H*unit b) B :=
    le_trans (Common.mul_le_mul (le_refl H) (unit_monotone (le_add_left b a))) hs
  refine .orE (lt_or_le zero e) ?_ ?_
  · have near := GaussianBarnesCanonicalFiniteTaylorDerivativeSuccessor.positive_order_rate p z h R B r J e
      hz.wk hw.wk hn.wk Prf.hyp0 he.wk h₁.wk
    exact retarget p _ z (R+one) B r (pred e) K (succ e) (widen z R B hz.wk)
      (GaussianBarnesCanonicalFiniteTaylorNamedQuotient.regular z h R B r J e hz.wk hw.wk hn.wk he.wk)
      (canonical_retention e) hK.wk near
  · let Δ := le e zero :: Γ
    have ez : Δ ⊢[PRAAx] (zero : PTm n) ≐ e := le_antisymm (zero_le e) Prf.hyp0
    have keep : Δ ⊢[PRAAx] le one (previous K) := le_congr (congrSucc ez).eqSymm (.eqRefl _) hK.wk
    have near := GaussianBarnesCanonicalFixedTaylorDerivativeFirstSuccessor.dyadic_rate (Γ := Δ) p z h R B r J
      hz.wk hn.wk h₀.wk
    have fixed := retarget p (qd z h R B r J zero) z (R+one) B r J K one (widen z R B hz.wk)
      (GaussianBarnesCanonicalFiniteTaylorNamedQuotient.regular z h R B r J zero hz.wk hw.wk hn.wk (zero_le _))
      (zero_lt_succ (succ J)) keep near
    exact order_congr p z h R B r J K zero e ez fixed

theorem canonical_rate (p z h R B r J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (he : Γ ⊢[PRAAx] le e (previous J))
    (hs : Γ ⊢[PRAAx] le (norm1 h*unit (stepClock p R e)) B) : Γ ⊢[PRAAx]
    independentRate Q F (qd z h R B r J e) (fd z (R+one) B r (pred e) (succ e)) one (unit p) :=
  rate p z h R B r J (pred e) e hz hw hn he (canonical_retention e) hs

theorem actual_Barnes_finite_all_retained_factorial_Taylor_derivatives_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let r := var 5
     let J := var 6
     let K := var 7
     let e := var 8
     (source z R B ⋏ source (add z h) R B ⋏ le one (normSq h)) ⟶
       (le e (previous J) ⋏ le (succ e) (previous K)) ⟶ le (norm1 h*unit (stepClock p R e)) B ⟶
       independentRate Q F (qd z h R B r J e) (fd z (R+one) B r K (succ e)) one (unit p)) :=
  closeUniv 9 (.impI (.impI (.impI (rate _ _ _ _ _ _ _ _ _
    Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorAllOrderDerivative
