import FreshModel106

/-! Literal 66-row integer graph and all-model/iPRA transfer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Current2011Unscaled66Fresh
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts ModelArithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  let J : Expr (Fin 14) := .var 0
  let F : Expr (Fin 14) := .var 1
  let alpha : Expr (Fin 14) := .var 2
  let z : Expr (Fin 14) := .var 3
  let f : Expr (Fin 14) := .var 4
  let i : Expr (Fin 14) := .var 5
  let T : Expr (Fin 14) := .var 6
  let s : Expr (Fin 14) := .var 7
  let w : Expr (Fin 14) := .var 8
  let n : Expr (Fin 14) := .var 9
  let eta : Expr (Fin 14) := .var 10
  let zeta : Expr (Fin 14) := .var 11
  let y : Expr (Fin 14) := .var 12
  let gamma : Expr (Fin 14) := .var 13
  let beta : Expr (Fin 14) := .constant (p 0)
  let K0 : Expr (Fin 14) := .constant (p 1)
  let MC : Expr (Fin 14) := .constant (p 2)
  let MF : Expr (Fin 14) := .constant (p 3)
  let qm := beta * J
  let q := qm + 1
  let q2 := q * q
  let q3 := q2 * q
  let X := w * q
  let Y := s * q3
  let E := X * Y
  let k := eta + zeta
  let kY := k * Y
  let ell := E * kY
  let c := kY + eta
  let a := E + Y
  let four_a := 4 * a
  let H := four_a + 3
  let a2 := a * a
  let Delta := a2 + H
  let ac := a * c
  let main_base := X + ac
  let gammaH := gamma * H
  let main_root := main_base + gammaH
  let c2 := c * c
  let Dc2 := Delta * c2
  let main_square := main_root * main_root
  let N1 := main_square - Dc2
  let qF := q - F
  let C := qF - alpha
  let gap_product := qm * qF
  let gap := gap_product + alpha
  let q2minus1 := q2 - 1
  let rproduct := gap * q2minus1
  let qMF := q * MF
  let maskfactor := MC + qMF
  let mask := maskfactor * J
  let R := rproduct + mask
  let En := E * n
  let tau_partial := En + k
  let tau := tau_partial - R
  let tau2 := tau * tau
  let ell_plus_k := ell + k
  let first_product := ell * ell_plus_k
  let N0 := tau2 - first_product
  let Kw := K0 + w
  let transport := Kw * C
  let transport_partial := transport + qF
  let zqm := z * qm
  let Nt := transport_partial - zqm
  let f2 := f * f
  let cT := c * T
  let cTminusR := cT - R
  let f2inner := f2 * cTminusR
  let V := f2inner - c
  let i2 := i * i
  let i2Dc2 := i2 * Dc2
  let strongTerm := i2Dc2 * c2
  let Z := f2 - strongTerm
  let auxCoefficient := Delta * strongTerm
  let V2 := V * V
  let y2 := y * y
  let squareGap := V2 - y2
  let auxProduct := auxCoefficient * squareGap
  let Na := auxProduct + y2
  let product0 := N0 * N1
  let product1 := product0 * Na
  let product2 := product1 * Nt
  let product3 := product2 * Z
  let polynomial := product3 - 1
  polynomial

section Eval
variable {R : Type*} [CommRing R]

def unscaledValue (p : Fin 4 → R) (v : Fin 14 → R) : R :=
  let d := Carrier65.core p v
  d.P * d.Q * d.U * d.W * Carrier65.strong d - 1

theorem strong_factor (d i c : R) :
    (i*i)*(d*(c*c))*(c*c) = d*((i*(c*c))*(i*(c*c))) := by ring

theorem aux_factor (d i c : R) :
    d * (d*((i*(c*c))*(i*(c*c)))) = ((i*d)*(c*c))*((i*d)*(c*c)) := by ring

theorem evalRing_expressionAt (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (expressionAt p).evalRing v = unscaledValue (fun j => (p j : R)) v := by
  simp only [expressionAt, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    unscaledValue, Carrier65.strong, Carrier65.core, pow_succ, pow_zero, one_mul,
    strong_factor, aux_factor]
  simp only [mul_assoc]

theorem scaled_identity (p : Fin 4 → R) (v : Fin 14 → R) :
    Carrier65.value p v = (Carrier65.core p v).delta * unscaledValue p v :=
  Carrier65.scaled_identity p v

end Eval

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sameZero138 (v : Fin 14 → V) :
    InternalZero (positiveShift (expressionAt CurrentWindowCarry2011.ports)) v ↔
      InternalZero ObjectCurrentEquation2011.naturalExpression v := by
  change InternalZero (positiveShift (expressionAt CurrentWindowCarry2011.ports)) v ↔
    InternalZero (positiveShift ObjectCurrentEquation2011.expression) v
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    evalRing_expressionAt, ObjectCurrentEquation2011.expression, FreshModel106.evalRing_expressionAt65]
  have hd : (Carrier65.core
      (fun j => ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V))
      (fun j => ι (v j + 1))).delta ≠ 0 :=
    (ModelCarrierScaled.delta_pos model_discrete _ _
      FreshModel106.beta_pos (FreshModel106.shifted_pos v)).ne'
  rw [scaled_identity, mul_eq_zero]
  simp only [hd, false_or]

end Model

theorem bridge138 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt CurrentWindowCarry2011.ports)) := by
  intro V _ _
  have eqv : (FoundationHANoZero.classicalNoZero (positiveShift
      (expressionAt CurrentWindowCarry2011.ports))).Evalb (M := V) ![] ↔
      (FoundationHANoZero.classicalNoZero ObjectCurrentEquation2011.naturalExpression).Evalb (M := V) ![] := by
    rw [HAExpressionAssembly.classicalNoZero_iff, HAExpressionAssembly.classicalNoZero_iff]
    simpa only [InternalZero, ne_eq] using
      (forall_congr' fun v : Fin 14 → V => not_congr (sameZero138 v))
  exact eqv.trans (HACurrentEquation2011.polynomialBridge V)

theorem native_equivalence138 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge138

theorem standard_equivalence138 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence138

#print axioms evalRing_expressionAt
#print axioms scaled_identity
#print axioms sameZero138
#print axioms bridge138
#print axioms standard_equivalence138

end DiophantineConsistency.Current2011Unscaled66Fresh
