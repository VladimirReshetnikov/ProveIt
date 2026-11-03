import DiophantineConsistency.ModelRepArith
import DiophantineConsistency.ArithmeticPow
import DiophantineConsistency.ArithmeticBinomFactorial

/-! # Interfaces for the internal power, binomial and factorial graphs

The three coordinate graphs below are the arithmetic leaves of the CRT
certificate of `BoundedForallRepresentation`. Their internal correctness is
stated here as `PowCase`, `BinomCase`, `FactCase` (internally `ArithmeticPow.power`,
`ArithmeticBinomPascal.binom`, `ArithmeticBinomFactorial.fact`) and proved in
separate modules:

* `ModelRepPower.powCase : PowCase` (Pell/Matiyasevich, via `ModelRepPell`);
* `ModelRepBinomial.binomCase_of : PowCase → BinomCase` (digit formula);
* `ModelRepFactorial.factCase_of : PowCase → BinomCase → FactCase`.

The substitution lemmas `graphHolds_pow`, `graphHolds_binomial`,
`graphHolds_factorial` transport them to the derived constructors
`GraphRep.pow`, `GraphRep.binomial`, `GraphRep.factorial`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelRepInterfaces
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelRep ModelScalarPR ModelRepBasic ModelRepArith

/-- Internal correctness of the Pell-based exponentiation graph. -/
abbrev PowCase : Prop :=
  GraphHolds PowerRepresentation.coordinates
    (fun V _ _ v => ArithmeticPow.power (v 0) (v 1))

/-- Internal correctness of the digit-extraction binomial graph. -/
abbrev BinomCase : Prop :=
  GraphHolds FactorialRepresentation.binomialCoordinates
    (fun V _ _ v => ArithmeticBinomPascal.binom (v 0) (v 1))

/-- Internal correctness of the ceiling-quotient factorial graph. -/
abbrev FactCase : Prop :=
  GraphHolds FactorialRepresentation.factorialCoordinates
    (fun V _ _ v => ArithmeticBinomFactorial.fact (v 0))

section Substitution
variable {σ : Type*}

theorem graphHolds_pow (hp : PowCase) {f g : (σ → ℕ) → ℕ} {r : GraphRep f}
    {s : GraphRep g} {F G : ModelFun σ} (hr : GraphHolds r F) (hs : GraphHolds s G) :
    GraphHolds (r.pow s) (fun V _ _ v => ArithmeticPow.power (F V v) (G V v)) :=
  graphHolds_composeTwo hp hr hs

theorem graphHolds_binomial (hb : BinomCase) {f g : (σ → ℕ) → ℕ} {r : GraphRep f}
    {s : GraphRep g} {F G : ModelFun σ} (hr : GraphHolds r F) (hs : GraphHolds s G) :
    GraphHolds (r.binomial s) (fun V _ _ v => ArithmeticBinomPascal.binom (F V v) (G V v)) :=
  graphHolds_composeTwo hb hr hs

theorem graphHolds_factorial (hf : FactCase) {f : (σ → ℕ) → ℕ} {r : GraphRep f}
    {F : ModelFun σ} (hr : GraphHolds r F) :
    GraphHolds r.factorial (fun V _ _ v => ArithmeticBinomFactorial.fact (F V v)) :=
  graphHolds_compose (G := fun _ => F) hf (fun _ => hr)

end Substitution

end DiophantineConsistency.ModelRepInterfaces
