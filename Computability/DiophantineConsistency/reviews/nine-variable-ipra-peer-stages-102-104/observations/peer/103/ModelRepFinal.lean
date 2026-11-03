import DiophantineConsistency.ModelBoundedForall
import DiophantineConsistency.ModelRepPower
import DiophantineConsistency.ModelRepBinomial
import DiophantineConsistency.ModelRepFactorial

/-! # Internal correctness of every compiled scalar primitive recursive graph

Assembly of the internalized compiler: the arithmetic leaves (`powCase`,
`binomCase_of`, `factCase_of`) give the CRT certificate (`certificateCase`),
which gives the bounded universal quantifier and the primitive-recursion trace
(`precCase`). Hence, inside every model of `𝗜𝚺₁`, the compiled graph
`c.graphRep` of every program `c` is correct for the internal semantics
`ModelScalarPR.evalV c`, and so is its existential acceptance. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelRepFinal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelRep ModelScalarPR ModelRepBasic

theorem binomCase : ModelRepInterfaces.BinomCase :=
  ModelRepBinomial.binomCase_of ModelRepPower.powCase

theorem factCase : ModelRepInterfaces.FactCase :=
  ModelRepFactorial.factCase_of ModelRepPower.powCase binomCase

/-- Internal correctness of the CRT bounded-universal certificate. -/
theorem certificateCase : ModelRepPrec.CertificateCase :=
  ModelBoundedForall.certificateCase_of ModelRepPower.powCase binomCase factCase

/-- The primitive-recursion case of `ModelRepBasic.graphRep_holds`. -/
theorem precCase : ModelRepBasic.PrecCase :=
  ModelRepPrec.precCase_of_certificate certificateCase

/-- Every compiled program graph is internally correct for `evalV`. -/
theorem graphRep_holds (c : ScalarPRCode) : GraphHolds c.graphRep (evalFun c) :=
  ModelRepBasic.graphRep_holds precCase c

/-- Internal correctness of existential acceptance for a compiled program. -/
theorem existsValue_holds (c : ScalarPRCode) (accepted : ℕ) :
    Holds (GraphRep.existsValue c.graphRep accepted)
      (fun V _ _ _ => ∃ t : V, evalV c t = (accepted : V)) :=
  ModelRepBasic.existsValue_holds precCase c accepted

end DiophantineConsistency.ModelRepFinal
