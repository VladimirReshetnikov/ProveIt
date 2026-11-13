import Positive75To74
import OwnZeroUnits74
import Ring78To75
import FirstRootBridge

/-! Source-only same-coordinate reverse zero transfer. It obtains the 74
unit factors from the 74 zero constructed from the given 75 zero. Imported
client drafts and tactics remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Model75To78Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticAdaptiveFactorMagnitude2011
open FirstFactor74Draft OwnZeroProduct74Draft OwnZeroUnits74Draft FactorResidues74Draft
open DirectFirstRootModelDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A positive 75 zero has all five 75 factor values equal to one. The
unit extraction is performed at the explicitly constructed 74 zero. -/
theorem factors_of_75_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hb : 0<beta) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P75NegativePell.graph p).output v) :
    let z : Fin 14 → DiffRing V := fun j => ι (v j)
    (P75NegativePell.graph p).first.evalRing z=1 ∧
    (P75NegativePell.graph p).main.evalRing z=1 ∧
    (P75NegativePell.graph p).aux.evalRing z=1 ∧
    (P75NegativePell.graph p).strong.evalRing z=1 ∧
    (P75NegativePell.graph p).guardFactor.evalRing z=1 := by
  let w : Fin 14 → V := Positive75To74Draft.forward v
  have hw : ∀ j, 0<w j := Positive75To74Draft.forward_positive v hv
  have hwzero : InternalZero (P74PositiveGuard.graph p).output w := by
    apply (internalZero_iff _ _).mpr
    have he := Ring75To74Draft.output_eval p (fun j => ι (v j))
    rw [←Positive75To74Draft.cast_forward v] at he
    change (P74PositiveGuard.graph p).output.evalRing (fun j => ι (w j)) =
      (P75NegativePell.graph p).output.evalRing (fun j => ι (v j)) at he
    rw [he]
    exact (internalZero_iff _ _).mp hz
  obtain ⟨hmain,haux,hstrong⟩ := restricted_residues p w
  have hu := factor_units_of_zero p beta w hbeta hb (hw 0) (hw 6) (hw 7)
    hwzero hmain haux hstrong
  have hfirst : (P74PositiveGuard.graph p).first.evalRing (fun j => ι (w j))=1 := by
    rw [first_eval p beta w hbeta,hu.1]
    simp only [map_add,map_one]
    ring
  have hmain1 := (unit_iff_one (P74PositiveGuard.graph p).main w).mp hu.2.1
  have haux1 := (unit_iff_one (P74PositiveGuard.graph p).aux w).mp hu.2.2.1
  have hguard1 := (unit_iff_one (P74PositiveGuard.graph p).guardFactor w).mp hu.2.2.2.1
  have hstrong1 := (unit_iff_one (P74PositiveGuard.graph p).strong w).mp hu.2.2.2.2
  have hevals := Ring75To74Draft.restricted_eval p (fun j => ι (v j))
  have heguard := Ring75To74Draft.guard_eval p (fun j => ι (v j))
  rw [←Positive75To74Draft.cast_forward v] at hevals heguard
  change (P74PositiveGuard.graph p).first.evalRing (fun j => ι (w j)) =
      (P75NegativePell.graph p).first.evalRing (fun j => ι (v j)) ∧
    (P74PositiveGuard.graph p).main.evalRing (fun j => ι (w j)) =
      (P75NegativePell.graph p).main.evalRing (fun j => ι (v j)) ∧
    (P74PositiveGuard.graph p).aux.evalRing (fun j => ι (w j)) =
      (P75NegativePell.graph p).aux.evalRing (fun j => ι (v j)) ∧
    (P74PositiveGuard.graph p).strong.evalRing (fun j => ι (w j)) =
      (P75NegativePell.graph p).strong.evalRing (fun j => ι (v j)) at hevals
  change (P74PositiveGuard.graph p).guardFactor.evalRing (fun j => ι (w j)) =
    (P75NegativePell.graph p).guardFactor.evalRing (fun j => ι (v j)) at heguard
  exact ⟨hevals.1.symm.trans hfirst,hevals.2.1.symm.trans hmain1,
    hevals.2.2.1.symm.trans haux1,hevals.2.2.2.symm.trans hstrong1,
    heguard.symm.trans hguard1⟩

/-- A positive 75 zero is a 78 zero at the original valuation. No guard
subtraction, K cast, mask bound or alternate 78 witness is used. -/
theorem zero_78_of_75_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hb : 0<beta) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P75NegativePell.graph p).output v) :
    InternalZero (P78AuxRoot.graph p).output v := by
  let z : Fin 14 → DiffRing V := fun j => ι (v j)
  have hf := factors_of_75_zero p beta v hbeta hb hv hz
  change (P75NegativePell.graph p).first.evalRing z=1 ∧
    (P75NegativePell.graph p).main.evalRing z=1 ∧
    (P75NegativePell.graph p).aux.evalRing z=1 ∧
    (P75NegativePell.graph p).strong.evalRing z=1 ∧
    (P75NegativePell.graph p).guardFactor.evalRing z=1 at hf
  rcases hf with ⟨hf0,hf1,hfa,hfs,hfg⟩
  rcases Ring78To75Draft.factor_evals p z with ⟨he0,he1,hea,hes,heg⟩
  have h0 : (P78AuxRoot.graph p).A0.evalRing z=0 := by rw [he0] at hf0; linarith
  have h1 : (P78AuxRoot.graph p).A1.evalRing z=0 := by rw [he1] at hf1; linarith
  have ha : (P78AuxRoot.graph p).aux.evalRing z-1=0 := by rw [hea] at hfa; exact sub_eq_zero.mpr hfa
  have hs : (P78AuxRoot.graph p).gap.evalRing z=0 := by rw [hes] at hfs; linarith
  have hg : (P78AuxRoot.graph p).guardResidual.evalRing z=0 := by rw [heg] at hfg; linarith
  rw [internalZero_iff,P78AuxRoot.output_shape]
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one]
  change fiveSquares ((P78AuxRoot.graph p).A0.evalRing z)
    ((P78AuxRoot.graph p).A1.evalRing z) ((P78AuxRoot.graph p).aux.evalRing z-1)
    ((P78AuxRoot.graph p).gap.evalRing z) ((P78AuxRoot.graph p).guardResidual.evalRing z)=0
  exact (fiveSquares_eq_zero_iff _ _ _ _ _).mpr ⟨h0,h1,ha,hs,hg⟩

end DiophantineConsistency.Model75To78Draft

#print axioms DiophantineConsistency.Model75To78Draft.factors_of_75_zero
#print axioms DiophantineConsistency.Model75To78Draft.zero_78_of_75_zero
