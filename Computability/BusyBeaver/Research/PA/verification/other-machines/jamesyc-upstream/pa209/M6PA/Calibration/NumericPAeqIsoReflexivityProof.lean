module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceZeroCalibration
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

noncomputable def isoReflexivityTyped : SF (V:=V) 0 :=
  ∀¹ (unary domain (Semiterm.bvar 0) 🡒 binary isoPredicate (Semiterm.bvar 0) (Semiterm.bvar 0))

theorem isoReflexivityTyped_quote : isoReflexivityTyped (V:=V) =
    ⌜RelationalSource.PairGraph.orderIsoReflexivityStatement⌝ := by
  simp [isoReflexivityTyped, RelationalSource.PairGraph.orderIsoReflexivityStatement,
    ←FFL.FirstOrder.Semiterm.typed_quote_bvar]

variable {T : InternalTheory V L}
noncomputable def isoReflexivityProof (x : ST (V:=V) 0) :
    ND.Proof (T:=T) (insert (∼isoReflexivityTyped) ∅)
      (unary domain x 🡒 binary isoPredicate x x) := by
  have h : ND.Proof (T:=T) (insert (∼isoReflexivityTyped) ∅)
      (isoReflexivityTyped (V:=V)) := ND.assumption _ (by simp)
  simpa [isoReflexivityTyped, Bootstrapping.Semiformula.substs_imp] using ND.allElim h x

theorem isoReflexivity_instance_val (x : ST (V:=V) 0) :
    (unary domain x 🡒 binary isoPredicate x x).val =
      imp L (NumericPAeqTerm.domainCode x.val) (NumericPAeqValueIsoGuard.isoCode x.val x.val) := by
  rfl
#print axioms isoReflexivityTyped_quote
#print axioms isoReflexivityProof
#print axioms isoReflexivity_instance_val
end M6.PA.NumericPAeqValueCoherence
