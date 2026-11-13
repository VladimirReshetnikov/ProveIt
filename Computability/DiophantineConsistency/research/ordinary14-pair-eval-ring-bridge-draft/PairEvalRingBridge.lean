import FiveUnitFacts
import DiophantineConsistency.ModelDifferenceRing

/-! Source-only generic transfer from a stated ring evaluation to an
internal signed-pair representation. No graph evaluation is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.PairEvalRingBridgeDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveFactorUnits2011
open FiveUnitFactsDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An explicit difference-ring value determines the corresponding signed
pair up to cross-sum equivalence. -/
theorem represented_of_ring_eval {σ : Type*} (e : Expr σ) (v : σ → V) (a b : V)
    (h : e.evalRing (fun j => ι (v j))=ι a-ι b) :
    Equivalent (pairEval e v) (a,b) := by
  have hs := split_evalRing e (fun j => ι (v j))
  rw [←evalSemiring_map ι e.splitNatural.1 v,
      ←evalSemiring_map ι e.splitNatural.2 v] at hs
  change ι (pairEval e v).1-ι (pairEval e v).2=e.evalRing (fun j => ι (v j)) at hs
  change (pairEval e v).1+b=(pairEval e v).2+a
  apply ι_injective
  simp only [map_add]
  linear_combination hs + h

/-- Replacing the first factor by an equivalent signed pair preserves any
five-factor product equivalence, in either direction. -/
theorem product5_first_iff (p p' q r s t u : Pair V) (hp : Equivalent p p') :
    Equivalent (product5 p q r s t) u ↔ Equivalent (product5 p' q r s t) u := by
  have he : Equivalent (product5 p q r s t) (product5 p' q r s t) := by
    unfold product5
    exact equivalent_multiply
      (equivalent_multiply (equivalent_multiply (equivalent_multiply hp
        (equivalent_refl q)) (equivalent_refl r)) (equivalent_refl s)) (equivalent_refl t)
  constructor
  · intro h; exact equivalent_trans (equivalent_symm he) h
  · intro h; exact equivalent_trans he h

/-- A literal first expression with this stated ring value can feed the
reviewed five-unit fact when the product and residue hypotheses are supplied. -/
theorem five_positive_of_first_eval {σ : Type*} (e : Expr σ) (v : σ → V)
    (m x k : V) (hm : 2≤m) (q r s t : Pair V)
    (he : e.evalRing (fun j => ι (v j))=ι (x*x)-ι ((m*k)*(m*k+k)))
    (hp : Equivalent (product5 (pairEval e v) q r s t) (natural (1:V)))
    (hq : pairResidue q ≠ -1) (hr : pairResidue r ≠ -1)
    (ht : pairResidue t ≠ -1) :
    x*x=(m*k)*(m*k+k)+1 ∧ q.1=q.2+1 ∧ r.1=r.2+1 ∧
      s.1=s.2+1 ∧ t.1=t.2+1 := by
  have hrep := represented_of_ring_eval e v (x*x) ((m*k)*(m*k+k)) he
  have hprod := (product5_first_iff (pairEval e v) (x*x,(m*k)*(m*k+k)) q r s t
    (natural (1:V)) hrep).mp hp
  exact five_positive_of_direct_first m x k hm q r s t hprod hq hr ht

end DiophantineConsistency.PairEvalRingBridgeDraft

#print axioms DiophantineConsistency.PairEvalRingBridgeDraft.represented_of_ring_eval
#print axioms DiophantineConsistency.PairEvalRingBridgeDraft.product5_first_iff
#print axioms DiophantineConsistency.PairEvalRingBridgeDraft.five_positive_of_first_eval
