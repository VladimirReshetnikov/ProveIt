import Surreal.HahnSeries.PolynomialInitialRoots

/-!
# Valuation Rouché for Hahn-coefficient polynomials

This proves `polynomial:cor:valrouche` under the strict weighted inequality
`polynomial:eq:valrouche`. A perturbation of higher weighted valuation preserves
both the Gauss value at the chosen center and scale and the entire initial
polynomial. Zero perturbations are included through the value `⊤`.

The root-count consequences take explicit finite split factorizations of the
original and perturbed polynomials. Their degrees and root index types may
be different. Only counts in the specified closed ball, open ball, shell,
and residue directions are preserved. The argument requires no algebraic
closedness, Archimedean exponent group, topology, or contour integration.
-/

namespace Surreal.HahnSeries

open Polynomial
open scoped _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- The weighted-value assertion of `polynomial:cor:valrouche`. The strict
inequality already implies that the original polynomial is nonzero. -/
theorem weightedGaussVal_add_eq_of_lt (a : K⟦Γ⟧) (ρ : Γ) (P E : K⟦Γ⟧[X])
    (h : weightedGaussVal a ρ P < weightedGaussVal a ρ E) :
    weightedGaussVal a ρ (P + E) = weightedGaussVal a ρ P := by
  change (centeredGaussExpansion a ρ (P + E)).orderTop = _
  rw [map_add]
  exact _root_.HahnSeries.orderTop_add_eq_left h

/-- Higher weighted valuation preserves the exact initial polynomial,
including its leading scalar (`polynomial:cor:valrouche`). -/
theorem gaussInitial_add_eq_of_lt (a : K⟦Γ⟧) (ρ : Γ) (P E : K⟦Γ⟧[X])
    (h : weightedGaussVal a ρ P < weightedGaussVal a ρ E) :
    gaussInitial a ρ (P + E) = gaussInitial a ρ P := by
  change (centeredGaussExpansion a ρ (P + E)).leadingCoeff = _
  rw [map_add]
  exact _root_.HahnSeries.leadingCoeff_add_eq_left h

/-- The two simultaneous conclusions in `polynomial:cor:valrouche`, under
the strict hypothesis `polynomial:eq:valrouche`. -/
theorem valuationRouche (a : K⟦Γ⟧) (ρ : Γ) (P E : K⟦Γ⟧[X])
    (h : weightedGaussVal a ρ P < weightedGaussVal a ρ E) :
    weightedGaussVal a ρ (P + E) = weightedGaussVal a ρ P ∧
      gaussInitial a ρ (P + E) = gaussInitial a ρ P :=
  ⟨weightedGaussVal_add_eq_of_lt a ρ P E h, gaussInitial_add_eq_of_lt a ρ P E h⟩

section Split

variable {ι κ : Type*}
  (a : K⟦Γ⟧) (ρ : Γ) (P E : K⟦Γ⟧[X])
  (h : weightedGaussVal a ρ P < weightedGaussVal a ρ E)
  (c d : K⟦Γ⟧) (hc : c ≠ 0) (hd : d ≠ 0)
  (s : Finset ι) (t : Finset κ) (α : ι → K⟦Γ⟧) (β : κ → K⟦Γ⟧)
  (hP : P = C c * ∏ i ∈ s, (X - C (α i)))
  (hPE : P + E = C d * ∏ i ∈ t, (X - C (β i)))

include h hc hd hP hPE

/-- Closed-ball root counts in `polynomial:cor:valrouche`, with every
indexed occurrence counted, so repeated roots retain their multiplicities. -/
theorem valuationRouche_closed_count :
    (closedRootIndices a ρ t β).card = (closedRootIndices a ρ s α).card := by
  rw [← natDegree_gaussInitial_split a ρ d hd t β,
    ← natDegree_gaussInitial_split a ρ c hc s α, ← hPE, ← hP,
    gaussInitial_add_eq_of_lt a ρ P E h]

/-- Open-ball root counts in `polynomial:cor:valrouche`, including roots
at the center, whose zero displacement has valuation `⊤`. -/
theorem valuationRouche_open_count :
    (t.filter (fun i => (ρ : WithTop Γ) < (β i - a).orderTop)).card =
      (s.filter (fun i => (ρ : WithTop Γ) < (α i - a).orderTop)).card := by
  rw [← natTrailingDegree_gaussInitial_split a ρ d hd t β,
    ← natTrailingDegree_gaussInitial_split a ρ c hc s α, ← hPE, ← hP,
    gaussInitial_add_eq_of_lt a ρ P E h]

/-- The shell count follows from the preserved closed- and open-ball
counts, using `polynomial:eq:shellcount`. -/
theorem valuationRouche_shell_count :
    (t.filter (fun i => (β i - a).orderTop = (ρ : WithTop Γ))).card =
      (s.filter (fun i => (α i - a).orderTop = (ρ : WithTop Γ))).card := by
  rw [shell_count_gaussInitial_split a ρ d hd t β,
    shell_count_gaussInitial_split a ρ c hc s α, ← hPE, ← hP,
    gaussInitial_add_eq_of_lt a ρ P E h]

/-- Every residue-direction count is preserved in
`polynomial:cor:valrouche`. The direction `r` is the open valuation ball
centered at `a + t^ρ r` with exponent `ρ`. -/
theorem valuationRouche_direction_count (r : K) :
    (t.filter (fun i => (ρ : WithTop Γ) <
      (β i - (a + _root_.HahnSeries.single ρ r)).orderTop)).card =
      (s.filter (fun i => (ρ : WithTop Γ) <
        (α i - (a + _root_.HahnSeries.single ρ r)).orderTop)).card := by
  rw [← rootMultiplicity_gaussInitial_split_direction a ρ d hd t β r,
    ← rootMultiplicity_gaussInitial_split_direction a ρ c hc s α r,
    ← hPE, ← hP, gaussInitial_add_eq_of_lt a ρ P E h]

end Split

end

end Surreal.HahnSeries
