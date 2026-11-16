# Checked finite core for the iPRA framework

Build with Lean 4.32.0 using `bash build.sh`.  The only dependency is `Std`.
See `FORMALIZATION.md` for every theorem's scope, exact unproved targets, and
the route from fixed PR programs to object-iPRA derivations.

- `RankedDescent.lean`: host finite descent and contraction lemmas.
- `CoherentTower.lean`: host finite lift coherence and uniqueness.
- `ObjectComposition.lean`: actual object-iPRA contract composition,
  specialization, induction interface, and an instantiated induction example.
- `DescentTargets.lean`: complete PR code and object formula definitions for
  the general descent compiler; the compiler itself remains a stated goal.
- `ApplicationTargets.lean`: concrete multivariate polynomial arrays,
  Jacobians, frozen-inverse iteration, rational jets, residues, projections,
  and completely specified Taylor, lifting, coherence and presentation goals.
- `WeightedNormTargets.lean`: exact rational coefficient lists, monic
  Y-reduction, multiplication matrix and determinant, weighted norm and all
  zero-count and dimension targets.
- `HurwitzTargets.lean`: divided-power multiplication, a derivative with
  explicit coefficient demand, and a concrete scalar polynomial-ODE producer.
- `ApplicationChecks.lean`: one kernel-reduced modular example, one checked
  finite basis count, and two exact rational executable diagnostics.
- `ObjectKernel.lean`: minimally adapted, pinned upstream object theory.
- `AxiomAudit.lean`: dependency audit of the main checked declarations.

The new general application target propositions are not proved.  The tower's
local algebraic contracts and the general object's arithmetic compiler are
not claimed to be completed Lean proofs.  No trusted module
introduces an axiom, an opaque placeholder, or a proof admitted by `sorry`.
