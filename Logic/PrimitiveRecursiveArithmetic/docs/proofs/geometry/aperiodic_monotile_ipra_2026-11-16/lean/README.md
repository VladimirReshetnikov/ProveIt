# Lean formalization outline

This directory is a **scaffold**, not a completed kernel-checked formalization.  It is
written for insertion into the `ProveIt` root Lake workspace and targets the checked
libraries

- `ConciseIPRA` (`LeanProofs.ConciseIPRA`), and
- `IPRADerivations` (`LeanProofs.IPRA`).

The intended build order is

1. `Encoding.lean`: finite codes for lattice points, affine maps, polygons, patches,
   torus quotients, and primitive-recursive Boolean predicates;
2. `HatData.lean`: the closed hat data and reflected computation theorems;
3. `Substitution.lean`: the 29-placement metatile construction, nested H-supertiles,
   and the radius-growth invariant;
4. `Periodicity.lean`: weak-to-strong periodicity, alignment on a finite torus,
   chevron/comet coupling, strip cycles, and the triangular-norm descent;
5. `IPRA.lean`: reification of all preceding Boolean computations and mathematical
   lemmas as derivations of type `[] ⊢[PRAAx] φ`, followed by transfer through
   `pra_iff_native`.

The `sorry` declarations identify the exact remaining proof obligations.  No theorem in
this directory is claimed to compile in the delivered archive; Lean was not installed in
the artifact-generation environment.  The report gives a dependency graph and a proof
for each obligation.
