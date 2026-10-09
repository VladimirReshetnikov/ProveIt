# Formalization plan (not a delivered Lean proof)

## Stage 1: finite geometric semantics

Define a coordinate cross in `(Fin s -> F_q)`, its finite Cartesian powers, the full-support stratum, and a partition into nonempty affine subspaces over the whole field. Keep `q > 2` explicit. Prove orthant containment by the two-zero-set argument, then torus capacity by selecting a basis from the coordinate restrictions.

The first target should be the exact point–torus identity and its equality criterion. This fixes the semantics of the optimization problem before introducing a numerical minimum or the regularized limit.

## Stage 2: support-word combinatorics

Use an option type for an arm label, not a field zero that could be confused with a valid cyclic arm residue. Prove the adjacent-layer degrees and derive the chain decomposition from finite left-saturating matchings. Define the chain head and the nested order of zero coordinates explicitly.

Represent a prefix line by its anchor and direction. Prove that nonzero parameters give full support and that the distinguished coordinate ratios separate different chain depths. This is a finite-algebra theorem independent of any optimization oracle.

## Stage 3: common-invariant fibers

For a coloring `[m] -> [z]` and a rainbow zero set, define all products in the unit group of the field. Derive the missing-coordinate line coefficients from the outside products. Prove a bijection between the fiber and pairs `(outside values, nonzero line parameter)`.

The main semantic requirement is that two different zero sets assigned to the same coloring use the *same* invariant fibers. A local parameterization theorem alone is insufficient for the global partition claim.

## Stage 4: residue routing

Use `ZMod s` only for the arm alphabet, separately from F_q. Prove that fixing a sum leaves exactly `s^(z-1)` extensions. Prove the slot-graph degrees, including the multiplicative factor `(q-1)^(z-1)` from invariant values.

Assemble all groups with pairwise disjoint residue sets and the tail chains. Prove separately: affine-cell membership, unique boundary anchor, torus disjointness, boundary disjointness, and complete coverage. These yield the exact finite theorem.

## Stage 5: the universal asymptotic construction

Formalize the elementary perfect-hash existence bound by the finite union bound, using an integer upper bound on the logarithm. Prove the rounding-budget inequality. Define the factorial cutoff and estimate its overhead using elementary logarithmic factorial bounds.

Keep the uniform-in-q threshold theorem separate from the fixed-q Taylor expansion. This prevents an accidental strengthening when analytic constants are introduced.

## Stage 6: regularization and the two-term rate

Prove the limit from submultiplicativity by the finite-block decomposition, then the Jensen lower bound and the finite exact-block upper bound. Derive the root expansion with uniform remainders on a fixed neighborhood of c_q. Prove positivity and the inverse-linear lower scale of the centered error before taking its logarithm.

Suggested final theorem names (proposals only):

```text
crossPartition_pointTorusDefect
crossPartition_eq_iff_boundaryLinePacking
rainbowFiber_affineLinePartition
crossPartition_colorCodedBudget
crossPartition_exactSaturation_hereditary
crossPartition_saturationThreshold_uniform
crossPartition_regularizedRate_twoTerm
crossPartition_centeredError_logExponent
```

No files bearing these names are supplied as compiled formal proofs. The proposed names and stages are integration guidance, not verification evidence.
