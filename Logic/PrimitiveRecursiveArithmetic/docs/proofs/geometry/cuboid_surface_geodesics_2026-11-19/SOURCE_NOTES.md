# Source and derivation notes

## Published diameter theorem

The complete three-regime intrinsic-diameter formula is due to
Y. G. Nikonorov and Y. V. Nikonorova, *The Intrinsic Diameter of the Surface
of a Parallelepiped*, Discrete & Computational Geometry 40 (2008), 504-527,
DOI 10.1007/s00454-007-9037-7.

The accompanying report restates the theorem in a coordinate form convenient
for computation, derives the five unfolding functions explicitly, and gives a
self-contained optimization argument organized around those functions.

## Fixed-vertex theorem

The explicit two-regime fixed-vertex theorem, including the candidate

```text
(A-delta, B-delta, C)
```

and the factorization

```text
R^2-L0^2 = A*(C-B)*K/(2*C^2),
```

is derived in the report by a four-source planar Voronoi analysis of the face
opposite the longest edge.

## ProveIt reuse

The Lean roadmap follows the current ProveIt organization for finite
coordinate geometry and for the distinction between:

- proofs of identities in host Lean/Mathlib; and
- actual derivations in the internal `Prf PRAAx` object theory.

The relevant inspected material is under
`Logic/PrimitiveRecursiveArithmetic/docs/proofs/geometry/triangle_formulas_ipra`
and the core `ConciseIPRA` Lean namespace. No ProveIt source file has been
copied verbatim into this package.

## Verification scope

`verify_formulas.py` checks all key polynomial identities symbolically and
performs independent numerical grid maximizations in randomly sampled boxes.
`audit_unfoldings.py` separately enumerates all simple face chains in the
six-face adjacency graph. For the fixed-vertex problem it certifies that 24
noncanonical planar source images are dominated by the four retained images;
for the diameter problem it certifies that nine noncanonical squared net
lengths are dominated by the five retained lengths.

These scripts do not formalize the general straightening lemma, the central
symmetry theorem, compactness, or the optimization proof. Those arguments are
in the PDF, while the Lean blueprint identifies the corresponding formal
obligations.
