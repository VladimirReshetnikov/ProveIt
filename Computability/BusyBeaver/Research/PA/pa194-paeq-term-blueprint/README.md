# Current-Foundation arithmetic-to-PAeq term codes

This package ports the pinned upstream PA196 numeric term-translation
blueprint to the current LO Foundation interfaces. In every IΣ₁ arithmetic
model, including nonstandard models, `termCode` and `termVector` are total
functions with explicit parameter-free Σ₁ graphs. The construction preserves
bound and free variable codes and maps source arithmetic zero, one, addition,
and multiplication to the corresponding target function-tag expressions.
It proves the vector length, entry, nil, and cons equations on valid vectors,
and returns zero on invalid individual source term codes.

These are graph-defined numeric term functions, not yet fixed finite
candidate-PRA codes. The package does not prove target-language validity,
source/target substitution compatibility, witness or output bounds for the
translation graphs, formula-level translation, proof-code transport, or a
machine reduction. The listed upstream hashes identify the two adapted input
files; changing from FFL to LO is not a claim that the Foundation versions are
identical.

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-term-blueprint/check.sh
```

Both modules were rebuilt in order against the audited project and Foundation
objects, with no `sorryAx` in their printed dependencies. The standalone
script checks the upstream pins and repeats that build.

An independent complete standalone replay rebuilt both the blueprint and term
code modules from the pinned audited overlays and passed without `sorryAx`.
