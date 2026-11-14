# PA194 source search over Foundation formula sets

`PA194SetSearch.lean` constructs a fixed finite candidate-PRA code for the
universal-rule preimage search directly on Foundation's bit-coded sets. It
chooses a bit-membership characteristic code once, using the existing proof
that candidate PRA certifies its Boolean and membership properties. The source
shift code is fixed separately and is correct on internally valid formulas.

In every candidate-PRA model whose arithmetic reduct satisfies IΣ₁,
`find_setShift` assumes exactly that `a` satisfies Foundation's
`IsFormulaSet L a` and that `target ∈ setShift L a`. It proves that
`setSearch(a,a,target)` is a member of `a` whose Foundation shift is `target`.
Both the sequent code and all its members may be nonstandard. The proof uses the
internal bounded-search invariant and the internal fact that a set member is
less than its set code. The resulting search may choose a different preimage
than the existing standard Lean list compiler; no transfer from that list is
asserted.

This theorem supplies one source universal-rule search component. It does not
traverse a coded Foundation derivation, prove a complete compiler or prove its
correctness, establish source-calculus/PA calibration, or establish either
machine halting reduction.

The final module passed a fresh Lean 4.32 suffix rebuild against the freshly
rebuilt source-shift chain and audited project and Foundation objects. Its
printed main theorem axioms are `[propext, Classical.choice, Quot.sound]`;
there is no `sorryAx`. A separate independent invocation of the final module
also passed against the independently rebuilt source-shift object. The full
nested replay script below is prepared but has
not yet completed for this package. The source-formula shift prerequisite's
separate full standalone replay has completed successfully.

From the repository root, with matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-source-set-search/check.sh
```

Temporary objects use `/dev/shm` by default; set `TMPDIR` to another suitable
temporary directory if required. The script rebuilds the source-shift chain
and checks the final module's reported axioms.
