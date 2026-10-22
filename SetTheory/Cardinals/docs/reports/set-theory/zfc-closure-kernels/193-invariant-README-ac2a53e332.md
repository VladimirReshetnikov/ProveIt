# Write each source prefix once

Status: **uncompiled source-only proposal**, separate from the checked residual
routing work. This changes the maintained whole-site checker statements, not
its evaluator, certificate partition, or proof bodies.

Add the following transparent abbreviation immediately after `SiteCoverage.descend`:

```lean
abbrev checkedSubtree (test : List Bool → Edge → Bool) (t : Tree)
    (prefix : List Bool) : Prop :=
  allSites test prefix.reverse (descend t prefix) = true
```

Every one of the 105 current generated block theorem statements prints the same
prefix twice: once forward and once reversed. Replacing those two literal lists
by `checkedSubtree test tree prefix` preserves the statement up to definitional
reduction of the abbreviation and finite list reversal. The existing proof body
`exact KFastSites215.allSites_of_fast (by decide +kernel)` is unchanged. The root
join proof is unchanged as well.

The generated patch shrinks the nine batch files from **55,794 to 36,991 bytes**:
**18,803 bytes** removed from their statements. The generic abbreviation and its
comment add **238 bytes**, for a net saving of **18,565 source bytes** over the ten
selected files. These are UTF-8 source-byte measurements, not proof-object sizes,
endpoint-wide measurements, or measured compile-time savings.

## Reproduce the proposal

```sh
python3 rewrite.py --repo /path/to/ProveIt --out /path/to/fresh-output
```

The script validates the ten Lean inputs and the separate generator against the exact hashes in
`source-pins.json`, verifies that every printed reverse prefix really is the
reverse of its forward prefix, requires exactly 105 replacements, and writes a
patch, transformed source copies, and a complete measurement receipt outside the
checkout. It does not apply changes or invoke Lean. The supplied patch was
checked with `git apply --check` against the pinned checkout.

The separate `generator-wiring.patch` applies the corresponding generator change in
`Research/ZFC/k225-formal/generate_sites215_lean.py`:

```python
def stmt(P):
    return f"checkedSubtree {TEST} {T} {bl(P)}"
```

The generator is separately source-pinned and excluded from the ten-Lean-file
byte measurement. Its proposed Python syntax was parsed; the generator was not
executed and the Lean changes remain uncompiled. `rewrite.py` reproduces both
patches.

Before adoption, apply both patches and freshly compile `SiteCoverage`, the nine batches, their root composition, and the
canonical endpoint with the project axiom audit. This packet does not claim that
those changed modules have been compiled. Regeneration must preserve the new
format; editing generated outputs alone would be temporary.
