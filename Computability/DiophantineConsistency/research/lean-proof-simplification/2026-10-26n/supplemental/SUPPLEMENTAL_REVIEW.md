# Two additional, novelty-screened proof ideas

Pinned source: `b310142330df89e48413c8fce62e7de223e1c7d5`.

**Status:** candidates are uncompiled. This environment has no Lean/Lake and no toolchain was installed. The incoming audit screened these exact ideas against six incoming report manuscripts and technical notes, and found no duplication. Absence from those reports is not a claim of global mathematical originality.

## S1. Close the explicit CRT congruence instead of running `exact?`

Target: `BoundedForallCertificate.lean:87–91`. This is the sole `exact?` occurrence among all 574 active Lean source files at the pin. The existing branch unfolds the modulus, invokes `gcongr`, then leaves `exact?` to locate the CRT residue already in the local context.

The imported pinned `MRDPCore.lean:110` defines `crtModulus scale index := (index + 1) * scale + 1`. Therefore transport `hIndex_residue k hk` through add-one, multiply-by-T, add-one, and compose with self-divisibility:

```lean
    · exact ((((hIndex_residue k hk).add_right 1).mul_right T).add_right 1).trans
        dvd_rfl.modEq_zero_nat
```

This replaces four tactic lines with two. The gain is a deterministic proof term and visible dependence on the right residue hypothesis, not a measured runtime improvement. Natural truncated subtraction in the preceding falling-factorial branch is untouched. No certificate shape, quantifier, witness, or arithmetic identity is changed.

Artifacts: `crt-explicit-congruence.patch` and complete `BoundedForallCertificateCandidate.lean`. The supporting imported source is in `evidence/`, with its independently verified pinned Git blob and SHA-256.

## S2. Factor the binary graph-composition depth proof

Targets: `BoundedForallDepth.lean:81–120`, five theorems `pow_depth_le`, `binomial_depth_le`, `sub_depth_le`, `mod_depth_le`, and `div_depth_le`.

Each proof repeats the same specialization of `GraphRep.compose_depth_le` to arity two, a two-case dependent-vector elimination, and arithmetic rearrangement to `h + 8`. A helper accepting the two component bounds once lets each wrapper consist of `unfold` followed by one `exact`.

`DepthCandidates.lean` supplies the generic helper and pow/binomial pilots. This preserves the precise +8 bounds and leaves every graph constructor untouched. It is a maintenance refactor with modest savings: five bodies shrink from four lines to two, but the helper's declaration consumes much of that saving. Do not present it as a large whole-file line reduction or runtime optimization. It becomes more attractive if further binary graph operations are added.

## Replay plan

Use a complete checkout of the pinned repository with its existing `leanprover/lean4:v4.32.0` toolchain and Mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997`. Do not treat this selected-source snapshot as a standalone Lake workspace: external local Lean libraries are not all included.

1. Check the CRT patch with `git apply --check` in the pinned checkout, then apply in a throwaway worktree.
2. Run `lake env lean Computability/DiophantineConsistency/Lean/DiophantineConsistency/BoundedForallCertificate.lean`.
3. Compile `DepthCandidates.lean` through `lake env lean`, with the candidate file copied into that worktree or passed by absolute path.
4. Inspect the supplied `#print axioms` output and compare it with the corresponding original declarations.
5. Replay downstream BoundedForall Checks modules before accepting any source replacement. No elaboration, axiom, or wall-time result has yet been obtained here.
