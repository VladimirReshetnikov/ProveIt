# Exact extraction of the two compact54 clause bands

`NativeCleanBands54.lean` proves an exact cyclic-stencil bridge using the
literal compact54 support and the sparse assignment already reconstructed
by `NativeSparseDigits54`. It covers arbitrary positive numbers of native
cells, including a single cell. It does not discard the temporal term or
claim phase alignment.

For any cyclic index `k` whose residue modulo4831 is2409, the contribution
of the complete folded native stencil is exactly

```
Σ (position,coefficient) in NativeStencil54.entries,
    coefficient * c(k − 2409 + position).
```

The same statement holds at residue3015 with2409 replaced by3015.
`convolution_left` and `convolution_right` prove these identities. All1045
raw stencil monomials are included before the irrelevant contributions
are proved zero; cyclic collisions are covered by the previously proved
folded-stencil identity.

The arithmetic separation uses only a coarse enclosure of the literal
support: every allowed position is at most583, or equals1203 or1807.
Two supported positions cannot differ by606 modulo4831. Consequently the
opposite clause band contributes zero. The four bare current-copy offsets
33,68,664,1268 and the spatial offset4877 also land outside the assignment
support at both clause targets. These are proved exclusions, not supplied
clean-band hypotheses. `subtraction_residue` handles cyclic subtraction
modulo a word of `N×4831` digits without assuming an unwrapped interval.

`source_clean_bands` composes this exact stencil calculation with the
positive literal old-z source and reconstructed digits. It yields both
clause-band tests in the precise form

```
(localContribution + temporalDigits) &&& maskDigit = 0.
```

The temporal contribution is retained explicitly. The theorem still lists
the arithmetic coefficient interface, exact `K` stencil binding, and high
mask word binding. These are the same transparent coefficient obligations
as `source_sparse_convolution`; no native-correctness or accepted-tableau
hypothesis is introduced.

The next steps are the literal periodic high-mask digits, temporal bit and
cell-position alignment, then the local decoder and global machine
interpretation. The full native refutation calibration and the internal
ZFC biconditional remain open.

The main module and eight public-API axiom checks pass with the repository
Lean4 toolchain. Every report uses only `propext`, `Classical.choice` and
`Quot.sound`. There are no new axioms or `sorry` terms.
