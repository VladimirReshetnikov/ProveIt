# IΣ₁ proves the conditional PAeq derivation-transport sentence

For arbitrary fixed Δ₁ source arithmetic theory `T` and target PAeq theory
`U`, `axiomSupplierSentence` expresses that every internal `T` axiom
translates to a formula provable in `U`. `derivationTransportSentence` states
that this supplier implies that every internal `T` derivation has a
`U`-derivable translated sequent. Lean checks

```
𝗜𝚺₁ ⊢ derivationTransportSentence T U
```

via completeness and the all-model ten-rule transport. Thus this is a
derivability theorem of IΣ₁ for the displayed conditional sentence. It does
not discharge the uniform axiom-supplier premise, supply a fixed finite PRA
proof-code transformer, or establish a PA194 machine equivalence.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-transport-sentence/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorems' axiom audits contained no `sorryAx`.
An independent complete replay also passed without `sorryAx`.
