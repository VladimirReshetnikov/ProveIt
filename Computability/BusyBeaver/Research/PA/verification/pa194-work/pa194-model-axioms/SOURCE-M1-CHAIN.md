# Incremental multiplication-totality source chain

The check completed successfully on 2026-11-15, rebuilding the 14
multiplication helper modules and the three final
`m1` modules in dependency order into a fresh output. They cover graph and
addition-witness construction, prefix successor and ordinal induction, output
extraction, the exact Separation sentence, and the full-source fact. The source
retains the repository-built recurrence and prefix-extension objects, the older
addition-output and induction overlays, and Foundation objects listed in the
checker. It does not rebuild the complete transitive closure. A separate standalone source
check of the corresponding addition-output development passed without
establishing byte identity with those older objects. The result is model-uniform
under the
stated candidate PRA and classical IΣ₁ assumptions, not an iPRA derivation.

From the repository root with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-source-m1-chain.sh "$PWD" NEW_EMPTY_OUTPUT
```

The checker verifies each declared axiom-report count and rejects `sorryAx`.
