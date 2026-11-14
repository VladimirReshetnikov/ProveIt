# Quote standard target proofs of translated source axioms

For any Δ₁ PAeq target theory `U`, standard arithmetic sentence `σ`, and
standard PAeq sentence `τ`, `translated_quote_proof` converts an actual
Foundation proof object `d : U ⊢! τ` into the internal proof whose code is
`⌜d⌝`, proving the actual numeric translation `formulaCode 0 ⌜σ⌝` in every
IΣ₁ arithmetic model. The theorem requires the explicit syntactic equality
between the PAeq translation of `σ` and `τ`.

This makes standard target proof constructions reusable for the finite
PeanoMinus supplier cases. It does not itself construct any new arithmetic or
order proof, handle nonstandard induction-schema instances, or establish a
connection to the literal PA194 machine.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-paeq-quote-proof/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorem's axiom audit contained no `sorryAx`.
An independent complete replay also passed without `sorryAx`.
