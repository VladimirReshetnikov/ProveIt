# Extracting a term value from a name

`PA194NameValueSchema.nameToValue` proves in every Δ₁ source theory the internal provability of `¬tr(exName s) ∨ ∃v valBody(s)[v]`, for every internally valid arity-zero PAeq term `s`, including nonstandard codes. It assumes no value existence, naming fields or source axioms. The proof instantiates a fixed first-order formula valid in every structure using the Schematic source-proof constructor; its four predicate parameters are the actual domain, variable-value, arbitrary term-value, and order-isomorphism codes.

The four modules separately establish the fixed logical schema's validity, its typed predicate-slot assignment, exact equality with the translated name/value code, and the internal provability result. The exact slot ordering matters: the two binary templates use bound indices `(0,1)` so that their substitutions produce the target indices `(1,2)` and `(1,0)` respectively.

From the repository root with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-name-to-value.sh "$PWD" /dev/shm/pa194-name-to-value-repo
```

The checker recompiles all four source modules, requires one clean axiom report per module, and rejects `sorryAx`. It retains the repository-built `/dev/shm/pa194-name-forms-repo` (which includes the revised `instS` interface) and the other object overlays listed in the script, including prebuilt Foundation. This is a Lean theorem uniform over IΣ₁ arithmetic models; it does not prove value existence, `eSucc`, the native iPRA implication or physical-machine synchronization.
