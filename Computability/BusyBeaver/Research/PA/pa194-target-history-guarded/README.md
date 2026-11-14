# Length-guarded target history

`PA194TargetGuardedHistory.lean` adds a caller-supplied length to the extended
target-history interpreter. In every candidate-PRA model whose arithmetic
reduct satisfies IΣ₁, `next_model` proves that stage `n` executes a line only
when `n < len`. `past_end_rejects` proves that every stage at or beyond `len`
returns zero, including for nonstandard model inputs. The conditional
`history_sound` and `accepted_sound` theorems repeat the internal IΣ₁ induction
for this guarded history, with the same explicit Σ₁ predicate and rule-closure
premises as `../pa194-target-history-extended`.

The length is an **input supplied by the caller**. No theorem in this package
proves that it equals the actual length of a particular encoded vector or
constructs a well-formed vector of that length. The separate
[`pa194-target-history-length`](../pa194-target-history-length) constructs a
finite PRA code for Foundation vector length and supplies that value to the
guarded step in every covered model. It therefore does not by
itself close the vector-representation, source-proof compiler, or
machine/calculus calibration gaps, and does not establish a PA194/Con(PA)
implication. Its line encoding remains independent of the upstream certificate
format.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-target-history-guarded/check.sh
```

The final module was rebuilt against the freshly rebuilt extended-history
suffix and previously checked deeper prerequisites. A full nested replay of
this wrapper has not yet been completed. Its printed axiom dependencies
contain no `sorryAx`.

An independent suffix replay recompiled the guarded history module against the
separately checked extended-history and target-step objects, reusing other
prerequisite overlays. Its reported theorem axioms did not include `sorryAx`.
