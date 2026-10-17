# Internal return across an actual register block

[`ArithmeticRegisterReturnPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticRegisterReturnPerm252.lean)
returns left across one unmarked unary register block in the frozen252
arithmetic evaluator. It consumes the reversed block supplied by the
[forward macro](arithmetic_register_forward_perm252.md) and reconstructs that
whole block on the right. Both complete numeric tape halves and the register
value are arbitrary elements of every IΣ1 model.

With the checked recentered representation
`leftFrame q L R = frame q (L/2) (L%2 + 2*R)`, the generic endpoint is

```
runFrom (value+2) (leftFrame entry (reverseBlock value left) right)
  = leftFrame exitState left (registerBlock value right)
```

One entry row crosses the first unary one, the uniform left scan crosses
the remaining `value` ones, and a final zero row crosses the separator.
The generic theorem retains its three actual lookup equations. Six
unconditional wrappers instantiate the frozen state families:

| Family | Entry states | Ones loop | Exit |
| --- | --- | --- | --- |
| Decrement | 3 or 5 | 3 | 5 |
| Mark | 4 or 7 | 6 | 7 |
| Increment | 63 or 48 | 63 | 48 |

The low-bit recentering identity preserves both halves, including a zero
left half. The one-step helper separates read bit, written bit and target
state, retaining the final write and move for a halt target as well.
Twelve audit callers cover the concrete wrappers, different read/write bits,
a zero-valued register and arbitrary exterior data. The states are tied to
the actual literal lookup, with no second table or assumed box oracle.
These are endpoints; first exit, absolute head coordinates, the complete
register/spare invariant and the internal binary/scheduler comparison remain
separate.

The return contracts follow `RegisterMarkPerm252.return_end_left` and the
return rows in `RegisterBoxesPerm252` and `RegisterIncrementPerm252`,
attributed to mira-emmy PR20 head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`, `ZF/m253/coq/tm/Box.v`.
Mira-Cult, Jeff and Wade retain the machine, verification and framework
attributions.

The [first fresh check](results/arithmetic-register-return-perm252-verification.json)
passes eleven named axiom reports and twelve callers, standard Lean axioms
only, with zero warnings. Source and audit took 2.542 and 2.386 seconds on
pinned Lean 4.32.0. All 78 input identities, 29 project providers, five
external first providers, toolchain Omega and the fresh object are bound.
The [independent review](results/arithmetic-register-return-perm252-review.json)
also checks the twelve relevant literal transition rows.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_register_return_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --forward-evidence /outside/successful-register-forward/verification.json \
  --output /outside/new-empty-register-return-check
```

The checker is byte-identical to the original successful driver. It freshly
checks only this source and audit, using existing dependency objects without
rebuilding or downloading. `--cache` relocates all 29 selected prerequisite
objects while preserving their recorded hashes. The maintained-default
`--prepare-only` result is separately **PREPARED_NOT_BUILT** with no proof
commands. The [publication record](results/arithmetic-register-return-perm252-publication.json)
preserves that distinction; no additional proof replay was performed.
