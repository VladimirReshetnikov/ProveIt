# Internal increment suffix shift over zero spares

[`ArithmeticZeroSpareShiftPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticZeroSpareShiftPerm252.lean)
handles increment's suffix shift through an arbitrary internal number of zero
spare registers in the frozen252 arithmetic evaluator. With the checked
zero-block, reversed-block and unary-prefix functions, its exact endpoint is

```
runFrom (value+2*count+2)
  (frame 94 left (bitPrefix true value (zeroBlocks count 0)))
 = leftFrame 63
     (reverseZeroBlocks count (bitPrefix true (value+1) left)) 0
```

The unary value, spare count and entire left half are arbitrary values of
every IΣ1 model; the right half has the specified blank exterior. The literal
states 94/108 swap a separator 01 to 10 in two steps. At the final blank
pair they write the added one and turn left into state 63, retaining the final
write and move. A Π1 induction predicate quantifies both the changing unary
value and the whole left half; the checked reverse-block push law closes the
successor case. Count zero and unary value zero are included. An audit caller
uses 56+count for the zero suffix of the known boot spare family.

This is a changing-tape endpoint rather than a first-exit assertion. A full
increment macro, absolute head/register-file framing, spare-growth invariant,
dispatch preservation and the complete internal binary/scheduler comparison
remain separate. It introduces no new consistency endpoint. The contracts
follow the attributed `shift_separator_steps`/`shift_suffix` framework in
`RegisterIncrementPerm252` and mira-emmy PR20 `Box.v`; Mira-Cult, Jeff and Wade
retain the machine, verification and framework attributions.

The [fresh check](results/arithmetic-zero-spare-shift-perm252-verification.json)
passes three named axiom reports and six callers, standard Lean axioms only,
with zero warnings. Source and audit took 5.645 and 1.988 seconds on pinned
Lean 4.32.0. Thirty-two project providers, five external first providers,
toolchain Omega, all 85 original input identities and the fresh object were
checked. Dependencies were reused without rebuilding or downloading.
The [independent review](results/arithmetic-zero-spare-shift-perm252-review.json)
binds the final bytes and retained failed first attempt; its fixes only
normalized numeral casts and restricted a time rewrite.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_zero_spare_shift_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built-dependency-checkout \
  --scan-evidence /outside/successful-zero-spare-scan/verification.json \
  --return-evidence /outside/successful-register-return/verification.json \
  --output /outside/new-empty-zero-spare-shift-check
```

The portable checker freshly checks only this source and its exact audit.
`--cache` relocates all 32 prerequisite objects, retaining their required
hashes. The maintained-default preparation is **PREPARED_NOT_BUILT** with
no proof commands, separate from the successful original kernel record.
Only the portable default sourcehash was updated to the final checked bytes;
the executed original checker and its explicit source override are preserved.
The [publication record](results/arithmetic-zero-spare-shift-perm252-publication.json)
keeps these identities and statuses distinct.
