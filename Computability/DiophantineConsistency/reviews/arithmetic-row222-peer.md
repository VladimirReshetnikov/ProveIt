# Independent C222 row source and provenance review

Reviewer: `/root/complemented47_review`, 26 October 2026. Result: PASS within
the stated bounded-row scope; no correction requested. This was a read-only
mathematical/source/provenance review, with no independent compiler invocation.
The author is `/root/controller_certificate`.

I read all 181 lines of `ArithmeticRow222.lean`, all 50 focused-check lines,
the complete 290-line `ArithmeticRow254`, the complete 210-line
`Code254History`, the actual `Code222Proof` conclusions/recursive validity,
the unchanged `RawProof` and `decodeStep` definitions, the actual `KCode222`
code constructors, and both new bounded template modules. I also read the
complete author receipt and all three preparation/compile/receipt drivers.
I previously independently reviewed the growG, seed-template and Nat-checker
packets; I did not author those implementations. I did not reread every
Foundation prerequisite or claim a fresh dependency-closure replay.

Source prefix: `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.

| Source | SHA-256 |
|---|---|
| `ArithmeticRow222.lean` | `7341c95d5b3d9a9d17eb2f6bfb32c7b1bf781fe86274c0eeba817c953be6c8f1` |
| `ArithmeticRow222Checks.lean` | `ad3e51c42e88ec378f4b20aefbd0b62c7075e4466af9b561ec34d35ea2deb24e` |
| `ArithmeticRow254.lean` | `90c29554d76400618777a6139be5089220093a5effb2b0587f0d3ab497d0ca7c` |
| `Code222Proof.lean` | `7e91fc3c3fca914db3b9063003e273dfa49f773c20366f61b23afe79ac48d1f5` |
| `KCode222.lean` | `fbc4fef6e479b6bc5bc83bcfafa73fb1befdc1b1d02b605da68ecf691f641eb3` |
| `ArithmeticSeedTemplates222.lean` | `d0f878669c9f8c8c9d94bccf451544aba6f7304368355f0bba440999ce342a59` |
| `ArithmeticTemplates222.lean` | `e346d466e4778df946d385dc4b45855326957894019e627925c42fea803be962` |

The actual nested Cantor payload is `(a,(b,c))`. Tag 9 returns the exact
`growG a b c + 1`; tag 11 returns the helper-free `bundle222 a b c + 1`
exactly when `c≠a ∧ c≠b`. There is no extra `a≠b` or `c≠0` gate.
The checks retain the legal case `a=b=1,c=0` and reject each forbidden
collision. Every other tag uses the old **numeric** row on unchanged inputs.
This retains the ordinary code-zero/valid-conclusion-zero distinction:
invalid data has result zero, while a valid conclusion has result successor.
The seed's actual false formula code remains 1.

The Sigma0 graph bounds all payload projections by the payload. Its output
witness is bounded by `r` only on a successful successor-output branch.
The rejected seed branch has `r=0` without requiring the large rejected seed
to be at most zero. The untouched MP gate separately bounds predecessors by
the two child results, including rejection. `row_defined` proves the graph
for arbitrary inputs in every stated IOpen model; it does not assume valid
children or a correct history. The reuse of `payload_fields_flat` is justified
by the actual two Cantor pair equations, including payload zero.

The natural-number adapter supplies `u=rec(tail)` for GEN/tag2, and
`u=rec(b)` otherwise; `v=rec(c)` is the major MP result. The `rowEnv` binding
uses exactly the same slots. For MP, both zero-child cases reject, and two
positive child values are accepted only when `v−1=wim(u−1,a)`. The new
`row_parsedValue` splits missing children and all four Boolean child-validity
cases against **new** `valid222` and **new** `conclusion222`; it does not reuse
C254 semantic soundness or C254's old parser-agreement conclusion. GEN,
truth/payload-zero, all ordinary leaves, both changed leaves and every
out-of-range tag are covered. `row_invalid` proves zero for all Nat tags
at least 12. `row_congr` retains the exact child-index-at-most-payload bound,
while the two changed leaves do not inspect the oracle at all.

I independently rehashed all 107 selected custom sources (86 Foundation),
all 365 listed objects/companions, all 37 explicit external object boundaries,
the three parent receipts, compiler, package manifest, and the three drivers.
I also checked the declared import lists against the actual source text and
verified that every direct custom import is in the selected set or explicit
external boundary. Every pin matched. All final leaf source/snapshot/object,
log and timing hashes matched; both development snapshots/logs/timings and
run JSON hashes also matched. Historical first-run object digests are retained
as history, not confused with the final overwritten private leaf object.

The author's two final capped commands exited zero. I read the empty final
main log and all ten focused axiom reports, each restricted to `propext`,
`Classical.choice` and/or `Quot.sound`. The initial already-successful pair
had one unused-simp-argument warning; the preserved final delta removes only
that redundant `h9` proof argument. The receipt accurately records a two-leaf
refresh over authenticated cached prerequisites, not a fresh Foundation
rebuild. This review authenticates those records and checks the mathematics;
it does not relabel the author's executions as my own.

Final author object pins:

- Main: `8eed6e75b5bdd4cb8641b33aa9e4509d9f99bf7a842d7c2ca25ab3b2a07b2aae`.
- Checks: `2b8430b1f35fe963e4eeb72536613bad495e62f0f1ac09bed35475d279401e11`.

Reviewed records:

- `arithmetic-row222-author.md`:
  `ddb88e1f5dd3112e4d20df692db5471c6877df21fa2df06dbb7009762c6cb036`.
- `arithmetic-row222-replay.json`:
  `5973c5695f0d1eee610a75e6eacf69b23744a585f22f14876b2855a9250de96d`.
- Pre-execution inventory:
  `113733085e6ecb2ed4d1b425264f364cdf08d02256544326945dc9e3a1d85f30`.

The remaining boundary is substantive: this packet supplies a bounded
arithmetic row and standard-Nat one-step parser agreement. It does not yet
represent the whole C222 history, prove internal seed validity, translate the
actual enumerator runtime, or establish an HA equation/consistency equivalence.
The explicit oracle is an input interface, not a represented lookup theorem.
No source, object, existing document or Git state was changed by this review.
