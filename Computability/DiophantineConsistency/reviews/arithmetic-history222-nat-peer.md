# Independent actual C222 history-to-Nat binding review

Reviewer `/root/complemented47_review`, 26 October 2026. PASS within the stated
scope; no correction requested. This was a read-only source, mathematical,
and provenance review. I did not compile the files or modify frozen sources,
objects, documentation, or Git state.

I read all 108 main lines and 52 focused-check lines, the complete actual
`Code222Proof` definitions and theorem interfaces, the unchanged raw parser's
`decodeStep`/`decodeFuel`, the actual row's parser agreement and oracle
congruence, the new history's recurrence/lookup contracts, and the exact old
arithmetic division/remainder helpers. I also read the complete author
receipt and all three preparation/compile/receipt scripts. I independently
reviewed the row, generic history and actual internal history earlier; I did
not author them. This review covers the Nat adapter rather than repeating a
claim of fresh validation for their whole transitive closure.

Source prefix: `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.

| Source | SHA-256 |
|---|---|
| `ArithmeticHistory222Nat.lean` | `871f3ef287a10bdbc3da19fd1d513d481ce7c6d36446f6d0c0d4cc7ab57b79ef` |
| `ArithmeticHistory222NatChecks.lean` | `c52ce33b7078ae821fdae72ec265dbfc50f81ca8a71d3d96b9f79efe599af404` |
| Old arithmetic-helper module `ArithmeticHistory254.lean` | `4cf3d35c0c8d156bfb14ceacf87a799e9d4a35108a17c70bb63c4f93278a9e2e` |

The old module is used only through `foundation_div_nat`,
`foundation_rem_nat`, and its numeral12 identity. `positiveStep_nat` keeps the
actual sequence-lookup oracle and uses the new `ArithmeticRow222.rowKernel_nat`.
It does not identify the new evaluator with the old C254 evaluator.
`value_succ_nat` then replaces those lookups by this same new history's values,
using the actual child bound `i≤raw/12≤raw`. The conversion from native Nat
order to the Foundation order is explicit via `Arithmetic.le_def`; no order
instance mismatch is hidden in the final proof.

The central theorem is strong induction on `code`, with `fuel` universally
generalized in the induction hypothesis. For code `raw+1` and fuel `fuel+1`,
the premise gives `raw+1<fuel+1`. Each child index is at most `raw/12≤raw`,
so it is both strictly smaller than the current code and strictly smaller
than the remaining fuel. Those are precisely the two premises required by
the induction hypothesis. The proof unfolds one actual parser step, invokes
new `row_parsedValue`, and uses `row_congr` only at its queried child indices.
It assumes neither valid trees nor a fuel-monotonicity theorem. Fuel zero is
excluded by the explicit premise; code zero remains invalid at every positive
fuel. No second Nat history or numeric fuel evaluator is introduced.

Specialization to `fuel=code+1` is exactly the fuel in `check222`. All Nat
inputs are covered, including malformed codes and invalid bundle/MP trees.
The acceptance proof splits `none` versus `some p`, then both new
`valid222 p` values; a rejected result is zero and cannot equal the successor
of the requested conclusion. Successful outputs compare the actual new
`conclusion222`, not the old raw tree's C254 conclusion. The same fixed
`valueDef`, `checkDef`, and `checkValue` from the arbitrary-IΣ1-model packet
receive the all-code Nat interpretation.

The final `c222_iff_represented` composes this all-code result with the proved
actual finite C222 checker theorem. Its conclusion is an external equivalence
between `KCode222.C222 n` and a natural witness to the fixed represented
formula. It is not an assertion of internal seed validity, a coded internal
C222/C254 proof translation, interpreter execution, or HA equivalence. The
focused checks retain invalid code0, truth at code1/conclusion0, actual growG,
actual helper-free bundle, and the legal repeated-label/zero-binder case
`a=b=1,c=0`.

I independently rehashed all 120 selected custom sources (95 Foundation),
405 object/companion files, 38 external boundary objects, six parent receipts,
compiler, package manifest, input inventory, three drivers, final leaf
sources/snapshots/objects/logs/timings, and both development-run records with
all executed snapshots/logs/timings. All 597 hash checks matched. Each
recorded source import list agrees with the actual text, and direct imports
are closed over the selected set plus explicit external boundary. The
unexecuted checks planned after the failed first main are not counted as an
execution.

The first source failed only because a native Nat order proof was passed to
the Foundation order interface. Its preserved log agrees with the reported
repair; the final main and checks both exited zero. I read the empty final
main log and all eight reports, each containing only `propext`,
`Classical.choice`, and `Quot.sound`. Their private objects are:

- Main: `fde4589e7e69f022d5e605c1b43f343fc42997fad1385f201841c495f00c6468`.
- Checks: `03a680ffda6cfd1c5aed3407d5d3b7273c05fc70a5117df0fff86c6fe42ef55f`.

Reviewed author receipt:
`db0da51045cb8126ff05d3a1443ca8a91ec7a535d3a7e7e0e6fe7dadcccbdc34`.
Replay receipt:
`05d3b53c279829df06a65f2c97d1d6a9ba5cbd7fcb32a1461d67d49495cbbcd8`.
Input inventory:
`31d79c8179642d52267fe31acca156f07e9a233d464e320ac985a10dd20eb5e8`.

This review authenticates the author's bounded executions and checks their
source mathematics. It is not an independent fresh compiler replay, a broad
Foundation build, or a new transitive package-internals audit.
