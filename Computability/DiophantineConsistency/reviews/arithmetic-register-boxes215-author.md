# ArithmeticRegisterBoxes215 — author construction and replay

27 October 2026. Authored by controller_certificate. ROOT authorized exactly
one unchanged numeric-prefix refresh and two new leaves. This receipt is an
author self-review and bounded private replay; independent review is pending.
No prerequisite source, shared object, shared progress document or Git state
was changed by this work.

The final 706-line main and 63-line Checks prove actual215 register-box
execution in every ORing model of IΣ1. All nine physical selectors are covered
by `Fin 9`; every register value, left tape, scan length, spare count and
execution clock is internal to the model. The public theorems are `box_mark`,
`box_inc`, `box_dec0` and `box_decp`, all with positive clock conclusions.
They take no table agreement, box execution, structured run or old252
simulation premise.

`plain` encodes nine blocks `0,1^(value+1)` followed by an internal number k
of spare blocks holding one; `marked` changes the selected block to
`0,0,1^value`. Mark preserves the rest of the tape. INC uses the actual
198/0 bypass, increments the selected value and appends exactly one spare 1.
Zero DEC restores the file and exits 97; its k>0 premise supplies the following
block at the last primary. Positive DEC exits 40, keeps k unchanged and
retains the exact extra left bit `2*L+1`. The other three theorems do not need
k>0. `leftFrame` retains quotient/remainder head recentering even at L=0.
Positive clocks follow from actual different entry/exit arithmetic state
codes and runFrom_zero, rather than an assumed moved flag.

The implementation proves both directional scans from actual sparse_step,
then block traversal, carry, rollback and return. Internal spare iteration
uses fixed PR repeat3 graphs and exact clock 3*k. The uniform exact-clock
scan/spare predicates are explicitly Pi1 and use the accepted IΣ1 Pi1
induction principle. The finite primary list is only the nine-tuple spine;
it does not replace internal spare counts or unary scan lengths by Nat.
All 45 engine rows are kernel-checked: the 44 listed shared engine inputs plus
the literal215 198/0 bypass, with complete input-list coverage and length.
No native_decide, sorry, new axiom or cap increase is used.

The complete final main, Checks, unchanged 86-line Prefix254 and executed
116-line driver were read. The final main differs from attempt 9 by only the
ROOT-requested explicit omission of unused ORing/IΣ1 section variables from
values_split; the statement and proof body are unchanged. That one-line
delta was read before the final command. The driver snapshots all three
inputs before any compiler invocation, validates every header/reachable
import and first provider, then rehashes inputs after execution.

## Exact cache and commands

The unchanged frozen plan is research/c222-site215-plan-20261027/cache-plan.json,
SHA 2db2db74059105fba7f58dacc502274b3fdb4dd0605dafa8a37bdd5bc7b35e88.
It selects 147 prerequisite modules: 146 cached and one explicit fresh
ArithmeticTapePrefix254, with 95 Foundation modules all cached. There are 431
cached custom artifacts and 41 boundary primaries plus 123 companions,
595 first artifact providers. No Foundation or other dependency refresh ran.
The stale historical prefix object remains excluded; the historical source
and nine dependency mismatches remain documented in the original plan.
Package/stdlib paths exclude the shared project output cache.

The final private provider is:
`/tmp/register-boxes215-controller-author-1kdy5c1a/lib`.
Each command used the pinned Lean 4.32 binary with
`-M6000 -j1 -DElab.async=false -o <fresh-private-regular-object> <source>`.
LEAN_NUM_THREADS=1 and a 512MiB disk reserve were enforced. Exact commands,
inputs, compiler pin, LEAN_PATH, first providers, output hashes, full logs,
wall times and resource reports are in the immutable final packet.

| Final command | Wall seconds | Maximum RSS KiB | Result |
| --- | ---: | ---: | --- |
| unchanged ArithmeticTapePrefix254 | 3.891 | 1797564 | PASS |
| ArithmeticRegisterBoxes215 | 32.388 | 1992524 | PASS |
| ArithmeticRegisterBoxes215Checks | 3.082 | 1822668 | PASS |

Final Prefix/main logs are empty. Checks have 14 reports: twelve use exactly
propext/Classical.choice/Quot.sound, engine_rows_checked uses propext only,
and engine_rows_coverage is axiom-free. Checks include arbitrary internal
parameters, all selectors, zero DEC at r8/k1/L0, INC at k0, positive DEC of
one, the extra left bit and literal marked-slot/row binding.

## Frozen evidence and history

Final source SHA256:

- Main: d39cd409204646b238ede3d7a900b71697b15cdde8d7e423632a790ffa0cb782
- Checks: 109832fb3c3f9759083df942510610859ba7ab735d40504146ac785bd320ea43
- Unchanged Prefix: 396b573e4e94058859608ffa74be668f1d29a092f4853bdeafc0702da222cd55

Final object SHA256:

- Main: b791ab4b27b43e631116b70bffcb006ef9c906f1346e0b6ef5085d254d1e2654
- Checks: 366b9b32480511cd594770035f0ff4912b086815657ce6269c5a4462b0a8de82
- Prefix: 8ebbb2e0703d2ae7501b066f2df83de8e51265ee0d812000ebadd1667b928c5b

The final replay JSON is arithmetic-register-boxes215-final-replay.json,
SHA c0f925175e1d7ca8144e3c5b86cc7b1935f580d190b0ff6da7f60600fa4c4bbe.
Its 16-file manifest is arithmetic-register-boxes215-final-replay/FILES.json,
SHA 10df28e674e9d17f2a0a4c10dd7f648d3330b3647f39248a36b7810b34cc96de.
It pins the separate immutable 102-file pre-final packet/manifest and all ten
attempt records. Final freeze reauthentication made 7056 comparisons over
5407 paths, explicitly substituting only the ROOT-authorized current main
source for its historical attempt 9 source observation. Earlier snapshots
remain exact and distinguish historical sources from current ones.

Attempts 1–2, 4–5, 7–8 failed on local syntax, definability/elaboration, rewrite
or list-normalization details. Attempts 3 and 6 passed smaller construction
checkpoints. Attempt 9 passed the full statements with one benign unused
section-variable warning. Its freeze initially rejected an incorrect
empty-main-log expectation; that failed freeze script/assertion and the
warning log are preserved. A corrected pre-final freeze recorded the warning,
then ROOT requested the explicit omit and fresh final triple in attempt 10.
All ten triples' three input snapshots were retained even when a preceding
compiler failed and Checks was not invoked; there are 24 actual compiler
invocations total. No failed attempt is reported as a successful full packet.

## Remaining boundary

The proposed ordinary-Nat algebraic comparison of plain/marked with
KRuntimeCore.sepsR/sepsM has **not** been proved in this packet. The new
encoding is explicit and its arithmetic execution is proved directly;
that separate comparison is a remaining client. Actual symbolic segment
interpretation, Home, moved-flag executor soundness, all 4751 site bindings,
canonical-path/control transport and the full 215 control/tape equivalence
remain outside this packet. No source-ZFC, Pell, full PA-equivalence or
HA-proof-existence endpoint is claimed.
