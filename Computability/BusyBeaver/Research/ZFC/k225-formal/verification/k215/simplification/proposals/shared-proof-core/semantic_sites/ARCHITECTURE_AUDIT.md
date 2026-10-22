# Architecture audit at 2ca3a5c16f

## Exact theorem boundary

`k225-formal/verification/k215/README.md` says the two checked proof-assistant
endpoints are external theorems

```
Halt(K215, blank) ↔ ZFC has a finite derivation of falsity.
```

Their negations give external nonhalting/consistency equivalence, with no
consistency premise. The page explicitly states that no internal PA proof or
derivation encoded in ZFC's own proof syntax is supplied. Refactoring the
external proofs does not by itself fill that internalization gap. The article
should distinguish the user's eventual in-ZFC goal from the currently checked
external endpoint.

The machine boundary is the literal dense 215-working-state, two-symbol,
two-way infinite tape table. Initialization is included. The dense-table hash
recorded there is
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
The exact source hash is
`17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`.

## Composition already in place

`BusyBeaver/ZFC/KEndpoint215.lean` supplies the five candidate-specific inputs
to the generic endpoint: dense/sparse correspondence, register-engine
contracts, blank bootstrap, site coverage, and source/calculus equivalence.
`KEndpoint.lean` already composes those once for all K-family machines.
The final endpoint is therefore not the substantial duplication target.

The Lean calculus calibration runs through a semantic model construction;
Rocq uses the inherited syntactic development. Replacing one with the other
would be a new verification program, not an automatic benefit of sharing a
machine certificate.

Current Lean `DominatedImplication.lean` is the new 58-step abstract derivation
with `rho8_all`, `composition`, and `lift_right`. The numerical adapter is
unchanged. The root commit reports focused compilation of the core, adapter,
and KCodeDom. The Rocq production file retains the checked earlier certificate
replay. The rho8cd README/status update is explicit about that lane boundary.

The phase-nine endpoint checkpoint predates the last core replacement. It
reports a 192-module endpoint closure plus five decoder-prefix-only modules,
with 20 fresh modules, 13 matched isolated providers and 164 phase-eight
providers. Those are incremental evidence counts, not a fresh 197-module
rebuild. The original full checks were 204 Lean modules and 237 Rocq sources.
The report must not silently combine the newest focused check and historical
full build into a fresh full-build claim.

## Completed simplifications not to propose as new

The maintained source correspondence already uses 1,426 normalized certificate
entries instead of the earlier 2,240, balanced lookup, a stable program/data
split, and sixteen independent kernel checks. The seed directions already
share bundle semantics. The implication core is representation independent.
The runtime already has a shared positive Home return theorem and checked
table gate. A new report should acknowledge those as its baseline.

Phase nine still checks all 4,751 leaf occurrences and 6,176 branch outcomes.
Its site batches total 984.608 seconds, compared with historical phase-six
1,649.340 seconds; the source explicitly disclaims a controlled paired timing
experiment. The five prefix-only modules prove exact decoder entry and stop
before the primitive. The claimed 135 role/outcome contracts are not yet
proved there. The 86-occurrence CB1 design is source-only research.

## Prioritized next work

1. Synchronize a compact abstract implication proof across the language lanes,
   preserving the three public Lean interfaces and Rocq's current theorem
   interface. A new Rocq proof must receive its own compiler/assumption receipts;
   the status of the imported proposal is not an integration receipt.

2. Insert the semantic site contract boundary implemented in this packet. This
   separates mathematical reachability from acceptance by one bounded executor,
   while keeping the executable definitions and existing clients exact. This
   necessary interface now compiles, but does not itself remove branch checks.

3. Prove one shared primitive suffix and compose it with the existing full-word
   decoder prefix. Start with the guarded CB1 family. Once its entire family
   coverage is checked, use the semantic interface to avoid re-running those
   occurrences. Then extend to register and continuation families. Preserve
   zero/nonzero branches, overflow/marker behavior, and positive progress.

4. Measure changes with separate metrics: hand-written proof source, generated
   data size, checker reduction work, object size, and wall-clock compilation.
   Historical site timings and counts of local trace classes do not establish
   an equivalent percentage reduction in kernel time or whole-proof size.

## Why the obvious sharing keys are unsound

The repository's decoder-sharing census gives state69/read0 with two contexts:
prefix `111110` exits at state105; prefix `1101001001110000` exits at state104.
The predecessor bit matters. It also shows that a repeated `(CI6, CC3)` subtree
returns to different ancestor paths at different occurrences. A common primitive
theorem must parameterize and preserve this whole continuation context.

The primitive-step contract must use `Reach1`, not merely `Reach`. The reverse
direction of `KSim.halts_iff` descends by the positive number of physical steps
used for one source step. Zero-step source progress would make that induction
invalid. Decoder prefixes may have zero length; the subsequent primitive must
supply the missing positivity.

## Evidence supplied here

The delivered `KSim.semantic.patch` and complete self-contained Lean closure
compile against Lean 4.32.0. Fifteen original definitions have exact source
equality checks. Five original API signatures and the new semantic client are
typed. Nine named theorem assumption reports use only standard Lean axioms.
The prototype changes no concrete table or program and does not establish new
state-count, minimality, internalization or whole-endpoint build claims.
