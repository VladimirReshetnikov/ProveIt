# Root74 proposed endpoint: source and semantics audit

This audit traces the **statements in source**, not elaborated Lean theorems.
At this snapshot it found no mismatch in the inspected graph slots, symbolic
port tuple, positive-model comparison, or the three adapter applications. The
root74 graph, bridge, adapter and their new transitive drafts remain
unelaborated. The audit does not show that iPRA proves these declarations,
that either side is true, or that ZFC is consistent.

## What the proposed endpoint says

`Root74EndpointDraft` proposes three theory-derivability declarations. The
native and standard theories each assert the equivalence

```
nativeNoZero (positiveShift Root74PositiveBridgeDraft.expression)
  ↔ ¬ mappedNativeRefutation embedding
```

inside the named theory. The equality-only reference declaration applies
`IPRAOrderErasure.erase` to the no-zero sentence and to
`mappedNativeRefutation embedding`, then negates the latter. The `⊢` notation
is a derivability/proof-existence assertion, not an assertion of either side.
The three bodies apply `native_of_positive`, `standard_of_positive`, and
`reference_of_positive`; standard transfer uses `provable_iff`, and the
reference transfer uses `nativeToReference`.

`mappedNativeRefutation f` is exactly
`IPRANativeFormula.native (Semiformula.lMap f rho)`. Here logical
`FoundationHAConsistencyNormalization.rho` is the Foundation arithmetic
provability predicate for `ZermeloFraenkelChoice` proving falsity.
`FoundationZFCConsistencyNat.sourceSentence` is the Foundation ZFC theory's
`.consistent`, and `source_eq_neg_rho` identifies it definitionally with
`¬rho`. The endpoint's displayed right side is the negation of the **mapped
native NNF refutation**, not literally the untransformed source consistency
sentence. `IPRABoundedRhoZFC.zfcEquiv` is the inherited theory-proof
comparison with the Gödel–Gentzen-translated mapped source; it is not a
claimed syntactic identity. `source_nat_iff_no_refutation` separately states
standard-natural semantics as absence of the particular Foundation BProv ZFC
refutation, using the validator and ZF/ZFC comparisons. These are existing
source declarations and dependencies, not a fresh axiom or provider audit.

## Which graph and domain

The expression is the literal 14-input 74-row positive-domain graph at
`CompactSymbolicModelIff.p`. Its variables are `[J,F,alpha,f,i,T,w,s,r,eta,
zeta,y,gamma,h]`. The fixed Lean tuple is `[betaNat,paramKernel rho,lowNat,
betaNat+highNat]`, where `betaNat=2^(67*8807)−1` and `67*8807=590069`.
The numerical `CompactSymbolicKernel.rho=2^67` in this tuple is **not** the
logical provability predicate also named `rho` above. The symbolic K, low and
high terms are not expanded or bound here to retained physical bytes.

`PositiveModelBridge` quantifies over every model of IΣ₁ and states that an
all-positive literal zero exists exactly when the represented machine-215 run
reaches its specified blank-halting state. The 78→74 source comparison is an
existence-level comparison: it can change the guard coordinate. The generic
adapter's `positiveShift e` substitutes `xᵢ+1` for each variable, and the
source theorem `internalZero_positiveShift` identifies its split-natural zero
with a zero of e at those shifted coordinates. `nativeNoZero` universally
quantifies the negation of equality of the two mapped split-natural terms.

The independently checked **74-operation** count and degree 107 refer to the
unshifted all-positive straight-line graph at its authenticated external port
specialization. They are not automatically a 74-operation bound for the
all-natural shifted expression, its recursively expanded expression tree, or
its formal arithmetic encoding. The shift needs its own sharing and operation
count. External graph/byte/degree checks and the Lean symbolic expression are
separate evidence boundaries; no symbolic-to-physical coefficient, payload or
PDF identity is established by this audit.

## Dependency boundary and reproduction

The existing static endpoint inventory records 159 bare draft modules and 31
directly imported qualified source modules. This checker verifies all 190
listed source hashes, Git tracking and equality to HEAD at the sample, checks
the displayed source interfaces and tuple definitions, and replays the literal
graph generator's source receipt. It does not follow all qualified, Foundation,
package or runtime transitive imports, resolve compiled objects or companions,
run Lean, check an axiom set, or establish build readiness. In particular, the
reviewed preventive tactic-import snapshots and small first-factor cut are
not part of the committed endpoint chain or slim overlay. The inherited root78
branch can still import the heavier `C44Short15Facts` source. The 74 graph's
external byte/degree receipt is not a physical binding for the endpoint.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-root74-endpoint-scope-audit/check_source.py | cmp - research/ordinary14-root74-endpoint-scope-audit/observation.json
```

The tracked/clean check is point-in-time and may fail after legitimate source
changes. No Lean process was launched.

Independent source review: [root74 endpoint scope audit](../../reviews/ordinary14-root74-endpoint-scope-audit-independent/README.md).
