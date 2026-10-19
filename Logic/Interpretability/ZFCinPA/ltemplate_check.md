# Checked template theory and internal proof compilation

The unchanged [LTemplate source](Lean/ZFCinPA/LTemplate.lean) passes a fresh
Lean check and **ten axiom probes with eleven typed clients**, with no
warnings. The [actual record](results/ltemplate-verification.json) checks
the reusable theory and compiler for fixed proofs over ZF enlarged by
placeholder predicates, equality, and full Separation and Replacement
schemas in the enlarged language.

For placeholder arities at most three, `compileT` specializes a standard
finite source proof at arbitrary internal predicate codes in an IΣ₁ model.
Free parameters are allowed: the compiler shifts the predicates at each
proof buffer instead of requiring them to be fixed by shifting. The source
proof itself remains external finite syntax. This does not compile arbitrary
internally coded source proofs or complete the later reflection generator.

The semantic interfaces identify the ZF reduct under genuine equality and
membership compatibility, extract Separation and globally total Replacement,
and use equality-aware completeness under an explicit validity premise.
Replacement retains the premise `∀ x, ∃! y`; it is not stated for an arbitrary
partial relation. These interfaces do not assert model existence.

Source and audit took 6.330 and 1.903 seconds with default proof limits,
one thread, 4,096 MiB and a shared 120-second deadline. All 168 recorded
inputs and the fresh first-provider object remained unchanged. Every
probe uses only standard Lean axioms.

The guard selects 23 project providers from the accepted OpenSchemaTemplates,
congruence/quotient and Foundation Z records. Nine opaque boundaries are
directly encountered; two more and the Omega tool are retained from the
older evidence. Init is direct. Older source options, warnings and missing
pre-audit captures remain explicit. The congruence result's original parser
failure and its later read-only recovery are distinguished: the failed record
has no postcheck map, while the recovery supplies a separate checked map.

The first new guard stopped before compilation by assuming that absent map
existed. Its root-reported failure receipt is retained. The next attempt
compiled the source but its audit could not infer the language parameters
of `pure_models`. Giving that client explicit `k` and `arities` arguments
produced the successful third attempt. The theorem source, audit statements
and proof limits are unchanged.

The [publication](results/ltemplate-publication.json) and
[history](ltemplate/history.json.gz) retain all attempts, guards, audit
versions and source snapshots. The [source/API peer review](ltemplate/peer-review.json)
and [audit correction](ltemplate/audit-v3-review.json) preserve the earlier
review's missed inference issue. This closes one original validator inventory
entry; the final PA equivalence for the exact 240-state machine remains open.
