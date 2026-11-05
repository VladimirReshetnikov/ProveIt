# Independent review: 64/65 literal-row Lean identity

**PASS within captured-provider and external-transcription scope.** The Lean
[`RationalCarrier64.lean`](../../research/rational-carrier64-lean-identity/RationalCarrier64.lean)
defines the complete 64- and 65-row arithmetic values over an arbitrary
commutative ring. Under exactly `beta*Urank=MF` and `Wrank=MC−MF`, it
proves equality of the two rank expressions, then equality and zero
iff of the full outputs. This argument assumes neither division nor
nonzero beta. The separate `value65_eq_carrier` theorem binds the generated
65-row definition to the imported `Carrier65.value`.

The independent [checker](check.py) compared the actual Lean let-bound
operations, aliases, shared-head tuple and value wiring against both frozen
JSON graphs. It verified their common 28-row prefix, five-versus-six-row
rank segments and common 31-row suffix, with 64 and 65 rows respectively.
This comparison is an external Python check; the Lean theorem does not
formalize JSON parsing or prove that a PDF has these rows. The checker did
not run the source-writing generator or replay Lean.

The successful attempt03 result and log match their temporary originals,
record Lean exit 0 and no resource stop, and contain exactly the three
reported axiom lines. The output object, captured `Carrier65.olean`, source,
generator and JSON inputs match their recorded hashes; all 15 direct
provider/companion/shadow guards matched at review time. The independent
checker ran exit 0 and retained [result.json](result.json). The direct
provider is a captured object from another worktree; source-to-object and
transitive/dynamic ancestry are not re-established here. Attempt01 failed;
attempt02's warning made the strict runner reject it, so neither is the
successful receipt.

The rational specialization `Urank=MF/beta` with nonzero beta is not
instantiated by this Lean module. In particular the fixed leaf values, their
nonzero denominator and integrality, any PDF binding and any iPRA endpoint
are outside this theorem. The symbolic rational leaf is not a new integer
64-operation record.

Checker SHA-256
`ef37698dce97915ae6a3b2a2ee7dcbb16f368feaeb2915b8caaaa81b35ccb423`;
result SHA-256
`8e7bc475fea6774748ee6b37d44fb3e66755597d7318f19c7f4e2e800f5b3de1`.
