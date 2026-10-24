# A supplied arithmetic checker for the original sealed-ZFC calculus

The direct annotated-certificate route now has a closed unary `ScalarPRCode`
program, `AnnotatedRefutationPR.refutationProgram`, with the Lean theorem

```text
(∃ certificate, refutationProgram.eval certificate = 1)
  ↔ BProv ZFCax_s [] fBot.
```

The theory, sealing operation, formulas, and seventeen proof rules are the
existing repository definitions. This route uses no K215 interface, machine
simulation, axiomhood oracle, calculus translation, or assumed syntax parser.
The program is literal executable data. Its construction does not select a
program from a primitive-recursiveness existence proposition.

## Exact sealed-axiom dispatch

`AnnotatedAxiomDispatch` supplies nine numeric branches in the original
`AxiomTag` order:

```text
Ext, Reg, Powerset, Pair, Union, Infinity,
Separation(argument), Replacement(argument), Choice.
```

Invalid tags reject. The seven fixed bodies are compiled from their finite
formula syntax using the existing constructor programs. Huge formula-code
numerals are not expanded into that many successor instructions. Their
closing lengths are certified by the actual bound-table validator, and their
outputs use the checked sealing program.

The schema branches reuse the frozen exact Separation and Replacement
programs, including every required renaming and the actual sealing operation.
Schema arguments and intermediate results are untrusted numeric inputs. A
successful first renaming table establishes an actual argument formula, so
schema soundness has no formula-parser hypothesis.

`program_sound` recovers an actual formula in `ZFCax_s` from every accepted
raw dispatch packet. `exists_program_iff` proves that some dispatch tag and
evidence are accepted for `formCode f` exactly when `ZFCax_s f`.

## Complete context and proof certificates

`AnnotatedAxiomContext` scans a numeric list of dispatch certificates. It
starts with the actual empty-context code, prepends each checked axiom, and
rejects any failed entry. Its raw-input invariant recovers an actual finite
context containing only `ZFCax_s` formulas. Acceptance requires consuming the
certificate list and matching the claimed complete context code. The explicit
fuel is untrusted; soundness holds for every fuel, and completeness uses the
actual finite certificate length. The empty context is correctly accepted.

`AnnotatedRefutationPR` combines this scanner with the frozen complete
logical-line scanner. Its six certificate fields are:

```text
context code, axiom fuel, axiom certificates,
proof-line fuel, proof-line certificates, unused.
```

Both scanners refer to exactly the same claimed context code. The logical
scanner checks the goal judgment constructed from that context and the
claimed formula code. The two numeric checks are multiplied, so acceptance
requires both to equal one.

`raw_sound` proves the stronger raw-goal statement: every accepted natural
goal code denotes an actual formula having an actual sealed-ZFC derivation.
The proof uses injectivity of the literal judgment constructor, rather than
assuming a successful formula or context decode. `complete` annotates every
existing `BProv ZFCax_s [] f` derivation using the independently proved
context and logical-scanner completeness theorems.

The closed refutation program constructs bottom's code from its syntax. Its
`exists_refutation_iff` and `no_refutation_iff` are exact external natural-code
correspondences with sealed-ZFC refutability and syntactic consistency.
`refutationProgram_primrec` follows from the supplied program's constructors.

## Exact source sizes

`AnnotatedCheckerSize` proves these actual program-tree counts with Lean
`decide`. It reduces finite code syntax only; it does not construct a compiled
`GraphRep` or expand the fixed formula-code numerals.

| Program | Nodes | Optimized nodes |
| --- | ---: | ---: |
| Sealed-axiom dispatcher | 58007 | 52913 |
| Complete axiom-context scanner | 58281 | 53187 |
| Closed sealed-ZFC refutation checker | 83281 | 76313 |

These are source program-tree counts. They are not polynomial variable counts,
operation counts for a Diophantine equation, or a claim that this route is
smaller than the existing closed baseline. The generic PR-to-polynomial
compiler expands arithmetic recursion and repeated subcomputations; a useful
small graph should instead reuse the shared quadratic constructor primitives.
No gigantic closed graph representation has been materialized here.

Dedicated checks cover invalid dispatch tags, the universal actual schema
cases, the empty axiom context, a claimed invalid context, unconsumed input,
an invalid first axiom tag, raw refutation rejection, and a positive closed
equality derivation. Complete fixed-axiom/schema certificates are supplied by
universal proofs. Running every branch of the PR dispatcher eagerly would
compute enormous fixed formula codes, so runtime controls intentionally avoid
that expansion.

All four main modules and four dedicated check files compile with no errors
or warnings. Eleven runtime controls return true. The six named size
theorems are kernel checked; fifty-four printed audits use only `propext`,
`Classical.choice`, and `Quot.sound`, or fewer.

## Internal boundary

This completes the external arithmetic refutation checker. It does not prove
that its syntax codes, local certificate relations, scanner loops, or rule
soundness have the required interpretation over arbitrary nonstandard
internal omega codes. Those model-level obligations remain explicit. The
existing internal semiring and pairing theorems are relevant foundations,
not an automatic transfer principle for this checker.

No new Diophantine degree, variable count, scalar-operation minimum, or
end-to-end internal consistency equivalence follows from the source counts.
