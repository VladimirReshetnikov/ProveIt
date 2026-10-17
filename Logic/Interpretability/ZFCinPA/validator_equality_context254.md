# Internal equality contexts for the configurable encoder

`ValidatorEqualityContext254` represents a conjunction of equalities between
the coordinates of two internal bound-variable stacks. It proves every
coordinate projection, both directions of the cons law, and the finite
assumption discharge needed by the checked relational quantifier rule.
The prefix length, stacks, labels and proof witnesses are arbitrary elements
of an IΣ1 model, including nonstandard ones.

Write `P(n,B,B')` for the prefix context and `EqCtx(B,B')` for the full context.
The fixed primitive-recursion blueprint gives the exact numeric equations

```text
P(0,B,B') = 0
P(n+1,B,B') = conj(weq(B[n],B'[n]), P(n,B,B'))
EqCtx(B,B') = P(len(B),B,B')
```

Here `0` is the literal validator's truth code and
`conj(a,b) = wim(wim(a,wim(b,1)),1)`. The blueprint is chosen before the ambient
model; its graph is fixed Σ1 and its total function has a Δ1 interface. This
uses internal primitive recursion, not an external list of finitely many
standard coordinates.

Every `i<n` yields a literal-validator proof of
`P(n,B,B') → weq(B[i],B'[i])`. The proof uses Σ1 induction on the internal
prefix length, with a bounded family of numerical proof witnesses.

The recursion places the newest coordinate equality first. Finite classical
proofs of conjunction interchange therefore give both CProv implications

```text
EqCtx(x::B,y::B') ↔ conj(weq(x,y), EqCtx(B,B')).
```

Both directions are separate proved implications; this is not a numeric
identity. A pushed-context body proof can consequently be converted to
`EqCtx(B,B') → weq(x,y) → body`, and back. The final `all_of_cons` client
combines that discharge with the
[finite quantifier interface](validator_quantifier_core254.md). It retains all
four vacuity premises explicitly.

The raw computation and cons/projection laws need no equal-length premise:
`EqCtx` uses the left stack's length and the total right-stack lookup. A later
encoder transport theorem must separately establish that both stacks have
the source depth. This module does not yet prove formula alpha equivalence,
construct the four vacuity witnesses, rename arbitrary accepted proofs, or
compile source derivations. It claims no consistency endpoint or new machine
state count. The [configurable encoder](validator_environment_labels254.md)
and [encoded-formula vacuity](validator_environment_vacuity254.md) supply the
other components for that next induction.

## Verification

The 189-line source and focused audit pass pinned Lean 4.32.0 with **21 named
axiom reports, 24 callers, the standard three axioms only, and zero warnings**.
The source took 10.743 seconds and the audit 2.938 seconds, using one thread,
4 GiB and default Lean limits, with a 120-second timeout per command.
The source object hash was persisted before the audit and remained unchanged.
The [exact successful record](results/validator-equality-context254-verification.json)
is preserved without modification.

The checker reuses the exact checked environment and quantifier parents,
24 project objects, five direct external boundaries and two toolchain
providers. It checks 70 current input paths, before/after identity and actual
first-provider identity. The environment lane's Cantor object is retained;
Foundation's `HFS.Seq` anchor from the quantifier parent is not an actual
direct boundary of this closure. The external caches are explicit boundaries,
not an attestation of an entire Foundation namespace. No dependency was built
or downloaded.

Three failed source checks preceded the successful fourth attempt. The repairs
made the Fin2 parameter-vector equality explicit, supplied its function
argument, registered fixed arithmetic graph interfaces to avoid excessive
constructor unfolding in definability, and qualified the intended `neg`.
The second run compiled its frozen tuple-only snapshot while a later graph
instance proposal was being prepared; its snapshot failed and no PASS or
successful provider postcheck is claimed for that run. The proposal is retained
separately. The public statements, audit and proof limits stayed unchanged.
Exact sources, guards, logs, records and the overlap note remain in
[the history](results/validator-equality-context254-history.json).

The portable runner changes only maintained source/audit defaults.
[Author and independent reviews](results/validator-equality-context254-review.json)
record the exact successful evidence and a separate maintained-default
preparation with no proof build or compiler-version query.

## Reproduction

From the repository root, with the existing checked prerequisite objects:

```sh
python -B Logic/Interpretability/ZFCinPA/check_validator_equality_context254.py \
  --dependency-root /path/to/dependency-checkout \
  --output /fresh/external/equality-context
```

`--environment-evidence` and `--quantifier-evidence` accept relocated copies of
the exact parent records. `--project-cache` may select a supplied cache
containing all 24 prerequisite project objects, and `--namespace-cache` a cache
root containing the Foundation namespace mirror. `--source` and `--audit`
accept relocated copies of the frozen successful bytes. `--prepare-only`
performs no proof compilation or compiler-version query.
