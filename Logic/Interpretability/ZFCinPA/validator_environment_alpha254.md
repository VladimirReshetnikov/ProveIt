# Internal alpha transport under explicit fresh streams

`ValidatorEnvironmentAlpha254` constructs literal-validator proofs that two
configurable encodings of the same internal source formula imply one another.
Both directions use the same represented equality assumptions for the old
bound-variable stacks. The theorem applies to arbitrary internal formula
codes and environments, including nonstandard ones, in IΣ2.

Write `E(F,B,s,p)` for the [configurable encoder](validator_environment_labels254.md)
and `EqCtx(B,B')` for the [represented stack equality context](validator_equality_context254.md).
Under `len(B)=len(B')=n`, an internally well-formed formula `p` at depth `n`,
and the explicit freshness invariant below, the theorem supplies

```text
CProv(EqCtx(B,B') → E(F,B,s,p) → E(F,B',t,p))
CProv(EqCtx(B,B') → E(F,B',t,p) → E(F,B,s,p)).
```

The `FreshPair(F,B,B',s,t)` premise says that every label in each future stream
`s+2*k` and `t+2*k` avoids every stored free label, fallback label 1, and both
old bound stacks. It also says that the two streams never intersect:
`s+2*i ≠ t+2*j` for all internal indices `i,j`.

This invariant is preserved when the encoder pushes `s` and `t` onto the
respective stacks and advances both starts by two. Own-stream future labels
are strictly above their newly pushed head; cross-stream inequalities exclude
the opposite head. Thus a binder step has the same invariant for its body.

Term transport uses the corresponding EqCtx projection for a bound variable
and equality reflexivity for a shared free label. The actual set language has
no function symbols. Atomic transport uses the checked
[equality interface](validator_equality_core254.md) for both coordinates of
equality or membership. Conditional negation, implication and conjunction
proofs then handle the Boolean encodings.

The quantifier step combines the body induction hypothesis with the finite
[relational quantifier rule](validator_quantifier_core254.md). Both old-context
vacuity witnesses come from [equality-context vacuity](validator_equality_context_vacuity254.md).
The two cross-body witnesses come from
[encoded-formula vacuity](validator_environment_vacuity254.md), using the
opposite binder stream. The proof never requires a binder to be vacuous in
its own body. For the reverse implication, it retains `EqCtx(B,B')` and applies
finite equality symmetry only to the new head premise `weq(s,t)`.
Existentials use the same rule on negated bodies and then negate the result.

The uniform environment invariant contains numerical proof witnesses and is
Π2. The main proof uses Π2 induction on the internal formula code in IΣ2,
with fixed represented graphs for all numeric computations. It does not use
external recursion over standard formulas. At empty bound stacks, EqCtx is
truth, so `encode_formula_alpha` discharges it with `cProv_truth`.

The two streams must be explicitly disjoint. The theorem does not directly
compare overlapping starts such as `s` and `s+2`; a fresh intermediate stream
and composition can provide that later client. Concrete stream selection, internal source-proof translation, ZF axiom
reconstruction and the reverse consistency endpoint remain open. The proof
compiler can use the configurable encoder directly, since it already maps
falsum to the literal code 1. Identifying it with the separate fixed
`formulaEncoder` is an optional comparison, not a prerequisite for that route.
There is no global renaming closure for arbitrary accepted proofs or bundles,
and no new machine-state bound is claimed here.

## Verification

The 346-line source and focused audit passed their first pinned Lean 4.32.0
check with **18 named axiom reports, 22 callers and the standard three axioms
only**. Three source linter warnings remain: one unused `if_neg` simp argument
and two unused section variables. The audit has no warnings. The exact
successful source, including its original draft docstring, is retained without
a cosmetic recompilation.

The source took 12.632 seconds and the audit 2.957 seconds, with one thread,
4 GiB, default Lean proof limits and a 120-second timeout per command.
The source object hash was persisted before the audit and remained unchanged.
The [exact verification record](results/validator-environment-alpha254-verification.json)
is preserved unchanged.

The runner reuses exact checked EqualityContextVacuity and EqualityCore
parents, 28 project objects, five direct external boundaries and two toolchain
providers. It checks 78 current input paths and their actual first providers.
It introduces no new direct external boundary or Cantor object variant. The
external caches remain explicit boundaries; no entire Foundation namespace
attestation is asserted. No dependency was built or downloaded.

The [history](results/validator-environment-alpha254-history.json) retains the
single successful attempt, its exact source/audit/guard/logs, initial prepared
record, source reviews and the separate maintained-default preparation.
The portable runner changes only maintained source/audit defaults.
[Author and independent reviews](results/validator-environment-alpha254-review.json)
record the exact evidence and the unbuilt default preparation, which makes
no compiler or compiler-version call.

## Reproduction

From the repository root, with the existing checked prerequisite objects:

```sh
python -B Logic/Interpretability/ZFCinPA/check_validator_environment_alpha254.py \
  --dependency-root /path/to/dependency-checkout \
  --output /fresh/external/environment-alpha
```

`--context-vacuity-evidence` and `--equality-evidence` accept relocated copies
of the exact parent records. `--project-cache` may select a supplied cache
containing all 28 prerequisite project objects, and `--namespace-cache` a cache
root containing the Foundation namespace mirror. `--source` and `--audit`
accept relocated copies of the frozen successful bytes. `--prepare-only`
performs no proof compilation or compiler-version query.
