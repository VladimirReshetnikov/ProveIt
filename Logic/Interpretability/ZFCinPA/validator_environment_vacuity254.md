# Vacuity of internally encoded formulas

`ValidatorEnvironmentVacuity254` constructs literal-validator proof witnesses
for vacuous universal generalization of every internally well-formed source
formula, including nonstandard codes and depths. It combines the checked
[configurable encoder](validator_environment_labels254.md) with the finite
[quantifier interface](validator_quantifier_core254.md).

Write `E(F,B,s,p)` for the encoder and
`Vac(z,a) := CProv(wim(a,wal(z,a)))`. The hypotheses are

```text
len(B) = depth(p)
FreeAvoid(z,F) := z != 1 and every stored label in F differs from z
Avoid(z,B) := every stored label in B differs from z
StreamAvoid(z,s) := for every internal k, z != s + 2*k.
```

Under these hypotheses the main theorem proves `Vac(z,E(F,B,s,p))`.
The fallback free-variable label is 1, so its avoidance is explicit even when
`F` is empty. The result includes terms and atomic formulas, the empty bound
context, and a concrete zero-label client `Vac(0,E([],[],2,p))`.

The formula induction is internal **Π2 induction in IΣ2**. Its invariant
universally quantifies the environments and contains Σ1 proof witnesses;
Π1 induction would not justify that invariant. The ambient IΣ1 instance
supports the existing encoder and proof-predicate definitions; IΣ2 implies it,
and PA supplies both. Fixed represented function graphs keep the hierarchy
proof separate from the constructor induction.

At a binder the proof prepends `s` to `B` and advances the stream to `s+2`.
Stream avoidance supplies both the new head-label inequality and avoidance
of the remaining stream. The atomic cases use the original gated equality
and membership vacuity certificates. Compound cases use the checked finite
negation, implication and universal closure rules.

This supplies the body-vacuity resources needed for later alpha conversion.
It does not yet prove alpha equivalence, rename arbitrary accepted proofs,
translate source derivations, transport ZF axioms or establish a consistency
equivalence. No new machine-state bound follows from this checkpoint alone.

## Verification

The 191-line source and audit pass pinned Lean 4.32.0 with **10 named axiom
reports, 16 callers and only the standard three axioms**. The source check took
7.289 seconds and the audit 2.521 seconds, using one thread, 4 GiB and default
Lean limits, with a 120-second timeout per command. Two source warnings report
an unused IΣ1 section variable on the generic hierarchy lifts; the audit has
no warnings. The fresh source object hash was recorded before the audit and
remained unchanged. The [successful record](results/validator-environment-vacuity254-verification.json)
is preserved exactly.

The checker imports the exact checked Environment39/28 and Quantifier25/18
parents. It reuses 24 project modules, five actual direct external boundaries
and two toolchain providers, checking 70 current input paths and their actual
first providers. The additional direct boundary relative to the environment
lane is Foundation's `HFS.PRF`, already attested by the quantifier parent.
The quantifier parent's `HFS.Seq` anchor is unused by the actual import closure.
No dependency was built or downloaded, and the whole Foundation namespace is
not independently attested.

[All three failed attempts and the successful attempt](results/validator-environment-vacuity254-history.json)
retain their exact source, audit, driver, record and logs. The repairs address
hierarchy witness elaboration, explicit graph lookup and a shadowed typing
hypothesis. They change no public theorem statement, audit or proof limit.
The [review record](results/validator-environment-vacuity254-review.json) checks
current bytes, the fresh object and the separate maintained-default preflight.
The portable runner changes only source/audit defaults; its preflight compiled
nothing and made no compiler-version query.

## Reproduction

From the repository root, with the existing checked prerequisite objects:

```sh
python -B Logic/Interpretability/ZFCinPA/check_validator_environment_vacuity254.py \
  --dependency-root /path/to/dependency-checkout \
  --output /fresh/external/vacuity
```

`--environment-evidence` and `--quantifier-evidence` accept relocated copies
of the exact parent evidence. `--project-cache` may select a supplied cache
containing all 24 prerequisite project objects; `--namespace-cache` may select
a cache root containing the Foundation namespace mirror. `--source` and
`--audit` accept relocated copies of the frozen successful bytes.
`--prepare-only` performs no proof compilation or compiler-version query.
