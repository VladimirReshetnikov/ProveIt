# Vacuity of internal equality contexts

`ValidatorEqualityContextVacuity254` proves that a label absent from both
bound stacks can be universally generalized over their represented equality
context. It combines the checked [internal equality context](validator_equality_context254.md)
with the shared avoidance predicate from [formula vacuity](validator_environment_vacuity254.md).

For arbitrary internal `n`, stacks `B,B'` and label `z`, the prefix theorem is

```text
(∀ i<n, z != B[i]) → (∀ i<n, z != B'[i]) →
  Vac(z,prefixContext(n,B,B')).
```

Here `Vac(z,a)` abbreviates the literal-validator proof predicate
`CProv(wim(a,wal(z,a)))`. The prefix code starts at truth and prepends one
coordinate equality at each successor. The proof uses the checked atomic
equality-vacuity certificate and the finite negation/implication closures
that implement conjunction.

The stacks and generalized label stay fixed during **Σ1 induction in IΣ1**
over the internal prefix length. The avoidance premises are bounded families.
No standardness assumption on the length or coordinates is used, and vector
lookup remains total even beyond a stack's length.

For the complete equality context, the interface becomes

```text
len(B) = len(B') → Avoid(z,B) → Avoid(z,B') → Vac(z,eqContext(B,B')).
```

Equal lengths are explicit because the context iterator uses the left stack's
length. The quantifier client derives both context-vacuity resources for
`all_of_cons` from avoidance of both stacks. Its two cross-body vacuity
resources remain explicit. The module does not assert formula alpha
equivalence, rename accepted proofs, translate source derivations or prove a
consistency endpoint.

## Verification

The 61-line source passed its first actual run, followed by **three named
axiom reports and seven callers**, with only the standard three axioms and
zero warnings. Pinned Lean 4.32.0 took 7.404 seconds for the source and 2.068
seconds for the audit, using one thread, 4 GiB and default Lean limits, with
a 120-second timeout per command. The fresh object hash was saved before
the audit and remained unchanged. The [exact successful record](results/validator-equality-context-vacuity254-verification.json)
is retained without rewriting its scratch equality-context evidence path.

The guard imports the exact checked EqualityContext21/24 and
EnvironmentVacuity10/16 parents, with 26 reused project modules, five direct
external boundaries and two toolchain providers. It checks 74 current input
paths and their actual first providers. No new external boundary, dependency
build, download or whole-namespace attestation is introduced.

The [history](results/validator-equality-context-vacuity254-history.json) includes
the unbuilt initial draft, pre-run graph-instance change, exact successful
source/audit/driver/logs and separate preparations. The portable runner changes
only source/audit defaults. Its maintained-default preflight uses a byte-identical
maintained copy of the equality-context parent record; it compiles nothing and
makes no compiler-version query. The [review](results/validator-equality-context-vacuity254-review.json)
checks current bytes, actual providers and the fresh source object.

## Reproduction

From the repository root, with the existing checked prerequisite objects:

```sh
python -B Logic/Interpretability/ZFCinPA/check_validator_equality_context_vacuity254.py \
  --dependency-root /path/to/dependency-checkout \
  --output /fresh/external/equality-context-vacuity
```

`--context-evidence` and `--vacuity-evidence` accept relocated copies of the
exact parent records. `--project-cache` may select a supplied cache containing
all 26 prerequisite project objects; `--namespace-cache` may select a cache
root containing the Foundation namespace mirror. `--source` and `--audit`
accept relocated copies of the frozen successful bytes. `--prepare-only`
performs no proof compilation or compiler-version query.
