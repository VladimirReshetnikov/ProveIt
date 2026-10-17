# Internal named-binder laws and universal distribution

Two checked prerequisites supply concrete parts of the decoded C254 rho2
quantifier row. They are separate from the already checked decoded GEN client.
This package does not yet prove the numerical rho2 row.

`ModelCodedNamedBinderLaws` proves, for every IΣ1 model, arbitrary internal
bound depth, selected label and well-formed formula at that depth:

```text
bindOneAt a d (neg p)   = neg (bindOneAt a d p)
bindOneAt a d (imp p q)= imp (bindOneAt a d p) (bindOneAt a d q).
```

The proof uses actual Π1 structural induction. The internal depth changes under
quantifiers, and the induction retains the arbitrary internal selected label.
The represented binder operation is total Δ1. There is no standard-formula,
finite external support, closed-matrix or freshness premise.

`ModelCodedNamedQuantifierTemplates254` constructs a finite internal proof

```text
T ⊢! All(p -> q) -> (All p -> All q)
```

for any internal target theory and arbitrary internal typed unary matrices
`p,q`. It specializes the shifted universal premise at free zero, applies the
actual typed `allImpAll` rule, and discharges the premise. The context is shifted
explicitly; leaving it unchanged would fail for arbitrary free parameters.
No target axiom or consistency premise is used. The unary level is fixed, while
the matrix codes may be nonstandard.

Pinned Lean 4.32.0 checked both sources and focused audits, using one thread
and a 4 GiB limit. Binder passed on its first proof attempt (2 probes,5 callers,
2.780/1.773 s); Distribution passed on its second (1 probe,3 callers,
1.778/1.747 s). Both report zero warnings and only `propext`, `Classical.choice`,
`Quot.sound`. Distribution's initial source error required only normalization
of the shifted universal premise and qualification of the internal `free`
operator; its proof architecture and statement are unchanged. Its Type-valued
audit declarations were placed in a `noncomputable section` before that first
proof attempt.

The Binder guard checks ten project predecessors and six external boundaries;
Distribution checks eleven, reusing the exact passed Binder object without
rebuilding it. Both check compiler/dependency pins and manifest, actual
source/audit bytes, the actual Omega provider and actual first-provider identities
before and after. This is selected source/object boundary verification, not an
independent attestation of the entire external cache. No dependency was built
or fetched. All successful build inputs and fresh objects retain their final
hashes.

The complete local preparation/build history embeds six records, twelve Lean
snapshots and the exact guards. An inherited scope-string typo in the first
unbuilt Binder preparation was corrected before any proof build. Historical
rechecks identify every intentionally changed live path rather than asserting
that old source/guard paths still match their initial hashes. The original
bytes remain recoverable.

Four portable preflights, including copied-project-cache relocation, and six
rejection controls passed. These perform no proof builds, though compiler
validation invokes `lean --version`. The relocation copies eleven project
objects and explicitly reuses the Foundation namespace and external providers.

From the repository root with the existing pinned providers:

```sh
python Logic/Interpretability/ZFCinPA/check_model_coded_named_binder_laws.py --output /absolute/fresh/binder
python Logic/Interpretability/ZFCinPA/check_model_coded_named_quantifier_templates254.py --output /absolute/fresh/distribution
```

Both guards accept `--repo`, `--dependency-root`, `--source`, `--audit`,
`--namespace-cache`, repeated ordered `--library-path`, `--lean` and
`--prepare-only`. Binder accepts `--bind-one-evidence`/`--bind-one-cache`;
Distribution accepts `--binder-evidence`/`--binder-cache` plus Binder source/audit
overrides. A namespace cache must contain an existing complete `Foundation/`
mirror. Missing providers are rejected; proof builds require the serialized
compiler slot.

The next numerical client can project each direction of the checked decoded
implication equivalence, apply actual ZF/ZFC named GEN and this distribution
proof, obtaining named-universal congruence. That would transport the decoded
inner implication of rho2. It is a source-first next step, not a theorem supplied
by this package. Rho4's distinct-variable slot swap, rho6's relative falsity when
binding label zero, the gated bundle and the full PA-internal consistency
comparison remain separate obligations.
