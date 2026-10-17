# Finite conjunction and named-existential normalization

`ModelCodedNamedLogicalNormalization254` supplies finite logical proofs for the
implication/Bottom encodings used by the separately checked circuit decoder.
Matrices and labels are arbitrary internal elements of any IΣ1 model; these
proofs do not recurse on an internal formula code.

The conjunction theorem is

```text
T ⊢ ((p → (q → Bottom)) → Bottom) ↔ (p ∧ q).
```

It combines the existing finite currying theorem ECKCC, classical double
negation ECCOO, and implication congruence. Intro and left/right projection
helpers let later clients assemble or extract the nested conjunctions in the
actual bundle. No target-theory axiom or GEN resource is used here.

`namedExists a p` is the native existential over the same actual `namedBody a p`
used by named universals. Typed DeMorgan and the already checked binding-negation
law give the exact syntax identity

```text
¬namedFormula a (¬p) = namedExists a p.
```

The relative existential normalization is

```text
T.internalize V ⊢
  (namedFormula a (p → Bottom) → Bottom) ↔ namedExists a p.
```

To lift the finite `p→Bottom ↔ ¬p` proof under the named universal, the generic
lemma exposes the exact actual named-GEN resource. Named existential congruence
uses that same resource. Actual ZF and ZFC audit callers discharge it with the
checked all-internal named-GEN theorem. There is no fresh-label, closed-matrix,
shift-fixed or standard-code premise; selected label0 is explicitly tested.

The exact69-line source and focused audit passed Lean4.32.0 on the first attempt:
seven ordered axiom reports, ten callers, zero warnings, and only `propext`,
`Classical.choice`, and `Quot.sound`. Recorded source/audit compiler times are
2.286822s/2.369670s. The guarded check reused the actual rho1 successful object,
with41 project predecessors, six external boundaries and106 recorded inputs.
No dependency builds or downloads occurred.

The portable maintained replay is

```bash
python Logic/Interpretability/ZFCinPA/check_model_coded_named_logical_normalization254.py --output /tmp/named-normalization-replay
```

Explicit repository/dependency/compiler/library, source/audit and rho1 parent
paths are supported. `--project-cache` relocates selected predecessor objects;
`--namespace-cache` supplies the complete existing Foundation namespace.
The historical unused Cantor object remains an explicit separate input, and a
relocated parent record may give its new path with the same recorded identity.
Only the previously accepted exact same-source Cantor pair is allowed.

The guard checks the exact rho1 10/16 parent contract, selected source/object
identities and actual first providers including Omega, compiler/pins/manifest,
ordered audit reports/callers, unchanged inputs and fresh object. Packaging adds
two explicitly unbuilt override/relocated preflights and three rejection controls
for changed source, an existing output directory and optimized Python. Version
queries occur in preflight; there are zero proof builds or successful-proof
replays during packaging. The original preparation/PASS records and exact
source/audit/guard snapshots remain preserved.

These helpers normalize the already interpreted finite circuits. They do not
prove the container C or image-collection G, the full bundle, general accepted
proof translation, or a PA consistency endpoint.
