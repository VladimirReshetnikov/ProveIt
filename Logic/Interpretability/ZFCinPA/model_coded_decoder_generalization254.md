# Decoded numerical GEN in internal ZF and ZFC

`ModelCodedDecoderGeneralization254` connects the live arithmetic universal
constructor to the checked internal proof-renaming theorem:

```text
Provable ZF  (decode h) → Provable ZF  (decode (ArithmeticCode254.wal a h))
Provable ZFC (decode h) → Provable ZFC (decode (ArithmeticCode254.wal a h)).
```

The variable, matrix and input proof may be arbitrary internal codes in every
IΣ1 model. There is no freshness, closed-matrix or target-axiom-closure premise.
The literal decoder truth formula's free zero is permitted, as are repeated
binders. The result is existence of an internal target proof; it does not
choose a represented output-proof function.

The proof is a small client of three checked interfaces. The actual
`ArithmeticCode254.wal a h` is `4*cantor a h+2`; the decoder constructor theorem
identifies this with `namedAll a (decode h)`; the checked all-internal ZF/ZFC
proof-renaming theorem supplies that named generalization. The universal tag
is always positive, so this client introduces no implication-zero case split.

Pinned Lean 4.32.0 checked the source and audit on the first proof attempt,
with one thread and a 4 GiB limit. The three named axiom reports and six callers
passed with zero warnings and only `propext`, `Classical.choice`, `Quot.sound`.
Source/audit times were 1.696/1.859 s. The callers include arbitrary internal
variable/matrix codes, repeated equal binders, the literal zero truth matrix
with selected label zero, and an explicit input proof witness.

The guard merges the passed proof-renaming and decoded-Lukasiewicz parent
records, then follows the actual new imports. It selects exactly 29 project
predecessors and six external source/object boundaries, and checks the actual
Omega provider, compiler, dependency pins/manifest, source/audit identities and
actual first providers before and after. It does not import the Lukasiewicz
module or reuse its fresh object; the parent record supplies the already
checked numerical constructor predecessor. ArithmeticTemplates and the
propositional decoder module are pruned from the actual import closure.

The inherited Cantor object exception remains exact and explicit: source
`aadfdeb41e75c1652b555ed996fea5d15d7f1b9f65c7c553823a99773ee24c84`,
selected object `bf2ee28833f61c6c9c44244cb22ec8932c6a3570beed1e94749b2ab1e6b9cc71`,
unused recorded object `ff1e2f291d3d81940552aeb6a2a221dbfefd032005b10c9ca4d20ba4b84fb3b8`.
The unused object is individually hashed before and after; every other shared
parent source/object identity must match exactly. This is not general
acceptance of arbitrary same-source object variants. These are selected cached
boundaries, not an independent attestation of the entire dependency cache. No
dependency was built or fetched.

The original preparation is retained separately. Before the first proof build,
`autoImplicit false` was added to source and audit and the corresponding guard
pins were updated. No proof body changed. The initial guard/source/audit and
both prepared snapshots remain embedded in the history record; its recheck
explicitly identifies these three changed live paths and verifies the other
82 inputs unchanged. The successful run's 85 inputs and new object remain
bound to their exact final bytes.

Portable override and copied-project-cache preflights passed, with six rejection
controls: optimized Python, nonempty output, altered source, inconsistent shared
parent object, unrecorded Cantor variant, and an actual Omega shadow even with
empty historical tool lists. These perform no proof builds; compiler checks do
invoke `lean --version`. The cache test copies 29 project objects and explicitly
reuses the external Foundation namespace and boundary objects.

From the repository root, with the existing pinned providers available:

```sh
python Logic/Interpretability/ZFCinPA/check_model_coded_decoder_generalization254.py --output /absolute/fresh/gen
```

Use `--prepare-only` for identity checks without a proof build. The guard accepts
`--repo`, `--dependency-root`, `--source`, `--audit`, `--proof-evidence`,
`--numeric-evidence`, parent-source/audit overrides, `--project-cache`,
`--namespace-cache`, repeated ordered `--library-path` and `--lean`. A relocated
namespace root must contain the existing complete `Foundation/` mirror. Missing
providers are rejected. Proof runs require the serialized compiler slot.

This completes the decoded GEN rule locally. It does not interpret the eight
logical axiom rows, the gated container/collection bundle or the whole accepted
history, and it does not prove a PA-internal C254/ZFC consistency comparison.
The separately drafted binder/quantifier-row sources are excluded from this
checked package.
