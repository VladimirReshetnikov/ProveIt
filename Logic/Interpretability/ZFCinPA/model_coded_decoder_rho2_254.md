# Internal proof of the decoded numerical rho2 row

`ModelCodedDecoderRho2_254` proves, in every IΣ1 model and for arbitrary
internal parameters `a,b,c`:

```text
Provable ZF  (decode (ArithmeticTemplates254.rho2 a b c))
Provable ZFC (decode (ArithmeticTemplates254.rho2 a b c)).
```

This is the actual numerical row

```text
All(a,Imp(b,c)) -> (All(a,b) -> All(a,c))
```

using the maintained arithmetic constructors and decoder. The parameters may
be nonstandard and may collide or be zero. Neither endpoint has a freshness,
closed-matrix, axiom-closure or proof-selector premise.

The proof first establishes monotonicity of the named universal. From an
internal proof of `p -> q`, actual named GEN supplies a proof of
`AllNamed(a,p -> q)`. The checked BindOne implication law exposes the two typed
bound bodies, and the finite checked universal-distribution template yields
`AllNamed(a,p) -> AllNamed(a,q)`. Applying this to both directions gives named
universal congruence. The generic helpers state their exact GEN resource;
actual ZF/ZFC corollaries discharge it with checked all-internal proof renaming.

The decoded inner implication is related to the target implication by the
checked provable equivalence, including `wim 0 0=0`. Named universal congruence
lifts that equivalence under the actual numerical `wal`; implication congruence
then handles both outer implications. The finite distribution template finishes
the row. There is no claimed syntactic implication homomorphism at the zero
alias, and the literal decoder truth formula may contain free label zero.

Pinned Lean 4.32.0 checked the final source and focused audit: eight named axiom
probes and eight callers, zero warnings, only `propext`, `Classical.choice` and
`Quot.sound`. Source/audit times were 2.429/1.998 s, with one thread and a 4 GiB
limit. The first source attempt failed only at the standard arity-zero/one
casts in the typed named body; explicit `Nat.cast_zero`/`Nat.cast_one`
normalization fixed it. All logical proofs and theorem contracts were unchanged.
The failed attempt, exact guards and source/audit snapshots are retained.

The guard merges three genuine successful parents: decoded GEN, the binder/
distribution template, and decoded Lukasiewicz implication equivalence. Their
three fresh objects are imported. Exact import traversal selects 35 project
predecessors and six external source/object boundaries, with all shared source/
object identities checked. The compiler, clean pinned dependency checkouts,
manifest, actual Omega object, actual first providers and all 98 input hashes
are checked before and after. No dependency was built or fetched; these are
selected cache boundaries, not independent attestation of the whole dependency
cache.

The already recorded Cantor exception is preserved exactly: identical source
`aadfdeb41e75c1652b555ed996fea5d15d7f1b9f65c7c553823a99773ee24c84`,
selected object `bf2ee28833f61c6c9c44244cb22ec8932c6a3570beed1e94749b2ab1e6b9cc71`,
unused recorded object `ff1e2f291d3d81940552aeb6a2a221dbfefd032005b10c9ca4d20ba4b84fb3b8`.
Both individual artifacts remain bound; arbitrary same-source object changes
are rejected.

Portable override and copied-project-cache preflights passed, along with six
rejection controls: optimized Python, nonempty output, altered source,
inconsistent shared parent object, unrecorded Cantor pair and an actual Omega
shadow with all historical tool lists empty. They perform no proof builds;
compiler validation does query `lean --version`. The relocation copies the 35
selected project objects and explicitly reuses the namespace/external objects
and unused recorded Cantor artifact.

From the repository root with existing pinned providers:

```sh
python Logic/Interpretability/ZFCinPA/check_model_coded_decoder_rho2_254.py --output /absolute/fresh/rho2
```

`--prepare-only` checks identities without compiling proofs. The guard accepts
`--repo`, `--dependency-root`, `--source`, `--audit`, `--gen-evidence`,
`--distribution-evidence`, `--logic-evidence`, corresponding parent source/audit
overrides, `--binder-source`, `--project-cache`, `--namespace-cache`, ordered
repeated `--library-path` and `--lean`. Missing providers are rejected. Proof
runs require the serialized compiler slot.

This establishes one actual decoded logical row and reusable named-universal
congruence. It does not construct a represented function selecting target
proofs, interpret the remaining logical rows or the gated bundle, or complete
the accepted-history translation/PA-internal C254–ZFC consistency comparison.
