# Internal proofs of the three decoded equality rows

`ModelCodedDecoderEquality254` proves the actual numerical C254 rows `rho7`,
`rho5` and `rho3` in every IΣ1 model, for arbitrary internal variable labels:

```text
rho7: c = a -> (c = b -> a = b)
rho5: c = a -> (c ∈ b -> a ∈ b)
rho3: a = b -> (c ∈ a -> c ∈ b).
```

The endpoints are `Provable T (decode (ArithmeticTemplates254.rhoN a b c))`
for any ordinary Δ1 set theory `T` containing the equality theory. The focused
audit instantiates all three with actual ZF and ZFC, including coincident labels,
all-zero labels and explicit internal proof witnesses. Labels and witness codes
may be nonstandard. No freshness, Foundation, choice of a well-founded model,
or proof-selector assumption occurs in these results.

Each proof first derives one fixed, universally closed ordinary sentence using
completeness over structures with genuine equality. Hilbert–Bernays D1 then
internalizes that fixed theorem. The actual typed `specialize₃!` operation opens
its three bound slots at the arbitrary internal free-variable labels. Its
argument order is `![c,b,a]`: slot zero is the innermost quantified variable.
Only the fixed closed sentence is quoted; no nonstandard formula or label is
passed to ordinary quotation.

The finite quotation/specialization pattern follows the existing equality seed
lemmas in `SetCongruence.lean`. This narrow module independently checks the
needed templates using the already checked decoder dependencies; it does not
import or attest the older module's full equality-replacement development.

The exact decoder equations identify the equality and membership atoms,
including the literal `Mem(0,0)` at numerical code one. The checked implication
congruence then transports the two implication constructors in each actual
arithmetic row. This uses provable equivalence and retains the implication zero
alias; it does not assume an injective decoder or a syntactic homomorphism.
The three intermediate decoder-equivalence lemmas need no equality-theory
premise; only the target equality proof templates use that premise.

Pinned Lean 4.32.0 passed 11 ordered axiom probes and 12 callers with zero
warnings and only `propext`, `Classical.choice` and `Quot.sound`. Source/audit
times were 3.604/2.068 seconds with one thread and a 4 GiB limit. The first
source attempt required an explicit natural-to-model cast normalization for
the membership symbol code and an elementary equality substitution in the
ordinary proof of rho3. Unused simplification arguments and unnecessary
equality premises on decoder-equivalence lemmas were also removed. No logical
row, arithmetic constructor or machine representation changed.

The guard reuses the successful decoded-Lukasiewicz object and its exact
closure: 27 project modules, six external boundaries and the actual first Omega
provider. Compiler, clean dependency pins, manifest, selected source/object
identities, all 78 inputs and the fresh object are checked around the proof
commands. The previously recorded Cantor compiled-artifact pair is inherited
with both hashes checked individually; the original selected object remains
the actual imported provider. This is selected-boundary verification, not
independent attestation of every object in the external cache. No dependency
was built or fetched.

The [successful record](results/model-coded-decoder-equality254-verification.json)
is preserved byte for byte. [History](results/model-coded-decoder-equality254-history.json)
preserves the initial unbuilt preparation, both proof attempts, six source/audit
snapshots and the exact drivers. It identifies intentionally changed historical
live paths and preserves their original bytes. The portable guard is identical
to the successful driver. Override and copied-project-cache preflights and four
rejection controls perform zero proof builds; compiler validation can call
`lean --version`.

From the repository root with the pinned existing providers:

```sh
python Logic/Interpretability/ZFCinPA/check_model_coded_decoder_equality254.py --output /absolute/fresh/equality
```

Use `--prepare-only` for provider validation without proof compilation. The
guard accepts `--repo`, `--dependency-root`, `--source`, `--audit`,
`--decoder-evidence`, `--decoder-cache`, `--namespace-cache`, ordered repeated
`--library-path`, and `--lean`. The namespace cache must contain a complete
existing Foundation mirror. Missing providers are rejected.

The two remaining quantifier rows, gated set-theoretic bundle, accepted-history
translation, global machine simulation and full PA consistency equivalence are
separate obligations. This checkpoint changes no machine states.
