# Internal decoded truth and modus ponens

[`ModelCodedDecoderPropositional254`](Lean/ZFCinPA/ModelCodedDecoderPropositional254.lean)
constructs actual internal proof codes for the source truth alias and the
modus-ponens rule. Formula codes and both input proof codes range over every
IΣ1 model, including nonstandard elements. The target can be any Δ1 theory
in the encoded set language; the audit includes the actual ZF and ZFC theories.

`impIdentityCode` builds an excluded-middle proof followed by disjunction
introduction. `mpCode` builds a cut from the two supplied proofs, weakening,
conjunction introduction and excluded middle. Both operations have fixed Σ1
graphs and are total on raw codes. Their correctness theorems use the actual
internal `Proof` predicate. No proof witness is selected from a provability
assumption to define either operation.

The source implication constructor is `4*P(a,b)`. When `a=b=0`, this is zero,
whose decoder is the literal truth formula T0 rather than the syntax tree
`T0 → T0`. `decodedMPCode` therefore returns the antecedent proof unchanged
in that case. For every other pair it applies the explicit target MP code
to the checked decoder outputs. The checked constructor equation justifies
that branch. The graph and proof theorem both retain this case split.

`decodedZero_isProof` supplies an explicit proof of the decoded zero alias.
The two provability corollaries package these concrete proof codes into
existential witnesses. This is a local proof-rule translation: generalization,
the twelve source axiom rows, accepted-history induction, the decoded-falsity
endpoint and the full PA consistency comparison remain separate.

The [kernel record](results/model-coded-decoder-propositional254-verification.json)
passes nine ordered axiom reports and fourteen callers, with only the three
standard Lean axioms and zero warnings. Source and audit took 7.540 and
3.289 seconds on pinned Lean 4.32.0, one thread and a 4 GiB limit. The checker
records 23 project predecessors, six external boundaries, actual first
Lean/Omega providers, all 69 input identities and the unchanged fresh object.
No dependency was built or downloaded.

The first attempt failed in the two zero-alias case proofs. The final source
uses an explicit contradiction for the impossible graph branch and simplifies
the zero-branch result directly. The proof-code definitions, theorem statements
and audit are unchanged. The failed attempt and source diff are preserved in
the [publication record](results/model-coded-decoder-propositional254-publication.json).

The original successful record is copied byte for byte. The portable runner
freezes the final source and audit and removes their command-line hash
overrides. Default and relocated-cache preflights are explicitly unbuilt.
Four controls reject Python `-O`, a nonempty output directory, a wrong first
Omega provider and a corrupted isolated constructor object. The original
providers remain unchanged.

```sh
python -B Logic/Interpretability/ZFCinPA/check_model_coded_decoder_propositional254.py \
  --dependency-root /path/to/built-dependency-checkout \
  --output /fresh/external/decoded-propositional-check
```

Source, audit and constructor evidence default to the maintained files.
`--decoder-cache` relocates all 23 exact predecessor objects;
`--namespace-cache` supplies the complete Foundation namespace mirror.
`--prepare-only` checks preparation and provider identities without compiling.
