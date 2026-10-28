# Full-seed theory recognizer and C222 axiom images: author receipt

27 October 2026. **Author fresh pair PASS; independent acceptance pending.**
Author: circuit_reduction. Final main 336 lines; Checks 82 lines. The entire
final pair and every development change were read before their relevant
execution. Preparation, compilation and freezing drivers were also read
before execution. Only the two new proof sources and owned evidence were
written; no frozen source, shared object, shared documentation, equation
artifact or Git state was changed.

## Exact new result

The source theory is explicitly defined in the new namespace:

```lean
seedSchema := Set.range (fun K : SetTheorySemiproposition 2 =>
  (fullSeedBodyMeta K).univCl)
seedTheory := ((𝗘𝗤 ℒₛₑₜ) ∪ {irreflexiveSentence}) ∪ seedSchema
irreflexiveSentence := “∀ x, x ∈ x → ⊥”
```

The frozen `fullSeedBodyMeta` is unchanged. Every one of its free parameters
is universally closed. The packet constructs a particular `Theory.Δ₁`
instance for this actual set of sentences and proves, in arbitrary arithmetic
models with the explicit IΣ1 and IΣ2 instances,

```lean
ValidatorSourceDerivation222.AxOK seedSchema V
ValidatorSourceDerivation222.AxOK seedTheory V
```

The `AxOK` conclusions quantify over arbitrary internal formula codes,
internal theory membership, free environments and free-safe streams. They
do not take any source-axiom-image premise. The accepted actual ten-case
source derivation interpreter then gives

```lean
Provable seedTheory (^⊥ : V) →
  ∃ d : V, ArithmeticHistory222.value d = 2
```

The antecedent is an internal proof of falsum in precisely the new theory;
no existence of such a proof is asserted. The result uses actual current
C222 history values and source encoding. It is not restricted to standard
formulas, contexts, closure lengths or proofs.

## Recognizer and exact source binding

The literal body contains the identity-substituted matrix `[0,1]` in a
negative antecedent. The recognizer therefore uses the parameterization
`fullSeedBodyMeta (∼K)`. `seedSchema_eq_negRange` proves exact equality of
the two ranges by NNF negation involution. It does not change the source
schema or claim that negation is code-monotone.

`recognizerBody_quote` proves exact quoted-body equality for the raw
function `seedRecognizerBodyVal`. For its required standard code bound,
`subst01_quote` applies the existing raw identity-substitution theorem.
`negative_core_le_body` follows the exact chain of eleven proper syntax
constructors to the matrix occurrence. With parameter `∼K`, typed double
negation turns that occurrence back into `K`. This yields
`⌜K⌝ ≤ seedRecognizerBodyVal ⌜K⌝` without any unsupported monotonicity of
substitution or negation.

`recognizerBodyGraph` is one fixed Σ1 formula. The finite graph is factored
through explicit substitution, left-body and right-body graphs; their
correctness is proved in every IΣ1 model. All five matrix occurrences and
all original membership/subset constants remain present. In particular,
the `[0,2]` raw vector occurs on both sides. Separate fixed-quote cast
lemmas prevent Lean from expanding large constant codes during elaboration.
No semantic hypothesis substitutes for graph correctness.

`seedCh` supplies explicit Σ1 and Π1 presentations of the bounded
universal-closure recognizer. They include internal bounds on the closure
length and body, actual `qqAlls`, formula typing, shift-fixedness, exact
bound-variable count, `fvarVec` substitution, and a bounded typed matrix
code. `seedR_defined` proves both presentations compute the same literal
`SchemaRecognizer`. The existing generic `schemaRecognizer_quote_iff`
proves standard-quote membership is exactly the new source set; properness
comes from the all-IΣ1-model graph identities. The standard quotation
argument is used only to verify the source theory's recognizer, not to
standardize arbitrary internal members during image construction.

## Internal universal closure and discharged images

`closure_image` is a separately stated generic internal closure theorem.
It uses Π2 order induction available under explicit IΣ2. Its invariant at
internal index `i ≤ m` quantifies over **every** free environment `F`:

```
StreamFree s F →
CProv (encode F 0 s (subst (fvarVec (m-i)) (qqAlls b i))).
```

The successor step applies the induction hypothesis at `eigen F s ∷ F`.
The actual `fresh_resources ... .2.2.1` supplies its free-safe stream, and
the proved `free_subst_qVec_fvarVec` identity matches the precise one-slot
opening required by the actual C222 `all_rule`. The source body's
shift-fixedness is propagated through every internal `qqAlls` layer.
There is no fixed-context GEN rule and no standard-natural induction on
the internal closure length. At `i=m`, the exact empty substitution is
removed by the typed identity theorem.

The generic closure theorem's base-image premise is fully discharged in
`recognized_seed_image`: internal membership yields an internally typed
matrix, its typed negation invokes the accepted `typed_fullSeed_image`, and
this holds for every free-safe environment needed by the invariant.
`axOK_seedSchema` converts the actual Δ1 membership graph to this image.
The finite union in `axOK_seedTheory` is split literally. Equality uses the
accepted five-image equality recognizer, and membership irreflexivity uses
the accepted Eind-based proof. Primitive numeric equality is not identified
with interpreted source equality.

## Checks and scope limits

Checks include truth/falsity matrix code bounds; the exact negative-body
quote; actual recognizer evaluation; arbitrary internal closure length;
closure of an arbitrary matrix; a nested matrix with free parameters 17 and 31;
overlapping requested streams; the actual even stream 2 with empty free
environment; the exact three-part theory definition; arbitrary internal
membership; and the actual History222 value 2 endpoint. All thirteen axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
These are Lean metatheory dependencies, not newly added HA rules.

This is the first concrete `AxOK` discharge for the fully closed full-seed
theory, together with equality and literal irreflexivity. It does not
identify this newly named theory with a historical unimported FQName,
raw CP/GIC, ZFC, tagged Collection or a quotient/bisimulation theory. It
provides no new ZFC-to-seed interpretation, internal decimal215 simulation,
Pell-to-equation calibration, or closed HA equation equivalence. Those
obligations remain separate.

Complemented47_review performed a source-only mathematical challenge of
the earlier complete draft and the relevant imported contracts, finding
no mathematical/interface issue. That was not a fresh replay or acceptance
of this final packet; root will arrange independent verification.

## Reuse and fresh verification

The exact main imports are `ZFCinPA.SchemaClosure`,
`ZFCinPA.ValidatorSourceFullSeed222`, and `ZFCinPA.ValidatorEqualityImages222`.
The private provider is
`/tmp/validator-full-seed-theory222-author-ornon89h/lib`.
It reuses the approved 191 current-source modules, including 136 Foundation
modules, 599 cached artifacts and 45 explicit external boundaries including
Init and meta Aesop. The accepted root FullSeed and Equality providers are
selected explicitly. The added SchemaClosure/Foundation subset uses its
previously authenticated source/object/trace providers; none was rebuilt.
Inherited qualifications about historical companion captures remain in
the full inventory. This is scoped authenticated reuse, not a fresh
whole-dependency proof replay.

The preparation snapshot is `4d1841128e825f8eb896fb41585fdb6c57f31544`.
The plan, all selected source/object/companion and package boundary pins,
compiler, toolchain and Lake manifest are rehashed before and after each
build. The final run has 2528 observations and retains 874 inherited audit
observations; freezing rehashes both sets. No cached client imports either
new leaf. New outputs are private regular files; cached symlink targets
are never compiler outputs.

Only the new pair was freshly compiled with pinned Lean 4.32,
`-M6000 -j1 -DElab.async=false`, `LEAN_NUM_THREADS=1`, no `LEAN_SRC_PATH`,
and the 512 MiB reserve guard. Final timings: 26.254/3.196 seconds. Main log
is empty; Checks contain exactly 13 standard-only reports and no diagnostics.

All four compiler attempts are preserved: two failed mains; a clean main
followed by a failed Checks namespace opening; and the final passing pair.
Development errors were default-heartbeat quotation/monolithic-graph
elaboration, namespace and rewrite-direction issues, one small natural
bound conversion, and the missing Checks namespace. The quotation and
fixed graph proofs were factored without increasing any resource cap or
changing an import. The previously passing main object is retained and
byte-identical to the final main. No failed object is used as evidence.

- Main source: `481f8f44a4d01cda7f41d92463336aabae66573e3764f056785667192bb33acd`.
- Checks source: `048cc4850a073f18c3eb29bc704b61b755db8c45eb91d922ae2743593be9ad6c`.
- Main object: `c0279d1a80ba6b1a7bafa5f75c0cf9e1a66126f0a5f26eb4b2bd76bb06995fb0`.
- Checks object: `3f21b6773186041147620319a7a214f32baed3b729ed9e55b7e24ee6bc079164`.
- [Frozen cache](validator-full-seed-theory222-cache.json): `f6419623c32fa0870b6dd368fbb2e324cb6a566aea6c38aa5c72d3d71e0c23ad`.
- [Replay summary](validator-full-seed-theory222-replay.json): `a43514a4122ddf304a805511b4ef444b30418c7408eb217882a8d8233f7e0502`.
- [47-file manifest](validator-full-seed-theory222-author-replay/FILES.json): `4f20507b3bafbd9e9158605bf6e162bdbc7bc64ab25d06c50145c5f30fce723b`.
- [Approved proposal](../research/validator-full-seed-theory222-plan.md): `955b3a4351649ca83fbbe357a3a0d2379f833e2b151aec20f190ac65a5c54e7a`.
