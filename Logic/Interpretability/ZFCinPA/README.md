# ZFCinPA — `PA ⊢ ∀ n, Prov_ZFC(⌜Conₙ(ZFC)⌝)`

This project formalizes, in Lean 4, the claim that Peano Arithmetic proves the
single arithmetic sentence

> for every `n`, `ZFC` proves the code of `Conₙ(ZFC)`

where `Conₙ(T)` is the bounded-complexity consistency scheme for `T` — the
polarity-aware, all-occurrences rank restriction defined in
[`SetTheory/BoundedConsistency`](../../../SetTheory/BoundedConsistency/README.md).

The point of the statement is that the semantic argument behind
`ZFC ⊢ Conₙ(ZFC)` can be made **purely syntactic**: not merely a metatheoretic
schema with one proof per numeral, but one arithmetic sentence with a single
`PA`-derivation, quantifying over the ambient model's elements — nonstandard
indices included.

## Status

**The target is not yet an unconditional theorem.** State it plainly:

| Statement | Status |
| --- | --- |
| `ZFC ⊢ Conₙ(ZFC)` for every metatheoretic `n` | **proved** (in `BoundedZFCConsistency`) |
| `𝗭𝗙𝗖 ⊢ conZFCSet n` inside Foundation's `𝗭𝗙𝗖` | **proved** (`Translation.zfc_proves_conZFCSet`) |
| The reduction of the target to eight internal implications | **proved** (`Endpoint`, and it is an *iff*) |
| Those eight implications at **standard** indices | **proved** (`StandardSuccessor`) |
| Those eight implications at **nonstandard** indices | **open** |
| `Peano ⊢ paUniformZFCProvabilitySentence` | **conditional** |

The endpoint is

```lean
theorem peano_proves_uniformZFCProvability_of_successorImplications
    (H : ZFCSuccessorImplicationsInAllModels) :
    Peano ⊢ paUniformZFCProvabilitySentence
```

and its hypothesis is *exactly* the remaining obligation — the reduction is an
equivalence (`zfcStagedSuccessorInAllModels_iff_successorImplications`), so no
strength is hidden in the reduction and no easier hypothesis would do.

A conditional endpoint is only worth as much as its hypothesis is plausible,
and this project has already had one hypothesis turn out to be **false**: an
earlier *five*-field certificate was machine-checked non-transferable in
[`LocalStepDerivation.lean`](Lean/ZFCinPA/LocalStepDerivation.lean)
(`exclusivity_not_step_transferable`), by exhibiting two definable expansions
that satisfy the five fields and disagree on the successor. The certificate was
therefore enlarged with the two Tarski fields, and the enlargement was
*semantically pre-checked* before any proof was attempted — see
[`EnlargedFields.lean`](Lean/ZFCinPA/EnlargedFields.lean) and
[`TarskiFieldSemantics.lean`](Lean/ZFCinPA/TarskiFieldSemantics.lean). That
episode is the reason this README leads with the status table.

## Why the obvious routes do not work

Three natural approaches fail, and knowing why is most of the design:

- **External recursion.** `zfc_proves_conZFCSet` is indexed by a metatheoretic
  `ℕ`, so a Lean `∀ n` in front of it is a schema, not a sentence. Turning it
  into one sentence needs a proof *selector* that works at arbitrary model
  elements, not a recursion over external numerals.
- **A truth predicate.** Tarski forbids a single internal satisfaction
  predicate. Compliance here is structural: truth levels recurse **externally**
  (the level is a Lean `Nat`, never a de Bruijn slot nor a model element), so
  each level is a separate, strictly larger formula. Within a level, recursion
  over nonstandard codes must be an internal certificate.
- **A bare closure predicate for derivations.** Unsound: `{a, b, a ∧ b}` is
  closed under conjunction introduction and elimination yet derives nothing.
  Derivations must cite premises at strictly smaller internal **rank**, which
  reduces well-foundedness to membership on von Neumann naturals and so still
  works at nonstandard ranks.

## Architecture

The construction runs in five layers. Each is a directory-level concern rather
than a single module; the module catalogue below gives the details.

1. **Definability.** Foundation's arithmetized syntax is generic over a
   language with `Encodable` and `LORDefinable` instances and a `Δ₁` theory.
   Supplying those for `ℒₛₑₜ` and `𝗭𝗙𝗖` is what lets `𝗭𝗙𝗖`-provability be
   *spoken about* inside arithmetic at all.
   → `Instances`, `SchemaClosure`, `SeparationDelta1`, `ReplacementDelta1`,
   `ZFDelta1`.

2. **The statement.** Build the literal arithmetic sentence and reduce it to a
   model-internal proof selector.
   → `Translation`, `UniformStatement`, `PackageInduction`.

3. **The certificate.** An eight-field, level-indexed master certificate —
   seven variable truth-construction fields plus, forced into the last
   coordinate so that no easier conclusion can be certified, the corresponding
   bounded-consistency instance.
   → `LevelCodeTower`, `CertificateFamily`, `CertificateFields`,
   `ConcreteFamily`, `BaseCertificate`, `EnlargedFields`, `TarskiFieldSemantics`.

4. **The compiler.** Rather than derive each obligation by hand inside the
   internalized theory, fix a *source* sentence in a placeholder template
   language, prove it derivable once, and transport it by instantiating the
   placeholders with real coded formulas. The equality quotient and congruence
   discharge are what make the transport legitimate.
   → `SeparationKernel`, `UniversalKernel`, `SetPlaceholders`,
   `SetPlaceholderQuotient`, `SetCongruence`, `SubstIdentity`, `StagedCompiler`.

5. **The successor.** The remaining obligation, its source layer, and the
   *evaluation bridge* that certifies the source sentences say what they are
   meant to say.
   → `StagedSuccessor`, `StandardSuccessor`, `SuccessorSources`, `TarskiSources`,
   `LocalStepSuccessor`, `LocalStepDerivation`, `LocalStepTransfer`,
   `NumeralOmega`, `TemplateEvaluation`, `SpineEvaluation`, `TowerEvaluation`,
   `TowerSuccessorEvaluation`, `FieldEvaluation`, `Endpoint`.

### The evaluation bridge

Layer 5 deserves a note, because it is the part that is easy to get wrong
silently. `complete_underSetPlaceholderCongruence` reduces a source derivation
to a semantic obligation: the source sentence must hold in every *template
structure*. The bridge reads each source formula, inside an arbitrary such
structure, as the corresponding abstract predicate over an induced level
relation. Without it, a source sentence could be perfectly derivable and still
mean the wrong thing — the failure mode that the false five-field hypothesis
exemplified.

The bridge's correspondence structure `Corr` reads bound and free Foundation
slots into one repository environment uniformly, which is why the evaluation
lemmas need **no** arity side conditions even though the translation lemmas do.

## Module catalogue

Modules live in [`Lean/ZFCinPA/`](Lean/ZFCinPA/); every module `M` has a
companion `MAudit` carrying `#print axioms` for its public declarations. The
facade is [`Lean/ZFCinPA.lean`](Lean/ZFCinPA.lean).

| Module | Role |
| --- | --- |
| `Instances` | `ℒₛₑₜ` gets `Encodable` and `LORDefinable` |
| `SchemaClosure` | language-generic recognizer for universally closed schemata |
| `SeparationDelta1`, `ReplacementDelta1` | the two `𝗭𝗙` schemata are `Δ₁` |
| `ZFDelta1` | `𝗭𝗙` and `𝗭𝗙𝗖` are `Δ₁` theories |
| `Translation` | `Conₙ(ZFC)` is a theorem of Foundation's `𝗭𝗙𝗖` |
| `UniformStatement` | the literal sentence; reduction to the selector |
| `PackageInduction` | existential proof packages for the selector |
| `LevelCodeTower` | PR-blueprint code towers for the level-indexed truth formulas |
| `CertificateFamily` | shape of a level-indexed eight-field certificate |
| `CertificateFields` | the seven variable field codes and their `𝚺₁` graphs |
| `ConcreteFamily` | typed model-coded formulas for those codes |
| `BaseCertificate` | a genuine typed `𝗭𝗙𝗖` proof at level `0` |
| `EnlargedFields` | why five fields fail and seven succeed, checked semantically |
| `TarskiFieldSemantics` | the two Tarski bundles are true at every level |
| `SeparationKernel` | internalized Separation and ω-induction at a coded formula |
| `UniversalKernel` | universal proof kernels for the staged compiler |
| `SetPlaceholders` | placeholder relations and their model-coded translation |
| `SetPlaceholderQuotient` | equality completion for placeholder templates |
| `SetCongruence` | internal equality replacement |
| `SubstIdentity` | self-substitution of a coded leaf at deeper ambient arity |
| `StagedCompiler` | staged compilation; states `HasStagedSuccessor` |
| `StagedSuccessor` | the obligation as eight flat internal implications |
| `StandardSuccessor` | those eight, discharged at every **standard** index |
| `SuccessorSources` | the shared source layer of the field successors |
| `TarskiSources` | source readings of the two Tarski fields |
| `LocalStepSuccessor` | the level tower as a two-placeholder proof template |
| `LocalStepDerivation` | the negative result: five fields do not transfer |
| `LocalStepTransfer` | the local step *does* transfer under the enlarged certificate |
| `NumeralOmega` | the numeral chain lands in ω, internally and uniformly in `x : V` |
| `TemplateEvaluation` | bridge part 1: template structures and their leaves |
| `SpineEvaluation` | bridge part 2: the closure spine |
| `TowerEvaluation`, `TowerSuccessorEvaluation` | bridge part 2(b), 2(c): the level tower, and one index up |
| `FieldEvaluation` | bridge part 3: certificate fields; carries the residue list |
| `TarskiEvaluation` | bridge part 4: the two Tarski fields, at both levels |
| `CrossLevelSource` | the `decided` conjunct as a source field, and its reading |
| `NumeralUnique` | pins the numeral placeholder; uniqueness discharged internally |
| `CodeInductionSource` | code-induction at `StepGood` as a Separation antecedent |
| `Endpoint` | the target, the chain to it, and its exact residue |
| `SetRelativization` | represented relativization for `ℒₛₑₜ`: closed terms are variables, and the internal relative-interpretation theorem `provable_falsum_of_relativize_set` (generic core: `BoundedPAConsistency.InternalRelativization`) |
| `ConstructibleInterpretation` | the constructible interpretation of `𝗭𝗙𝗖` in `𝗭𝗙`, internalized: a model-independent `x ∈ L` formula, external relativization with its evaluation and quotation laws, `𝗭𝗙 ⊢ σ^L` for the equality, fixed and choice axioms, and `provable_falsum_ZF_of_ZFC` (`Prov_ZFC(⊥) → Prov_ZF(⊥)` in every model of `IΣ₁`, modulo the separation/replacement schema obligation `hSchema`) |
| `EnvTransform` | the `L`-relativized environment transform `envForm d K` for the `hSchema` reflection generator: every variable of an internal formula code read from one internal environment (`econs`/`applyV` slots via von Neumann numerals), one `UformulaRec1` construction with the binder depth as parameter (large fixed codes ride in the parameter, not as numerals), constructor equations, and `isSemiformula_envForm` (the output mentions only the environment) |
| `LTemplate` | the template theory of the `hSchema` generator: lifted `𝗭𝗙`, enlarged equality, and the full separation/replacement schemata over placeholder relations; `translated_axiom` discharges every source axiom internally (placeholder arities ≤ 3), `compileT` compiles a fixed source derivation at internal formula codes, and the semantic side (`pure_models`, `sep_iff`, `repl_iff`, `templ_provable`) |
| `LPieces` | the pure pieces of the reflection templates (ordinals, limits, `S = L_β`, membership relations, environments, finite support, formula codes, `SatIn`) with their evaluation in every model of ZF |
| `LTransVal` | `transVal`, the untyped mirror of `translateFormula`, and its `Σ₁` definability in the placeholder codes (so translated template codes can enter internal inductions) |
| `LInvariant` | the reflection invariant of the `hSchema` generator: `totS F` (a total function on ordinals above its argument) and `reflS P F` (one internal code reflects `P` as `SatIn` over every limit stage closed under `F`), read in every template model |
| `LStepAnd` | the conjunction step: `and_step` for arbitrary relations (closure under the maximum gives closure under both components; the and-code reflects the conjunction by `satIn_and`) and `andTemplate_provable`, a theorem of the template theory over six placeholders |
| `LStepBasic` | the disjunction step (`orTemplate`, by `satIn_or`), the negation step for negated atoms (`negTemplate`, code `c → ⊥`), and the constant bases `topBase`/`botBase` with the successor as reflection function |
| `LStepAtom` | the atomic steps: if the numeral placeholders each define one natural number, the membership (equality) atom read at those environment slots, built literally from `EnvTransform`'s pieces, is reflected by the code `⟨0, ⟨a, b⟩⟩` (`⟨1, ⟨a, b⟩⟩`) with the successor as reflection function (`atom_step`, `atomTemplate_provable`) |
| `LStepEx` | the mathematical core of the quantifier steps: the witness-bounding function (`Wit`, `WB`, `wb_exists`), earlier-stage bookkeeping at limits, and `ex_step`/`all_step` (codes `⟨7, c'⟩`, `⟨6, c'⟩` by `satIn_ex`/`satIn_all`) |
| `LStepExT` | the quantifier templates: witness formulas (`hasWitS`, `anyWitS`, `witS`, `wbS`, `rkS`), `wb_tot` (in every template model the witness-bounding formula is a total function bounding witnesses, from Replacement for `rkS` over a power set of environments and Separation for `witS`), and `exTemplate_provable`/`allTemplate_provable` |
| `LIterate` | ω-iteration of a class function on ordinals inside any ZF model: the successor-closure step `HStep`, finite chains (`Chain`, `chain_exists` by restricted ω-induction, `chain_agree`), and `orbit_closure` (the union of the orbit is a nonzero limit closed under the function), with every Separation/Replacement use an explicit hypothesis |
| `LClosure` | `LIterate` inside template models: L6 formulas for steps, chains, images and orbits with their readings, and `closure_point` (if `F₅` is total on ordinals, limits closed under `F₅` are unbounded), discharging the resources by `sep_iff`/`repl_iff` |
| `LFinalSep` | the final Separation template: `sep_final` (a reflected predicate cuts a definable subset of a closed stage `L_β`, hence a constructible set, by `inL_of_definable` and `inL_sep`) and `sepTemplate_provable`: `totS F₅ ⋏ reflS P₄ F₅ → ` `L`-separation for `P₄` at extended environments |

## Building

From the repository root. Set `LEAN_NUM_THREADS=0` first if your machine cannot
afford Lake's default worker pool: several modules here are large enough that
each concurrent `lean.exe` can consume gigabytes.

```powershell
$env:LEAN_NUM_THREADS = '0'
lake build ZFCinPA
```

**Gotcha worth knowing before you debug a phantom success.** The `ZFCinPA`
`lean_lib` in the root `lakefile.toml` declares no globs, so its only module
target is the root facade. A command like `lake build +ZFCinPA.NumeralOmega`
is a **silent no-op**: it exits `0` having built nothing. To check one module,
invoke the elaborator directly:

```powershell
lake env lean -o ".lake/build/lib/lean/ZFCinPA/NumeralOmega.olean" -i ".lake/build/lib/lean/ZFCinPA/NumeralOmega.ilean" "Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NumeralOmega.lean"
```

Clean elaboration prints nothing. Modules are otherwise reachable only through
the facade, so a new module must be added there to be built by `lake build`.

## Trust boundaries

There are none beyond Lean's kernel and mathlib. No `sorry`, no `admit`, no
project-specific axiom, no `native_decide`, no `unsafe`, no unproved
`implemented_by`. Every audit module reports

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

Two conventions guard against false confidence, both learned the hard way:

- Every statement-bearing module sets `set_option autoImplicit false`. An
  out-of-scope identifier once became an implicit variable, a headline statement
  silently elaborated to `Nat → sorry`, and `#print axioms` cheerfully reported
  no axiom dependence. The six definability-layer modules (`Instances`,
  `SchemaClosure`, `SeparationDelta1`, `ReplacementDelta1`, `ZFDelta1`,
  `Translation`) predate the convention and do not yet set it; they state
  instances and transport lemmas rather than headline results, but tightening
  them is outstanding.
- The endpoint's conditionality is stated in the module, in its audit, and in
  the status table above. A conditional theorem whose hypothesis is quietly
  false is worse than an admitted gap.

## Residue

The open work is enumerated precisely in the residue sections of
[`FieldEvaluation.lean`](Lean/ZFCinPA/FieldEvaluation.lean),
[`LocalStepTransfer.lean`](Lean/ZFCinPA/LocalStepTransfer.lean) and each new
module. The state as of the last commit:

**Done.** All four prerequisites of the `localStep` assembly now exist and
build: the two Tarski field readings (`TarskiEvaluation`), the `crossLevel`
source field (`CrossLevelSource`), the `Num`-uniqueness antecedent
(`NumeralUnique`), and the source code-induction antecedent
(`CodeInductionSource`).

**Open, in dependency order.**

1. *One vocabulary mismatch, mechanical but unwritten.*
   `NumeralOmega.zfcInternal_numChain_omega` lives over the one-placeholder
   `SeparationKernel.setTemplateLanguage`, while `srcNumUnique` lives over the
   two-placeholder `SuccessorSources.srcL`. Both specialize the numeral
   placeholder to the same `numChainCode x`, so restating ω-membership as an
   `srcL` source formula is a code-identity exercise — but it exists nowhere,
   and the assembler needs both antecedents in one sentence.
2. *The assembly.* Build
   `(srcNumOmega ⋏ srcNumUnique ⋏ srcCodeInduction ⋏ srcLaws) 🡒 srcLocalStepSucc`,
   transport it by `complete_underSetPlaceholderCongruence`, and discharge each
   antecedent after translation. This yields `localStep` at arbitrary `n : V` —
   **one** of the eight implications.
3. *Four fields with no source formula at all*: `shiftInvariant`,
   `substitutionInvariant`, `axiomSound`, and `finalConsistency` (with its
   `conFormula` well-formedness obligation). Each needs the same five
   deliverables — source formula, translation identity, `FvFree`, evaluation
   reading, derivation. The good news is that the closure spine they recurse
   through (`srcLevelSat`, `srcSigmaTrue`, `srcPiFalse`, `srcPiTrue` and their
   successor forms) is field-*independent* and already proved, so the marginal
   cost per field does not include the apparatus.

A reusable tool for step 3, found while writing `CodeInductionSource`:
`shift_translateFormula_of_fvFree` establishes shift-fixedness of the
translation of *any* free-variable-free source proposition in a few lines, from
`SetPlaceholders.translateFormula_shift` and `Semiformula.rew_eq_self_of`. It is
strictly more general than mirroring `LevelCodeTower.shift_closCode`'s
per-formula spine walk, and it reuses the `FvFree` fact needed anyway to close a
`Proposition srcL` into a `Sentence srcL`.

## Related projects

- [`SetTheory/BoundedConsistency`](../../../SetTheory/BoundedConsistency/README.md)
  — `ZFC ⊢ Conₙ(ZFC)`, proved; the set-theoretic half of this development.
- [`Logic/PeanoArithmetic/BoundedConsistency`](../../PeanoArithmetic/BoundedConsistency/README.md)
  — the arithmetic analogue `PA ⊢ ∀ n, Prov_PA(⌜Conₙ(PA)⌝)`, proved, and the
  template this project mirrors.

[Open template closure](open-template-closure.md) supplies
`OpenTemplateClosure.generalizeAll` and `closeTemplate`: ordinary finite source
parameters are universally closed while arbitrary extra free parameters of
internal predicate interpretations stay free. The proof callback at every
finite buffer remains explicit. The focused run6 check passed four probes and
four callers with zero warnings, reusing 16 matched project providers; all five
nonpasses and the maintained-default unbuilt preflight remain archived. This
module supplies no schema callback or arbitrary internal source-proof transport.

[Set congruence refresh](set_congruence_refresh.md) checks the unchanged equality-replacement and binary-congruence proofs for arbitrary internal predicates, including free parameters. Twelve axiom probes and fourteen callers passed with zero warnings. The original driver failure and the separately validated, read-only apostrophe-parser recovery are preserved; the maintained default preparation is explicitly unbuilt.


[Open schema template callbacks](open-schema-templates.md) now provide actual internal ZF proofs of translated Separation and globally total functional Replacement, with finite closure of the ordinary source parameters and arbitrary additional internal predicate parameters retained. The lifted ordinary ZF-axiom callback is also checked. Run3 passed 5 probes/5 callers with standard axioms and one retained source unused-simp warning; both failed attempts and the maintained-default UNBUILT preflight remain separate. This supplies actual schema callbacks, not arbitrary internal source-proof compilation or nonfunctional Collection.

[Internal two-slot reindexing](model_coded_bind_two_slots.md) proves the exact syntax law for two distinct chosen labels and arbitrary internal target indices, including coincident targets. It covers the three substitutions needed by Collection. The focused check passed 8 probes/12 callers with standard axioms and zero warnings; the failed first attempt and separate unbuilt preparations are preserved.

[Compiled internal Collection](compiled_collection254.md) now produces an actual internal ZF proof for every binary internal predicate, including arbitrary free parameters. The fixed ordinary derivation is translated with all three schema callbacks and expanded-language equality discharged. Run3 passed 5 probes/8 callers with standard axioms and zero warnings; two failed normalization attempts and the unbuilt default preparation remain archived. Exact decoded G identification and the represented proof-search endpoint remain separate.

[Exact G-circuit normalization](model_coded_decoder_collection_normalization254.md) identifies the actual numerical G circuit with its named quantifier formula, preserving every numeric label. Its equivalence and congruence check passed 3 probes/6 callers with standard axioms and zero warnings. The failed initial audit and separate unbuilt preparations are retained. This equivalence will connect the compiled Collection proof to the actual gated G row.

[The exact numerical G row](model_coded_decoder_collection254.md) now has an internal ZF proof under precisely the two validator gates, including coincident labels and the zero-code case. The check passed 10 probes/16 callers with standard Lean axioms; eleven source style warnings remain. All five attempts are archived. Full bundle assembly, accepted-proof induction and the PA consistency equivalence remain separate.

[The full numerical bundle](model_coded_decoder_bundle254.md) now has an internal ZF proof for every permitted input, including coincident labels and code zero. It combines the exact C/G rows and both atomic vacuity clauses under the original two gates. The first check passed 3 probes/8 callers with standard Lean axioms and zero warnings. Accepted-proof induction and the PA consistency comparison remain separate.

[All-internal accepted-proof soundness](model_coded_decoder_accepted254.md) now transports every accepted numerical conclusion to an actual internal ZF proof, by eligible Σ₁ induction over all proof codes. Accepted value 2 yields a ZF contradiction. The complete check passed 5 probes/10 callers with standard Lean axioms; fourteen source style warnings remain. The first failed numeral-normalization attempt is retained. The reverse proof translation remains open; the fixed forward PA sentence is proved below.

[The fixed forward consistency implications](validator_consistency_forward254.md) are now theorems of IΣ₁ and PA: Con(ZF) and Con(ZFC) each imply that no internal numerical proof code has validator value 2. The first check passed 8 probes/10 callers with standard Lean axioms and zero warnings. It uses the completed all-internal accepted-proof transport before arithmetic completeness. The converse and the actual binary-machine equivalence remain open.

[The internal validator proof calculus](validator_provability254.md) now supplies a fixed Σ₁ theorem predicate with all twelve original rule closures and a classical implication interface, for arbitrary internal formula and proof codes. The check passed 22 probes/16 callers with standard Lean axioms and zero warnings. It reuses the existing numerical proof constructors and polymorphic propositional certificates. The internal formula/proof encoder and reverse consistency implication remain open; variable renaming needs special care because the bundle parameter is both a formula code and a variable label.

- [Constructible interpretation: fixed L domain, finite axiom discharge, and conditional internal refutation transport](constructible_interpretation.md) — checked 25/18, standard axioms, zero warnings. Uniform internal Separation/Replacement `hSchema` remains open.

The represented formula encoder now passes its 18-probe/24-caller narrow
check: fixed Sigma1 syntax graphs and total Delta1 semantics for arbitrary
internal source/depth inputs, with the actual set-language symbol codes and
literal numeric constructor equations. The source has zero warnings; the
audit retains one unused-simp warning. This supplies the computation used by
a future ZF-to-validator proof compiler, not that compiler or a reverse
consistency implication. See `ValidatorFormulaEncoder254.lean`,
`validator_formula_encoder254.md`, and the matching verification/history/review
records. Its maintained-default prepare-only check builds nothing and makes
no compiler/version call.

The finite CProv quantifier interface passes all 25 probes and 18 callers
with standard axioms and zero warnings. It derives quantifier monotonicity,
original gated atomic vacuity and the explicit-resource `all_relational`
bridge at arbitrary internal formula/label values. All four vacuity proof
witnesses remain premises; no global renaming closure of accepted proofs or
bundles is assumed. The represented environment/alpha induction and actual
ZF axiom reconstruction remain open. See `ValidatorQuantifierCore254.lean`,
`validator_quantifier_core254.md`, and the matching records. The maintained
prepare-only check queries the compiler version and performs no proof build.

The [internal equality interface](validator_equality_core254.md) now checks reflexivity, symmetry, transitivity and both-coordinate atomic congruence for arbitrary internal labels. All nine probes and twelve callers passed with standard axioms and zero warnings; the environment induction and source-proof compiler remain open.

The [configurable environment encoder](validator_environment_labels254.md) now checks total internal free/bound environment graphs and exact term, vector and formula SHIFT laws, including nested quantifiers. All 39 probes and 28 callers passed with standard axioms and zero warnings. Alpha induction and the source-proof compiler remain open.

[Internal binder opening](validator_environment_opening254.md) now proves the
exact term, vector and formula substitution identities for arbitrary internal
depths and environments, with explicit stack-extension premises. Its finite
clients identify the opened matrices of ALL and EXS. The check passed 19 probes
and 22 callers with standard axioms and zero warnings. Alpha equivalence and
the source-proof compiler remain open; this computation does not rename
accepted proofs.

[Encoded-formula vacuity](validator_environment_vacuity254.md) now constructs
literal-validator vacuity witnesses for every internal source formula under
explicit free-label, bound-label and future-binder-stream avoidance. Its
universal environment invariant uses Π2 induction in IΣ2. The check passed
10 probes and 16 callers with standard axioms, retaining two unused-section
warnings. This supplies body-vacuity resources for the later alpha proof;
alpha equivalence and source-proof translation remain open.

[Internal equality contexts](validator_equality_context254.md) now represent
pointwise stack equalities by a fixed total internal conjunction. All coordinate
projections, both cons implications and the body-assumption discharge needed by
the quantifier bridge are checked using IΣ1 induction and finite classical
proofs. The check passed 21 probes and 24 callers with standard axioms and zero
warnings. Stack lengths and all four quantifier vacuity witnesses remain
explicit obligations for the later alpha proof; source-proof translation and
the reverse consistency implication remain open.

[Equality-context vacuity](validator_equality_context_vacuity254.md) now derives
the two context-vacuity resources for the relational quantifier rule from
explicit avoidance of both equal-length bound stacks. The represented-prefix
proof uses Σ1 induction in IΣ1 and passed three probes and seven callers with
standard axioms and zero warnings. Both cross-body vacuity resources remain
explicit; the formula alpha induction and source-proof compiler remain open.

[Internal alpha transport](validator_environment_alpha254.md) now constructs
both implication proofs between configurable encodings of every internal source
formula, under the same represented bound-stack equality context. It uses Π2
induction in IΣ2 and explicit disjoint future streams avoiding the free labels,
fallback1 and both old stacks. The first check passed 18 probes and 22 callers
with standard axioms; three source linter warnings remain. Concrete stream
selection, source-proof compilation and the reverse consistency endpoint
remain open; that compiler can use the configurable encoder directly.
