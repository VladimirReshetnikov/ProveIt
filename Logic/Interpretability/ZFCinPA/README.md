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
