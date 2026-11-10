# A divergent program with every possible output in a model of PA

**Status: proved in Lean.** The main theorem is
`PAFlexibleOutput.exists_partrec_flexibleOutput` in
[`Lean/PAFlexibleOutput/Main.lean`](Lean/PAFlexibleOutput/Main.lean). Its
axioms are `propext`, `Classical.choice` and `Quot.sound`.

## The theorem

There is a partial recursive function `f : ℕ ⇀ ℕ` such that for every `o`,
which is either a natural number `n` or `⊥`, the statement `f(0) = o` holds in
some model of first-order Peano arithmetic.

```lean
theorem exists_partrec_flexibleOutput :
    ∃ f : ℕ →. ℕ, Partrec f ∧ ∃ e : Code, Nat.Partrec.Code.eval e = f ∧
      ∀ o : Option ℕ, ∃ (M : Type) (_ : ORingStructure M) (_ : M↓[ℒₒᵣ] ⊧* 𝗣𝗔),
        ValueIn M e o
```

The function is given by a program code `e`, and a model reads `f(0) = o`
through one fixed arithmetical formula `universalGraph(y, program, input)`,
"the program halts on the input with output `y`":

- `ValueIn M e (some n)` says that the numeral `n` is the unique element `y`
  of `M` with `M ⊨ universalGraph(y, ⌜e⌝, 0)`;
- `ValueIn M e none` says that no element of `M` is such an output.

The same code and the same formula serve every `o`. Three facts make the
formula a definition of `f` and not an arbitrary formula:

- `standardCorrectness`: in the standard model, `universalGraph(y, ⌜c⌝, x)`
  holds iff `y ∈ Nat.Partrec.Code.eval c x`;
- `functionalityInPAModels`: in every model of PA the formula has at most one
  output for a given program and input, nonstandard programs and inputs
  included (this holds already in models of `𝗣𝗔⁻`);
- `universalGraphSigmaOne`: the formula is `𝚺₁`.

The function `f` diverges on every standard input
(`flexibleOutput`, `strongClaim`). So `ℕ` is a model for `o = ⊥`, and by
`standardCorrectness` it is a model for no `o = n`: the models for the
numerical outputs are nonstandard.

Other forms of the statement in `Main.lean`:

| Theorem | Statement |
| --- | --- |
| `flexibleOutput` | sentence form: for every `o` a model of PA satisfies `outputSentence e o`, which is `haltSentence e 0 n` or `divergeSentence e 0` |
| `flexibleOutputValue` | the semantic form above, together with divergence on every input |
| `strongClaim`, `mainClaim`, `fullySpecifiedMainClaim` | the three propositions named in `Statement.lean`, with `Satisfiable (insert (haltSentence e 0 n) 𝗣𝗔)` |

## Proof

The program is a self-referential proof search. `Search(a)` enumerates PA
proofs and halts with output `k` on the first proof of `¬H_a(0, k)`, where
`H_a(x, y)` is `haltSentence a x y`. Kleene's second recursion theorem gives
`e` with `φ_e(x) = Search(e)`. If PA refuted some output, the search would
really halt with some output `k` (possibly a different one), PA would verify
that finite computation, and PA would prove both `H_e(0, k)` and its negation.
So PA refutes no output, the program never halts, and completeness gives a
model of `PA + H_e(0, n)` for each `n`. Only the consistency of PA is used.

This is the single-input case of the self-reference proof (due to Vadim
Kosoy) in Joel David Hamkins, "Every function can be computable!", and a
consequence of Woodin's universal algorithm; the article gives the references.

## Layout

| Path | Contents |
| --- | --- |
| [`Lean/PAFlexibleOutput/Statement.lean`](Lean/PAFlexibleOutput/Statement.lean) | The concrete target in Foundation's first-order arithmetic and Mathlib's `Nat.Partrec.Code`: `universalGraph`, `haltSentence`, `MainClaim`, `StrongClaim`, `FullySpecifiedMainClaim`, and the named obligations. Definitions of propositions only. Delivered. |
| [`Lean/PAFlexibleOutput/ProofCore.lean`](Lean/PAFlexibleOutput/ProofCore.lean) | The logical core over an abstract `ArithmeticInterface`, given a self-search fixed point. Imports `Std` only. Delivered; not used by the final proof. |
| [`Lean/PAFlexibleOutput/MathlibAssembly.lean`](Lean/PAFlexibleOutput/MathlibAssembly.lean) | The recursion-theorem argument with the fixed point from `Nat.Partrec.Code.fixed_point₂`: `exists_program_with_arbitrary_possible_output`, for an abstract `ArithmeticBridge` and `SearchImplementation`. Delivered. |
| [`Lean/PAFlexibleOutput/Arithmetization.lean`](Lean/PAFlexibleOutput/Arithmetization.lean) | `universalEvalPartrec`, `universalGraphSigmaOne`, `standardCorrectness`, `finiteProofAdequacy` (`𝚺₁`-completeness); `divergeSentence` and its semantics, `standardDivergence`. |
| [`Lean/PAFlexibleOutput/Functionality.lean`](Lean/PAFlexibleOutput/Functionality.lean) | `code_uniq`: Foundation's representing formula of a partial recursive function has at most one output in every model of `𝗣𝗔⁻`, by induction on the code. `universalGraph_uniq`, `functionalityInPAModels`. |
| [`Lean/PAFlexibleOutput/Refutations.lean`](Lean/PAFlexibleOutput/Refutations.lean) | `refutationsRE`: "PA refutes output `y` of program `c`" is recursively enumerable, through the `𝚺₁`-definability of Foundation's arithmetized provability and numeral substitution. |
| [`Lean/PAFlexibleOutput/Search.lean`](Lean/PAFlexibleOutput/Search.lean) | `exists_search`: a dovetailing partial recursive search through a recursively enumerable relation. Mathlib only. |
| [`Lean/PAFlexibleOutput/Main.lean`](Lean/PAFlexibleOutput/Main.lean) | `paBridge` (PA as an `ArithmeticBridge`), `exists_searchImplementation`, and the theorems of the table above. |
| [`Lean/PAFlexibleOutput.lean`](Lean/PAFlexibleOutput.lean) | Import surface. |
| [`Article/pa_flexible_output.tex`](Article/pa_flexible_output.tex), [`.pdf`](Article/pa_flexible_output.pdf) | The delivered draft: statement, mathematical proof, the Lean statement, the located repository and dependency results, and a five-stage route to a Lean proof. It predates the Lean proof and describes it as future work. |
| [`Research/delivery/`](Research/delivery/) | The rest of the delivered package, unchanged: `README.txt`, `verification_status.txt`, `dependencies.json` (pinned revisions and inspected sources), `notes/mathematical_audit.txt`, `notes/api_audit.txt`, `scripts/`, `lean-toolchain`. |

## How the obligations were discharged

The delivery's `verification_status.txt` listed five obligations; the names
are those of `Statement.lean`.

1. `UniversalEvalPartrec`, `UniversalGraphSigmaOne`, `StandardCorrectness`:
   `Arithmetization`. Partial recursiveness comes from
   `Nat.Partrec.Code.eval_part`, and the standard semantics from Foundation's
   `codeOfPartrec'_spec`.
2. `FunctionalityInPAModels`: `Functionality`. Foundation's own `code_uniq` is
   commented out at the pinned revision, so the induction on the code is new.
   The only case with content is minimisation, which needs the order of the
   model to be linear; this is why the statement is about `𝗣𝗔⁻` and not `𝗥₀`.
3. `RefutationsRE` and the proof search: `Refutations` and `Search`. The
   relation is `𝚺₁`-definable in `ℕ` because `Bootstrapping.Provable 𝗣𝗔`,
   formal negation and formal numeral substitution are; Foundation's
   `sigma1_re` turns that into `REPred`. The code inside is the Gödel number
   of `∼(haltSentence c 0 y)` (`neg_subst_quote`), and arithmetized
   provability of a Gödel number in `ℕ` is real provability
   (`provable_iff_provable`).
4. `FiniteProofAdequacy`, consistency and model existence: `finiteProofAdequacy`
   is `sigma_one_completeness`; in `paBridge` consistency is soundness in `ℕ`
   and `modelOfUnrefuted` is `Arithmetic.complete`.
5. `Main` instantiates `MathlibAssembly` and derives the endpoints. The `⊥`
   case is not part of the delivered statement: it is `divergeSentence e 0`,
   which holds in `ℕ` by `standardDivergence`.

## Verification

Every module was elaborated in the root workspace (Lean `4.32.0`, mathlib
`v4.32.0`, the pinned Foundation submodule), one target per `lake` call, with
no errors. Every `#print axioms` line of the project reports `propext`,
`Classical.choice`, `Quot.sound` or a subset; `ProofCore` reports none. There
is no `sorry`, no added axiom and no `native_decide`.

The three delivered modules are the delivered bytes. Their author had no Lean
executable and delivered them uncompiled, which their module comments still
say; they compiled unmodified. The only diagnostics in the project's own
modules are two `checkUnivs` linter warnings on the delivered interface
structures.

The mathematical proof in the article has not been independently reviewed in
this repository; the Lean proof follows its argument.

## Building

The modules belong to the root workspace library `PAFlexibleOutput`. Build one
target at a time:

```powershell
$env:LAKE_JOBS = '1'; $env:LEAN_NUM_THREADS = '0'
lake build +PAFlexibleOutput.Main
```

Like `PAUndecidable`, the library imports Foundation and is therefore not part
of the `ProveIt.lean` facade. The delivered `scripts/check_lean.sh` expects
the package's original `lean/` directory and is kept for provenance only.

## Provenance

Delivered as `docs/incoming/pa_flexible_output.zip` (arrival commit
`cb5ce85523`, 364,120 bytes) and placed on 2026-11-09. All thirteen entries of
the package's `SHA256SUMS` manifest matched the placed files; the manifest
itself is not filed, since the repository keeps no package-local checksum
ledgers, and remains in the archive at the arrival commit. The package's
`lean/*.lean` is now `Lean/PAFlexibleOutput/*.lean`, its
`pa_flexible_output.{tex,pdf}` is under `Article/`, and everything else is
under `Research/delivery/`. `Arithmetization`, `Functionality`, `Refutations`,
`Search` and `Main` were written in this repository on 2026-11-09.
