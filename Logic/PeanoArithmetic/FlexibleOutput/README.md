# A divergent program with every possible output in a model of PA

**Status: proved in Lean.** The main theorem is
`PAFlexibleOutput.flexibleOutput` in
[`Lean/PAFlexibleOutput/Main.lean`](Lean/PAFlexibleOutput/Main.lean). Its
axioms are `propext`, `Classical.choice` and `Quot.sound`. The proof is five
modules, 376 lines in all.

## The theorem

There is a partial recursive function `f : ℕ ⇀ ℕ` such that for every `o`,
which is either a natural number `n` or `⊥`, the statement `f(0) = o` holds in
some model of first-order Peano arithmetic. The Lean theorem proves this for
every input, not only for `0`, and for a function that diverges everywhere:

```lean
theorem flexibleOutput :
    ∃ e : Code, (∀ x, Nat.Partrec.Code.eval e x = Part.none) ∧ ∀ (x : ℕ) (o : Option ℕ),
      ∃ (M : Type) (_ : ORingStructure M) (_ : M↓[ℒₒᵣ] ⊧* 𝗣𝗔), ValueIn M e x o
```

The function is given by a program code `e`, and a model reads `f(x) = o`
through one fixed arithmetical formula `universalGraph(y, program, input)`,
"the program halts on the input with output `y`":

- `ValueIn M e x (some n)` says that the numeral `n` is the unique element `y`
  of `M` with `M ⊨ universalGraph(y, ⌜e⌝, x)`;
- `ValueIn M e x none` says that no element of `M` is such an output.

The same code and the same formula serve every `x` and every `o`. Three facts
make the formula a definition of `f` and not an arbitrary formula:

- `standardCorrectness`: in the standard model, `universalGraph(y, ⌜c⌝, x)`
  holds iff `y ∈ Nat.Partrec.Code.eval c x`;
- `universalGraph_uniq`: in every model of `𝗣𝗔⁻` the formula has at most one
  output for a given program and input, nonstandard programs and inputs
  included;
- `universalGraph_sigma_one`: the formula is `𝚺₁`.

Since `f` diverges on every standard input, `ℕ` is a model for `o = ⊥`, and by
`standardCorrectness` it is a model for no `o = n`: the models for the
numerical outputs are nonstandard.

Two corollaries in `Main.lean`:

| Theorem | Statement |
| --- | --- |
| `exists_partrec_flexibleOutput` | the statement as worded above: a partial recursive `f : ℕ →. ℕ` with a program `e`, and for every `o` a model of PA with `ValueIn M e 0 o` |
| `flexibleOutput_satisfiable` | sentence form: `e` diverges, and `Satisfiable (insert (haltSentence e x n) 𝗣𝗔)` for all `x` and `n` |

## Proof

The outputs refuted by PA form a recursively enumerable relation: "PA proves
that program `c` does not halt on input `x` with output `y`"
(`refutationsRE`). So a partial recursive `Search(c, x)` returns some refuted
output of `c` on `x` whenever there is one (`exists_selector`). Kleene's
second recursion theorem (`Nat.Partrec.Code.fixed_point₂`) gives a program `e`
with `φ_e(x) = Search(e, x)`.

1. `e` diverges. An output `m` of `e` on `x` would be an output of the search,
   so PA would prove that `e` does not halt on `x` with output `m`. But `e`
   does halt with that output, so the halting sentence is true in `ℕ`
   (`standardCorrectness`), and `ℕ` is a model of PA.
2. PA refutes no output of `e`: a refuted output would make the search, and
   with it `e`, halt.
3. By the completeness theorem every halting sentence `H_e(x, n)` holds in
   some model of PA, and in that model `n` is the only output
   (`valueIn_of_models`, from `universalGraph_uniq`).
4. `ℕ` is a model in which `e` has no output.

Step 1 uses that `ℕ` is a model of PA. The paper proof in the article uses
less, the consistency of PA alone: there PA verifies the finite computation
(`𝚺₁`-completeness) and so proves both `H_e(x, m)` and its negation. The Lean
proof takes the semantic route because it is shorter and Foundation provides
`ℕ ⊧* 𝗣𝗔`; the first Lean proof (commit `410c820c4f`) followed the paper.

This is the self-reference proof (due to Vadim Kosoy) in Joel David Hamkins,
"Every function can be computable!", for one input at a time (the models for
different inputs may differ), and a consequence of Woodin's universal
algorithm; the article gives the references.

## Layout

| Path | Contents |
| --- | --- |
| [`Lean/PAFlexibleOutput/Halting.lean`](Lean/PAFlexibleOutput/Halting.lean) | `universalGraph`, Foundation's representing formula of the universal function of Mathlib's `Nat.Partrec.Code`; `haltSentence`, `OutputIn`, `ValueIn`; `standardCorrectness`, `outputIn_nat`, `universalGraph_sigma_one`. |
| [`Lean/PAFlexibleOutput/Functionality.lean`](Lean/PAFlexibleOutput/Functionality.lean) | `code_uniq`: Foundation's representing formula of a partial recursive function has at most one output in every model of `𝗣𝗔⁻`, by induction on the code. `universalGraph_uniq`, `valueIn_of_models`. |
| [`Lean/PAFlexibleOutput/Refutations.lean`](Lean/PAFlexibleOutput/Refutations.lean) | `refutationsRE`: "PA refutes output `y` of program `c` on input `x`" is recursively enumerable, through the `𝚺₁`-definability of Foundation's arithmetized provability and numeral substitution. |
| [`Lean/PAFlexibleOutput/Search.lean`](Lean/PAFlexibleOutput/Search.lean) | `exists_selector`: a recursively enumerable relation has a partial recursive selector, by dovetailing. Mathlib only. |
| [`Lean/PAFlexibleOutput/Main.lean`](Lean/PAFlexibleOutput/Main.lean) | `flexibleOutput` and the two corollaries. |
| [`Lean/PAFlexibleOutput.lean`](Lean/PAFlexibleOutput.lean) | Import surface. |
| [`Article/pa_flexible_output.tex`](Article/pa_flexible_output.tex), [`.pdf`](Article/pa_flexible_output.pdf) | The delivered draft: statement, mathematical proof, the Lean statement, the located repository and dependency results, and a five-stage route to a Lean proof. It predates the Lean proof and describes it as future work. |
| [`Research/delivery/`](Research/delivery/) | The rest of the delivered package, unchanged: `README.txt`, `verification_status.txt`, `dependencies.json` (pinned revisions and inspected sources), `notes/`, `scripts/`, `lean-toolchain`, and the three delivered Lean files in `lean/`. |

Notes on the Lean proof:

- Foundation's own `code_uniq` is commented out at the pinned revision, so the
  induction on the code in `Functionality` is new. The only case with content
  is minimisation, which needs the order of the model to be linear; this is
  why the statement is about `𝗣𝗔⁻` and not `𝗥₀`.
- In `Refutations` the relation is `𝚺₁`-definable in `ℕ` because
  `Bootstrapping.Provable 𝗣𝗔`, formal negation and formal numeral substitution
  are; Foundation's `sigma1_re` turns that into `REPred`. The code inside is
  the Gödel number of `∼(haltSentence c x y)` (`neg_subst_quote`), and
  arithmetized provability of a Gödel number in `ℕ` is real provability
  (`provable_iff_provable`).

## The delivered scaffold

The package delivered three Lean files, now in
[`Research/delivery/lean/`](Research/delivery/lean/) with their delivered
bytes: `Statement.lean` (the concrete target and five named obligations, as
definitions of propositions), `ProofCore.lean` (the logical core over an
abstract interface) and `MathlibAssembly.lean` (the recursion-theorem argument
over an abstract arithmetic bridge and proof search). Their author had no Lean
executable and delivered them uncompiled, which their comments still say.

The first Lean proof, commit `410c820c4f`, compiled the three files unmodified
as modules of the library, discharged every obligation of `Statement.lean`
and proved its `MainClaim`, `StrongClaim` and `FullySpecifiedMainClaim` by
instantiating `MathlibAssembly`: eight modules, 1003 lines. The current proof
replaces that route by the direct argument above and does not import the
delivered files, so they are no longer part of the library or of any build.
They import only Mathlib and Foundation, and the delivered
`scripts/check_lean.sh` checks them from the `lean/` directory.

What the current proof does differently:

- the search takes the input as a parameter, so the theorem holds at every
  input and the clause "the search ignores its input" is gone;
- divergence comes from truth in `ℕ` and not from `𝚺₁`-completeness;
- the abstract bridge, the search-implementation structure and the sentence
  for divergence are gone: `ValueIn` states both cases directly.

## Verification

Every module was elaborated in the root workspace (Lean `4.32.0`, mathlib
`v4.32.0`, the pinned Foundation submodule), one target per `lake` call, with
no errors and no warnings in the project's modules. Each of the seven
`#print axioms` lines reports `propext`, `Classical.choice`, `Quot.sound`.
There is no `sorry`, no added axiom and no `native_decide`.

The mathematical proof in the article has not been independently reviewed in
this repository.

## Building

The modules belong to the root workspace library `PAFlexibleOutput`. Build one
target at a time:

```powershell
$env:LAKE_JOBS = '1'; $env:LEAN_NUM_THREADS = '0'
lake build +PAFlexibleOutput.Main
```

Like `PAUndecidable`, the library imports Foundation and is therefore not part
of the `ProveIt.lean` facade.

## Provenance

Delivered as `docs/incoming/pa_flexible_output.zip` (arrival commit
`cb5ce85523`, 364,120 bytes) and placed on 2026-11-09. All thirteen entries of
the package's `SHA256SUMS` manifest matched the placed files; the manifest
itself is not filed, since the repository keeps no package-local checksum
ledgers, and remains in the archive at the arrival commit. The package's
`pa_flexible_output.{tex,pdf}` is under `Article/` and everything else is
under `Research/delivery/`. The modules under `Lean/` were written in this
repository on 2026-11-09.
